/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.Execution
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Bodies
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Statements
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.ExecutionLowering
import all StrataBoole.Boole.Interpretation.Legacy.Interp
import all StrataBoole.Boole.Interpretation.Source
import all StrataBoole.Boole.Interpretation.Legacy.Semantics
import all StrataBoole.Verify
import all Strata.Languages.Core.Statement
import Strata.DL.Imperative.StmtSemanticsProps

public section

namespace Strata.Boole

open StrataDDM

private theorem coreExit_trace (procedures : String → Option Core.Procedure)
    (state : State) (label : String) (md : Imperative.MetaData Core.Expression)
    {trace : Imperative.Trace Core.Expression} {reached : Core.CoreConfig}
    (run : Core.CoreStepStarE procedures (.stmt (.exit label md) (coreEnv state)) trace reached) :
    trace = [] ∧ (reached = .stmt (.exit label md) (coreEnv state) ∨
      reached = .exiting label (coreEnv state)) := by
  cases run with
  | refl => exact ⟨rfl, .inl rfl⟩
  | step _ _ _ _ _ first rest =>
    cases first with
    | step_exit =>
      obtain ⟨same, rfl⟩ := Imperative.stepStmtStarE_from_exiting rest
      exact ⟨rfl, .inr same⟩

/-- A single exit agrees in both directions, carrying the same label and
unchanged state. It produces no assertion events or normal returns. -/
theorem exit_executionAgreement (procedures : String → Option Core.Procedure)
    (label : String) (md : Imperative.MetaData Core.Expression)
    (entryValid returnValid : State → Prop) :
    ExecutionAgreement procedures [.exit label md] (Computation.exit label) entryValid returnValid := by
  constructor
  · intro initial _ outcome ran
    change outcome = .exited label initial at ran
    subst outcome
    apply forward_singleton
    exact ⟨[], .step _ [] _ [] _ .step_exit (.refl _), by simp [coreChecksPass]⟩
  · intro initial final _ ran
    change Outcome.returned () final = .exited label initial at ran
    contradiction
  · constructor
    · intro initial final trace _ ran _
      rcases (coreExit_trace procedures initial label md (coreSingleton_terminal_inside ran)).2 with h | h <;>
        contradiction
    · intro initial target final trace _ ran _
      rcases (coreExit_trace procedures initial label md (coreSingleton_exit_inside ran)).2 with h | h
      · contradiction
      · cases h
        exact ⟨initial, rfl, rfl⟩
    · intro initial prior check reached _ ran _ _
      obtain ⟨_, inner⟩ := coreSingleton_trace_inside ran
      have impossible := (coreExit_trace procedures initial label md inner).1
      simp at impossible

/-- The exit case of the per-statement execution premise, for the actual
source interpretation and lowering, and any corresponding typed Core chunk. -/
theorem interpExit_execution (program : Core.Program) (labels : List String)
    (valid : Scope → TranslateState → Core.Expression.TyContext → Core.TypeSpec.TypeScopes → State → Prop)
    (range : SourceRange) (metadata : Ann (Option (BooleDDM.MetadataAnn SourceRange)) SourceRange)
    (name : Ann String SourceRange)
    {entry final : Scope} {before after : TranslateState}
    {context next : Core.Expression.TyContext} {scopes nextScopes : Core.TypeSpec.TypeScopes}
    {body : Computation Unit} {raw annotated : List Core.Statement}
    (interpreted : interpStmt denotation (.exit_statement range metadata name) entry =
      .ok (body, final))
    (lowered : lowerStatementChunk (.exit_statement range metadata name) before = .ok (raw, after))
    (erased : eraseStatementsAnnotations annotated = eraseStatementsAnnotations raw)
    (_typed : Core.TypeSpec.StatementsWellTyped program context scopes labels annotated next nextScopes) :
    ExecutionAgreement program.findProcByString? annotated body
      (valid entry before context scopes) (valid final after next nextScopes) := by
  rw [interpStmt] at interpreted
  simp only [bind, StateT.bind, Except.bind, pure, Except.pure,
    get, getThe, MonadStateOf.get, StateT.get, reject, throw, throwThe,
    MonadExceptOf.throw] at interpreted
  split at interpreted
  · contradiction
  · have bodyEq := congrArg Prod.fst (Except.ok.inj interpreted)
    change Computation.exit name.val = body at bodyEq
    subst body
    simp only [lowerStatementChunk] at lowered
    rw [toCoreStmt] at lowered
    simp only [toCoreMetaData, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
      get, getThe, MonadStateOf.get, StateT.get] at lowered
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj lowered)
    rcases annotated with _ | ⟨statement, rest⟩
    · simp [eraseStatementsAnnotations] at erased
    have restNil : rest = [] := by
      have h := (List.cons.inj erased).2
      cases rest <;> simp_all [eraseStatementsAnnotations]
    subst rest
    have same := (List.cons.inj erased).1
    cases statement <;> simp [eraseStatementAnnotations] at same
    case exit label md =>
      obtain ⟨rfl, _⟩ := same
      exact exit_executionAgreement _ _ _ _ _

end Strata.Boole
