/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.Bodies
public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.DeclarativeBodies
public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.ExecutionLowering
public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.ExecutionScopes
import all Strata.Languages.Core.Statement
import all Strata.Languages.Core.Typing.Spec.TypingSpec
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Statements
import all StrataBoole.Boole.Interpretation.Legacy.Semantics
import all StrataBoole.Boole.Interpretation.Legacy.Interp
import all StrataBoole.Boole.Interpretation.Source
import Strata.Util.RelationsProps
import Strata.DL.Imperative.StmtSemanticsProps

public section

namespace Strata.Boole

/-- Two-way execution agreement for a statement list, with an invariant at
each end. Normal returns must establish the invariant for the next statement. -/
structure ExecutionAgreement (procedures : String → Option Core.Procedure)
    (statements : List Core.Statement) (body : Computation Unit)
    (entryValid returnValid : State → Prop) : Prop where
  forward : ∀ initial, entryValid initial → ∀ outcome, body.run initial outcome →
    CoreForwardOutcome procedures (.stmts statements (coreEnv initial)) outcome
  return_valid : ∀ initial final, entryValid initial → body.run initial (.returned () final) →
    returnValid final
  replay : CoreReplay procedures (fun initial => .stmts statements (coreEnv initial))
    body entryValid returnValid

/-- Both executions of an empty list return the unchanged state. -/
theorem executionAgreement_nil (procedures : String → Option Core.Procedure)
    (valid : State → Prop) :
    ExecutionAgreement procedures [] (Computation.pure ()) valid valid := by
  refine ⟨?_, ?_, nil_replays procedures valid⟩
  · intro initial _ outcome ran
    obtain rfl := (Computation.run_pure _ _ _).mp ran
    exact forward_admin .step_stmts_nil ⟨[], .refl _, by simp [coreChecksPass]⟩
  · intro initial final ready ran
    have same := Outcome.returned.inj ((Computation.run_pure _ _ _).mp ran)
    exact same.2.symm ▸ ready

/-- Compose forward runs of adjacent chunks, using the first computation's
normal return invariant when entering the second computation. -/
private theorem executionForward_append {procedures : String → Option Core.Procedure}
    {head tail : List Core.Statement} {first rest : Computation Unit}
    {entryValid middleValid returnValid : State → Prop}
    (headAgrees : ExecutionAgreement procedures head first entryValid middleValid)
    (tailAgrees : ExecutionAgreement procedures tail rest middleValid returnValid)
    {entry : State} (ready : entryValid entry) {outcome : Outcome Unit}
    (ran : (first >>= fun _ => rest).run entry outcome) :
    CoreForwardOutcome procedures (.stmts (head ++ tail) (coreEnv entry)) outcome := by
  rcases (Computation.run_bind _ _ _ _).mp ran with
    ⟨⟨⟩, middle, firstRun, restRun⟩ | ⟨label, final, firstRun, rfl⟩ |
    ⟨label, final, firstRun, rfl⟩ | ⟨_, _, _, rfl⟩
  · obtain ⟨trace, witness, passing⟩ := headAgrees.forward _ ready _ firstRun
    obtain ⟨next, extended, returns, _⟩ := coreStmts_append_prefix _ _ witness
    rw [returns _ rfl] at extended
    exact forward_prepend extended passing
      (tailAgrees.forward _ (headAgrees.return_valid _ _ ready firstRun) _ restRun)
  · obtain ⟨trace, witness, passing⟩ := headAgrees.forward _ ready _ firstRun
    obtain ⟨next, extended, _, exits⟩ := coreStmts_append_prefix _ _ witness
    rw [exits _ _ rfl] at extended
    exact ⟨trace, extended, passing⟩
  · obtain ⟨prior, check, reached, witness, passing, failed⟩ := headAgrees.forward _ ready _ firstRun
    obtain ⟨next, extended, _, _⟩ := coreStmts_append_prefix _ _ witness
    exact ⟨prior, check, next, extended, passing, failed⟩
  · exact True.intro

private theorem executionReturn_append
    {first rest : Computation Unit}
    {entryValid middleValid returnValid : State → Prop}
    (firstValid : ∀ initial final, entryValid initial → first.run initial (.returned () final) →
      middleValid final)
    (restValid : ∀ initial final, middleValid initial → rest.run initial (.returned () final) →
      returnValid final)
    {entry final : State} (ready : entryValid entry)
    (ran : (first >>= fun _ => rest).run entry (.returned () final)) : returnValid final := by
  rcases (Computation.run_bind _ _ _ _).mp ran with
    ⟨⟨⟩, middle, headRun, tailRun⟩ | ⟨_, _, _, impossible⟩ |
    ⟨_, _, _, impossible⟩ | ⟨_, _, _, impossible⟩
  · exact restValid _ _ (firstValid _ _ ready headRun) tailRun
  all_goals contradiction

private theorem append_run_split {procedures : String → Option Core.Procedure}
    (head tail : List Core.Statement) (entry : Imperative.Env Core.Expression)
    {trace : Imperative.Trace Core.Expression} {reached : Core.CoreConfig}
    (ran : Core.CoreStepStarE procedures (.stmts (head ++ tail) entry) trace reached) :
    (∃ next, Core.CoreStepStarE procedures (.stmts head entry) trace next ∧
      (∀ final, reached = .terminal final → False) ∧
      (∀ label final, reached = .exiting label final →
        Core.CoreStepStarE procedures (.stmts head entry) trace (.exiting label final))) ∨
    (∃ middle first rest, trace = first ++ rest ∧
      Core.CoreStepStarE procedures (.stmts head entry) first (.terminal middle) ∧
      Core.CoreStepStarE procedures (.stmts tail middle) rest reached) := by
  induction head generalizing entry trace reached with
  | nil =>
    exact .inr ⟨entry, [], trace, rfl,
      .step _ [] _ [] _ .step_stmts_nil (.refl _), ran⟩
  | cons statement head ih =>
    rcases Imperative.stmts_cons_headE _ ran with ⟨rfl, rfl⟩ | stepped
    · exact .inl ⟨_, .refl _, by simp, by simp⟩
    rcases Imperative.seq_run_decomposeE _ stepped with
      ⟨inner, rfl, first⟩ | ⟨middle, firstTrace, restTrace, rfl, first, rest⟩ |
      ⟨label, final, rfl, first⟩
    · exact .inl ⟨.seq inner head,
        ReflTransTrace.step _ [] _ _ _ .step_stmts_cons (Imperative.seq_inner_starE _ first),
        by simp, by simp⟩
    · have entered := Imperative.stmts_cons_stepE _ statement head entry middle first
      rcases ih middle rest with ⟨next, front, notTerminal, exits⟩ | ⟨last, front, back, rfl, ranPrefix, ranSuffix⟩
      · exact .inl ⟨next, ReflTransTrace.trans _ entered front, notTerminal,
          fun label final eq => ReflTransTrace.trans _ entered (exits label final eq)⟩
      · exact .inr ⟨last, firstTrace ++ front, back, (List.append_assoc ..).symm,
          ReflTransTrace.trans _ entered ranPrefix, ranSuffix⟩
    · have lifted : Core.CoreStepStarE procedures (.stmts (statement :: head) entry) trace
          (.seq (.exiting label final) head) :=
        ReflTransTrace.step _ [] _ _ _ .step_stmts_cons (Imperative.seq_inner_starE _ first)
      have done : Core.CoreStepStarE procedures (.stmts (statement :: head) entry) trace
          (.exiting label final) := by
        simpa using ReflTransTrace.trans _ lifted
          (show Core.CoreStepStarE procedures (.seq (.exiting label final) head) [] (.exiting label final) from
            .step _ [] _ [] _ .step_seq_exit (.refl _))
      exact .inl ⟨_, done, by simp, fun _ _ eq => eq ▸ done⟩

/-- Replay a Core trace across the same chunk boundary as the Boole bind. -/
theorem sequence_replays_append {procedures : String → Option Core.Procedure}
    {head tail : List Core.Statement} {first rest : Computation Unit}
    {entryValid middleValid returnValid : State → Prop}
    (headReplay : CoreReplay procedures (fun state => .stmts head (coreEnv state)) first entryValid middleValid)
    (tailReplay : CoreReplay procedures (fun state => .stmts tail (coreEnv state)) rest middleValid returnValid) :
    CoreReplay procedures (fun state => .stmts (head ++ tail) (coreEnv state))
      (first >>= fun _ => rest) entryValid returnValid := by
  constructor
  · intro initial final trace ready ran passed
    rcases append_run_split head tail _ ran with
      ⟨_, _, impossible, _⟩ | ⟨middle, before, after, rfl, firstRan, tailRan⟩
    · exact False.elim (impossible final rfl)
    · obtain ⟨firstPass, tailPass⟩ := (coreChecksPass_append _ _).mp passed
      obtain ⟨state, returned, rfl, readyTail⟩ := headReplay.returns _ _ _ ready firstRan firstPass
      obtain ⟨result, replayed, same, valid⟩ := tailReplay.returns _ _ _ readyTail tailRan tailPass
      exact ⟨result, (Computation.run_bind _ _ _ _).mpr (.inl ⟨(), state, returned, replayed⟩), same, valid⟩
  · intro initial label final trace ready ran passed
    rcases append_run_split head tail _ ran with
      ⟨_, _, _, escaped⟩ | ⟨middle, before, after, rfl, firstRan, tailRan⟩
    · obtain ⟨result, replayed, same⟩ := headReplay.exits _ _ _ _ ready (escaped label final rfl) passed
      exact ⟨result, (Computation.run_bind _ _ _ _).mpr (.inr (.inl ⟨label, result, replayed, rfl⟩)), same⟩
    · obtain ⟨firstPass, tailPass⟩ := (coreChecksPass_append _ _).mp passed
      obtain ⟨state, returned, rfl, readyTail⟩ := headReplay.returns _ _ _ ready firstRan firstPass
      obtain ⟨result, replayed, same⟩ := tailReplay.exits _ _ _ _ readyTail tailRan tailPass
      exact ⟨result, (Computation.run_bind _ _ _ _).mpr (.inl ⟨(), state, returned, replayed⟩), same⟩
  · intro initial prior check reached ready ran passed failed
    have replayHead (next : Core.CoreConfig)
        (run : Core.CoreStepStarE procedures (.stmts head (coreEnv initial)) (prior ++ [.assert check]) next) :
        ∃ label state, (first >>= fun _ => rest).run initial (.assertionFailed label state) := by
      obtain ⟨label, state, replayed⟩ := headReplay.fails initial prior check next ready run passed failed
      exact ⟨label, state, (Computation.run_bind _ _ _ _).mpr
        (.inr (.inr (.inl ⟨label, state, replayed, rfl⟩)))⟩
    rcases append_run_split head tail _ ran with
      ⟨next, run, _, _⟩ | ⟨middle, before, after, split, firstRan, tailRan⟩
    · exact replayHead _ run
    cases suffix : after.reverse with
    | nil =>
      have empty := List.reverse_eq_nil_iff.mp suffix
      subst after
      rw [List.append_nil] at split
      exact replayHead _ (split ▸ firstRan)
    | cons event tailPrior =>
      have suffixEq : after = tailPrior.reverse ++ [event] := by
        simpa only [List.reverse_reverse, List.reverse_cons] using congrArg List.reverse suffix
      rw [suffixEq, ← List.append_assoc] at split
      obtain ⟨prefixEq, eventEq⟩ := List.append_singleton_inj.mp split
      subst event
      rw [prefixEq] at passed
      obtain ⟨firstPass, tailPass⟩ := (coreChecksPass_append _ _).mp passed
      obtain ⟨state, returned, rfl, readyTail⟩ := headReplay.returns _ _ _ ready firstRan firstPass
      rw [suffixEq] at tailRan
      obtain ⟨label, final, replayed⟩ := tailReplay.fails _ _ _ _ readyTail tailRan tailPass failed
      exact ⟨label, final, (Computation.run_bind _ _ _ _).mpr (.inl ⟨(), state, returned, replayed⟩)⟩

open Core.TypeSpec

private theorem eraseStatements_append (first rest : List Core.Statement) :
    eraseStatementsAnnotations (first ++ rest) =
      eraseStatementsAnnotations first ++ eraseStatementsAnnotations rest := by
  induction first with
  | nil => rfl
  | cons first tail ih => simp [eraseStatementsAnnotations, ih]

private theorem eraseStatements_length (statements : List Core.Statement) :
    (eraseStatementsAnnotations statements).length = statements.length := by
  induction statements with
  | nil => rfl
  | cons first rest ih => simp [eraseStatementsAnnotations, ih]

/-- The remaining statement proof compares one source statement with the
Core chunk it actually lowers to, preserving the entry invariant at a
normal return. A declaration can lower to several Core statements. -/
def StatementExecution (program : Core.Program) (labels : List String)
    (valid : Scope → TranslateState → Core.Expression.TyContext → TypeScopes → State → Prop) : Prop :=
  ∀ (source : BooleDDM.Statement SourceRange)
    (entry final : Scope) (before after : TranslateState)
    (context next : Core.Expression.TyContext) (scopes nextScopes : TypeScopes)
    (body : Computation Unit) (raw annotated : List Core.Statement),
    interpStmt denotation source entry = .ok (body, final) →
    lowerStatementChunk source before = .ok (raw, after) →
    eraseStatementsAnnotations annotated = eraseStatementsAnnotations raw →
    StatementsWellTyped program context scopes labels annotated next nextScopes →
    ExecutionAgreement program.findProcByString? annotated body
      (valid entry before context scopes) (valid final after next nextScopes)

/-- Compose the execution of an actual source statement list. The head and
tail use the intermediate scope produced by each of the two traversals and
the intermediate scopes of the declarative Core typing derivation. -/
theorem interpStmts_execution
    (program : Core.Program) (labels : List String)
    (valid : Scope → TranslateState → Core.Expression.TyContext → TypeScopes → State → Prop)
    (scopeEquiv : ∀ entry before context scopes other state,
      Strata.Util.HMaps.Equiv other scopes →
      valid entry before context scopes state → valid entry before context other state)
    (headAgreement : StatementExecution program labels valid)
    (source : List (BooleDDM.Statement SourceRange))
    {entry final : Scope} {before after : TranslateState}
    {context next : Core.Expression.TyContext} {scopes nextScopes : TypeScopes}
    {body : Computation Unit}
    {chunks : List (List Core.Statement)} {annotated : List Core.Statement}
    (interpreted : interpStmts denotation source entry = .ok (body, final))
    (lowered : source.mapM lowerStatementChunk before = .ok (chunks, after))
    (erased : eraseStatementsAnnotations annotated = eraseStatementsAnnotations chunks.flatten)
    (typed : StatementsWellTyped program context scopes labels annotated next nextScopes) :
    ExecutionAgreement program.findProcByString? annotated body
      (valid entry before context scopes) (valid final after next nextScopes) := by
  induction source generalizing entry final before after context next scopes nextScopes body chunks annotated with
  | nil =>
    rw [interpStmts.eq_def] at interpreted
    change Except.ok (Computation.pure (), entry) = .ok (body, final) at interpreted
    change Except.ok ([], before) = .ok (chunks, after) at lowered
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj interpreted)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj lowered)
    cases annotated with
    | cons statement rest => simp [eraseStatementsAnnotations] at erased
    | nil =>
      cases typed with
      | nil _ _ _ other equivalent =>
        have base := executionAgreement_nil program.findProcByString? (valid entry before context scopes)
        have preserve := fun state => scopeEquiv entry before context scopes _ state equivalent
        refine ⟨base.forward, fun initial final ready ran => preserve final
          (base.return_valid initial final ready ran), ?_⟩
        refine ⟨?_, base.replay.exits, base.replay.fails⟩
        intro initial final trace ready ran passed
        obtain ⟨state, returned, same, validReturn⟩ :=
          base.replay.returns initial final trace ready ran passed
        exact ⟨state, returned, same, preserve state validReturn⟩
  | cons statement rest ih =>
    obtain ⟨rawHead, middle, rawTail, firstLowered, restLowered, rfl⟩ :=
      mapM_lowerStatementChunk_cons statement rest before after chunks lowered
    rw [interpStmts.eq_def] at interpreted
    simp only [bind, StateT.bind, Except.bind] at interpreted
    cases firstRan : interpStmt denotation statement entry with
    | error error => simp [firstRan] at interpreted
    | ok result =>
      obtain ⟨first, intermediate⟩ := result
      cases restRan : interpStmts denotation rest intermediate with
      | error error => simp [firstRan, restRan] at interpreted
      | ok result =>
        obtain ⟨tail, last⟩ := result
        simp only [firstRan, restRan, pure, StateT.pure, Except.pure] at interpreted
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj interpreted)
        change ExecutionAgreement _ _ (first >>= fun _ => tail) _ _
        rw [List.flatten_cons, eraseStatements_append] at erased
        obtain ⟨headEq, tailEq⟩ := statementsEraseTypes_take_drop erased rawHead.length
        rw [← eraseStatements_length rawHead, List.take_left] at headEq
        rw [← eraseStatements_length rawHead, List.drop_left] at tailEq
        simp only [eraseStatements_length] at headEq tailEq
        rw [← List.take_append_drop rawHead.length annotated] at typed ⊢
        obtain ⟨middleContext, middleScopes, headTyped, tailTyped⟩ :=
          statementsWellTyped_append_split typed
        have firstAgrees := headAgreement statement entry intermediate before middle context
          middleContext scopes middleScopes first rawHead _ firstRan firstLowered headEq headTyped
        have restAgrees := ih restRan restLowered tailEq tailTyped
        exact ⟨fun _ ready _ ran => executionForward_append firstAgrees restAgrees ready ran,
          fun _ _ ready ran => executionReturn_append firstAgrees.return_valid restAgrees.return_valid ready ran,
          sequence_replays_append firstAgrees.replay restAgrees.replay⟩

/-- Apply the list induction to a body lowered by the original block
lowerer. The lowering states here come from its actual successful run. -/
theorem loweredBlock_execution
    (program : Core.Program) (labels : List String)
    (valid : Scope → TranslateState → Core.Expression.TyContext → TypeScopes → State → Prop)
    (scopeEquiv : ∀ entry before context scopes other state,
      Strata.Util.HMaps.Equiv other scopes →
      valid entry before context scopes state → valid entry before context other state)
    (headAgreement : StatementExecution program labels valid)
    {range annotation : SourceRange} {source : Array (BooleDDM.Statement SourceRange)}
    {entry final : Scope} {context next : Core.Expression.TyContext}
    {scopes nextScopes : TypeScopes} {body : Computation Unit}
    {raw annotated : List Core.Statement}
    (interpreted : interpStmts denotation source.toList entry = .ok (body, final))
    (lowered : BlockWasLowered (.block range ⟨annotation, source⟩) raw)
    (erased : eraseStatementsAnnotations annotated = eraseStatementsAnnotations raw)
    (typed : StatementsWellTyped program context scopes labels annotated next nextScopes) :
    ∃ before after, ExecutionAgreement program.findProcByString? annotated body
      (valid entry before context scopes) (valid final after next nextScopes) := by
  obtain ⟨before, after, chunks, ran, rfl⟩ := lowered.chunks
  exact ⟨before, after,
    interpStmts_execution program labels valid scopeEquiv headAgreement source.toList
      interpreted ran erased typed⟩

end Strata.Boole
