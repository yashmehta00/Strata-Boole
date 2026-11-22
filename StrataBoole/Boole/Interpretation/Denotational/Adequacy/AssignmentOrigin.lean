/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.AssignmentExecution
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.ExecutionLowering
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Statements
import all StrataBoole.Boole.Interpretation.Legacy.Interp
import all StrataBoole.Boole.Interpretation.Source
import all StrataBoole.Boole.Interpretation.Legacy.Semantics
import all StrataBoole.Verify
import all Strata.Languages.Core.Statement
import all Strata.DL.Imperative.Cmd

import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.SourceInterface
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.SourceFreshness

public section
namespace Strata.Boole
open StrataDDM

private theorem resolveWriting_name (range : SourceRange) (name : String)
    (scope next : Scope) (reference : Variable) (sort : ValueType)
    (resolved : resolveVariable range name true scope = .ok ((reference, sort), next)) :
    next = scope ∧ reference.coreIdent = ⟨name, ()⟩ := by
  unfold resolveVariable at resolved
  simp only [bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, Except.pure, reject, throw, throwThe, MonadExceptOf.throw,
    Function.comp_apply, StateT.lift, Functor.map, Except.map] at resolved
  cases localSlot : findBinding name scope.locals with
  | some binding =>
    simp only [localSlot, StateT.pure, Except.pure] at resolved
    obtain ⟨fields, scopeEq⟩ := Prod.mk.inj (Except.ok.inj resolved)
    obtain ⟨referenceEq, sortEq⟩ := Prod.mk.inj fields
    subst reference
    subst sort
    exact ⟨scopeEq.symm, rfl⟩
  | none =>
    simp only [localSlot] at resolved
    cases globalSlot : findBinding name scope.globals with
    | none => simp [globalSlot, StateT.lift, Functor.map, Except.map] at resolved
    | some binding =>
      simp only [globalSlot, Bool.true_and] at resolved
      split at resolved
      · simp [bind, Except.bind, StateT.bind, StateT.lift, Functor.map, Except.map] at resolved
      · simp only [StateT.pure, Except.pure] at resolved
        obtain ⟨fields, scopeEq⟩ := Prod.mk.inj (Except.ok.inj resolved)
        obtain ⟨referenceEq, sortEq⟩ := Prod.mk.inj fields
        subst reference
        subst sort
        exact ⟨scopeEq.symm, rfl⟩


/-- Recover the source RHS and the matching target name from an actual assignment. -/
theorem interpAssignment_origin (range lhsRange : SourceRange)
    {annotations annotation2} (name : Ann String SourceRange) (expression : Boole.Expr)
    {scope final : Scope} {body : Computation Unit}
    (ran : interpStmt denotation
      (.assign range annotations annotation2 (.lhsIdent lhsRange name) expression) scope =
      .ok (body, final)) :
    ∃ reference rhs,
      interpExpr denotation expression scope = .ok (rhs, scope) ∧
      body = Computation.assign reference rhs ∧ final = scope ∧ reference.coreIdent = ⟨name.val, ()⟩ := by
  rw [interpStmt] at ran
  obtain ⟨⟨reference, sort⟩, next, resolved, ran⟩ := split_run ran
  obtain ⟨scopeEq, named⟩ := resolveWriting_name range name.val scope next reference sort resolved
  subst next
  obtain ⟨rhs, last, read, ran⟩ := split_run ran
  have unchanged := interpExpr_readOnly _ _ _ _ _ read
  subst last
  have same := Except.ok.inj ran
  exact ⟨reference, rhs, read, (congrArg Prod.fst same).symm,
    (congrArg Prod.snd same).symm, named⟩

/-- A plain assignment lowers to one Core set using the actual lowered RHS. -/
theorem loweredAssignment_origin (range lhsRange : SourceRange)
    {annotations annotation2} (name : Ann String SourceRange) (expression : Boole.Expr)
    {before after : TranslateState} {raw : List Core.Statement}
    (ran : lowerStatementChunk
      (.assign range annotations annotation2 (.lhsIdent lhsRange name) expression) before = .ok (raw, after)) :
    ∃ rhs md, ExpressionWasLowered expression before rhs ∧
      raw = [.cmd (.cmd (.set ⟨name.val, ()⟩ (.det rhs) md))] := by
  simp only [lowerStatementChunk] at ran
  rw [toCoreStmt] at ran
  rw [toCoreStmt.lhsParts] at ran
  simp only [bind, StateT.bind, Except.bind, StateT.pure, Except.pure, pure] at ran
  cases rhsRun : toCoreExpr expression before with
  | error => simp [rhsRun] at ran
  | ok result =>
    obtain ⟨rhs, next⟩ := result
    simp only [rhsRun, toCoreMetaData, nestMapSet, get, getThe, MonadStateOf.get, StateT.get,
      bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
    have same := congrArg Prod.fst (Except.ok.inj ran)
    exact ⟨rhs, _, ⟨next, rhsRun⟩, same.symm⟩

/-- Reduce the two-way proof for a plain assignment to evaluation of
its actual RHS and preservation of the updated state's invariant. -/
theorem interpAssignment_execution (procedures : String → Option Core.Procedure)
    (range lhsRange : SourceRange)
    {annotations annotation2} (name : Ann String SourceRange) (expression : Boole.Expr)
    {scope final : Scope} {before after : TranslateState}
    {body : Computation Unit} {raw annotated : List Core.Statement}
    (valid : State → Prop)
    (interpreted : interpStmt denotation
      (.assign range annotations annotation2 (.lhsIdent lhsRange name) expression) scope =
      .ok (body, final))
    (lowered : lowerStatementChunk
      (.assign range annotations annotation2 (.lhsIdent lhsRange name) expression) before =
      .ok (raw, after))
    (erased : eraseStatementsAnnotations annotated = eraseStatementsAnnotations raw)
    (assignFacts : ∀ reference rhs rawRhs coreRhs,
      interpExpr denotation expression scope = .ok (rhs, scope) →
      ExpressionWasLowered expression before rawRhs →
      coreRhs.eraseTypes = rawRhs.eraseTypes →
      reference.coreIdent = ⟨name.val, ()⟩ →
      body = Computation.assign reference rhs →
      (∀ state, valid state → ∃ (previous value : Value) (oldValue newValue : Core.Expression.Val),
        state.lookup reference = some previous ∧
        (∀ n, reference = .global n → state.locals.lookup n = none) ∧
        rhs state = .ok value ∧ previous.sort = value.sort ∧
        coreValue? previous = some oldValue ∧ coreValue? value = some newValue ∧
        Core.Expression.eval coreRuntimeFactory (coreStore state) coreRhs = some newValue) ∧
      (∀ state, valid state → ∀ value,
        rhs state = .ok value → valid (state.update reference value))) :
    ExecutionAgreement procedures annotated body valid valid := by
  obtain ⟨reference, rhs, sourceRun, bodyEq, _, named⟩ :=
    interpAssignment_origin range lhsRange name expression interpreted
  obtain ⟨rawRhs, md, targetRun, rfl⟩ :=
    loweredAssignment_origin range lhsRange name expression lowered
  rcases annotated with _ | ⟨stmt, rest⟩
  · simp [eraseStatementsAnnotations] at erased
  have restNil : rest = [] := by
    have h := (List.cons.inj erased).2
    cases rest <;> simp_all [eraseStatementsAnnotations]
  subst rest
  have same := (List.cons.inj erased).1
  cases stmt <;> simp [eraseStatementAnnotations] at same
  case cmd command =>
    cases command <;> simp [Core.Command.eraseTypes] at same
    case cmd primitive =>
      cases primitive <;> simp at same
      case set id initializer actualMd =>
        cases initializer <;> simp [Imperative.ExprOrNondet.map] at same
        case det coreRhs =>
          obtain ⟨idEq, rhsEq, _⟩ := same
          have ⟨facts, keeps⟩ := assignFacts reference rhs rawRhs coreRhs sourceRun
            targetRun rhsEq named bodyEq
          rw [bodyEq, idEq, ← named]
          exact assignment_executionAgreement _ _ _ _ _ _ facts keeps

end Strata.Boole
