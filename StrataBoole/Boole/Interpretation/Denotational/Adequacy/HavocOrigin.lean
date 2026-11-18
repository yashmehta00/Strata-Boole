/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.HavocExecutionAgreement
import all StrataBoole.Boole.Semantics.Adequacy.ExecutionLowering
import all StrataBoole.Boole.Semantics.Adequacy.Statements
import all StrataBoole.Boole.Interp
import all StrataBoole.Boole.Semantics.Semantics
import all StrataBoole.Verify
import all Strata.Languages.Core.Statement
import all Strata.DL.Imperative.Cmd

public section
namespace Strata.Boole
open StrataDDM

/-- Recover the target slot and sort of an actual Boole havoc statement.
The lowering emits a single nondeterministic assignment to that same name. -/
theorem havoc_origin (range : SourceRange)
    (annotations : Ann (Option (BooleDDM.MetadataAnn SourceRange)) SourceRange)
    (name : Ann String SourceRange) (scope final : Scope) (before after : TranslateState)
    (body : Computation Unit) (raw : List Core.Statement)
    (interpreted : interpStmt denotation (.havoc_statement range annotations name) scope =
      .ok (body, final))
    (lowered : lowerStatementChunk (.havoc_statement range annotations name) before = .ok (raw, after)) :
    ∃ reference sort md,
      body = Computation.havoc reference sort ∧
      final = scope ∧ after = before ∧ reference.coreIdent = ⟨name.val, ()⟩ ∧
      raw = [.cmd (.cmd (.set reference.coreIdent .nondet md))] := by
  rw [interpStmt] at interpreted
  simp only [bind, StateT.bind, Except.bind] at interpreted
  simp only [lowerStatementChunk] at lowered
  rw [toCoreStmt] at lowered
  simp only [toCoreMetaData, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
    get, getThe, MonadStateOf.get, StateT.get] at lowered
  have lowerShape := Except.ok.inj lowered
  cases resolved : resolveVariable range name.val true scope with
  | error => simp [resolved] at interpreted
  | ok result =>
    obtain ⟨⟨reference, sort⟩, entry⟩ := result
    simp only [resolved] at interpreted
    have eq := Except.ok.inj interpreted
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj eq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj lowerShape
    unfold resolveVariable at resolved
    simp only [bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, Except.pure, reject, throw, throwThe, MonadExceptOf.throw,
      Function.comp_apply, StateT.lift, Functor.map, Except.map] at resolved
    cases localSlot : findBinding name.val scope.locals with
    | some binding =>
      simp only [localSlot, StateT.pure, Except.pure] at resolved
      obtain ⟨fields, scopeEq⟩ := Prod.mk.inj (Except.ok.inj resolved)
      obtain ⟨referenceEq, sortEq⟩ := Prod.mk.inj fields
      subst reference
      subst sort
      exact ⟨_, _, _, rfl, scopeEq.symm, rfl, rfl, rfl⟩
    | none =>
      simp only [localSlot] at resolved
      cases globalSlot : findBinding name.val scope.globals with
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
          exact ⟨_, _, _, rfl, scopeEq.symm, rfl, rfl, rfl⟩

/-- A source havoc and its annotation-preserving lowering agree when the
resolved variable has a represented, writable slot of the source sort. -/
theorem interpHavoc_execution (procedures : String → Option Core.Procedure)
    (range : SourceRange)
    (annotations : Ann (Option (BooleDDM.MetadataAnn SourceRange)) SourceRange)
    (name : Ann String SourceRange) (scope final : Scope) (before after : TranslateState)
    (body : Computation Unit) (raw annotated : List Core.Statement)
    (valid : State → Prop)
    (interpreted : interpStmt denotation (.havoc_statement range annotations name) scope =
      .ok (body, final))
    (lowered : lowerStatementChunk (.havoc_statement range annotations name) before = .ok (raw, after))
    (erased : eraseStatementsAnnotations annotated = eraseStatementsAnnotations raw)
    (slotFacts : ∀ reference sort, body = Computation.havoc reference sort →
      reference.coreIdent = ⟨name.val, ()⟩ →
      (∀ state, valid state → ∃ prior old,
        state.lookup reference = some prior ∧ prior.sort = sort ∧
        (∀ n, reference = .global n → state.locals.lookup n = none) ∧
        coreStore state reference.coreIdent = some old ∧ coreValue? prior = some old) ∧
      (∀ value, value.sort = sort → ∃ chosen, coreValue? value = some chosen) ∧
      (∀ state, valid state → ∀ value, value.sort = sort → valid (state.update reference value))) :
    ExecutionAgreement procedures annotated body valid valid := by
  obtain ⟨reference, sort, md, bodyEq, _, _, named, rfl⟩ :=
    havoc_origin range annotations name scope final before after body raw interpreted lowered
  obtain ⟨facts, reifies, preserved⟩ := slotFacts reference sort bodyEq named
  subst body
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
        case nondet =>
          obtain ⟨rfl, _⟩ := same
          exact havoc_executionAgreement procedures reference sort actualMd valid facts reifies preserved

end Strata.Boole
