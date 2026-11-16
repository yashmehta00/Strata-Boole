/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.Execution
import all StrataBoole.Boole.Semantics.Adequacy.Statements

public section

namespace Strata.Boole

/-- Core's nondeterministic assignment and Boole havoc make the same choice:
source values of the slot's sort correspond exactly to typed Core values, and
both update the same slot while leaving every other Core slot alone. -/
theorem havoc_choice_correspondence (state : State) (reference : Variable)
    (metadata : Imperative.MetaData Core.Expression) (prior : Value)
    {old : Core.Expression.Val}
    (sourceSlot : state.lookup reference = some prior)
    (unshadowed : ∀ name, reference = .global name → state.locals.lookup name = none)
    (coreSlot : coreStore state reference.coreIdent = some old)
    (encoded : coreValue? prior = some old) :
    (∀ value, value.sort = prior.sort → ∀ chosen : Core.Expression.Val,
      coreValue? value = some chosen →
      ∃ final, Imperative.EvalCmdE Core.Expression coreRuntimeFactory (coreStore state)
        (.set reference.coreIdent .nondet metadata) final [] ∧
        final = coreStore (state.update reference value)) ∧
    (∀ final, Imperative.EvalCmdE Core.Expression coreRuntimeFactory (coreStore state)
        (.set reference.coreIdent .nondet metadata) final [] →
      ∃ value chosen, value.sort = prior.sort ∧ coreValue? value = some chosen ∧
        (Computation.havoc reference prior.sort).run state
          (.returned () (state.update reference value)) ∧
        final = coreStore (state.update reference value)) := by
  constructor
  · intro value sameSort chosen represented
    obtain ⟨updated, typed⟩ := coreAssignment_update state reference sourceSlot
      unshadowed sameSort.symm encoded represented
    have sourceRun : (Computation.havoc reference prior.sort).run state
        (.returned () (state.update reference value)) := by
      unfold Computation.havoc
      apply (Computation.run_bind _ _ _ _).mpr
      left
      exact ⟨value, state, ⟨value, sameSort, rfl⟩,
        (assign_run_iff sourceSlot rfl sameSort.symm).mpr rfl⟩
    exact ⟨coreStore (state.update reference value),
      .eval_set_nondet updated typed
        (Core.coreEvaluator_WellFormedSemanticEvalVar coreRuntimeFactory), rfl⟩
  · intro final run
    exact match run with
    | .eval_set_nondet (v := chosen) actualUpdate sameType _ => by
      obtain ⟨old, ty, oldSlot, oldTyped, newTyped⟩ := sameType
      rw [coreSlot] at oldSlot
      obtain rfl := Option.some.inj oldSlot
      have sameRuntimeSort := Option.some.inj (oldTyped.2.symm.trans newTyped.2)
      obtain ⟨value, valueSort, represented⟩ :=
        coreTypedChoice_reifies encoded chosen newTyped.1 sameRuntimeSort.symm
      obtain ⟨expectedUpdate, _⟩ := coreAssignment_update state reference sourceSlot
        unshadowed valueSort.symm encoded represented
      have sourceRun : (Computation.havoc reference prior.sort).run state
          (.returned () (state.update reference value)) := by
        unfold Computation.havoc
        apply (Computation.run_bind _ _ _ _).mpr
        left
        exact ⟨value, state, ⟨value, valueSort, rfl⟩,
          (assign_run_iff sourceSlot rfl valueSort.symm).mpr rfl⟩
      exact ⟨value, chosen, valueSort, represented, sourceRun,
        Imperative.UpdateStateUniqueResult actualUpdate expectedUpdate⟩

end Strata.Boole
