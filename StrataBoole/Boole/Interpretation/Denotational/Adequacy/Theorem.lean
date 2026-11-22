/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.DeclarativeAdequacy
import all StrataBoole.Boole.Interpretation.Denotational.CoreReference

public section

/-! ## The end-to-end theorem -/

namespace Strata.Boole
open StrataDDM

/-- Successful checker results satisfy Strata's declarative typing judgment.
The soundness theorem for the Strata checker supplies this implication. -/
private theorem checked_lowering_wellTyped
    {source : Boole.Program} {names : GlobalContext} {checked : Core.Program}
    (typeChecked : checkedCoreProgram source names = .ok checked) :
    Core.TypeSpec.ProgramWellTyped booleCoreTypingContext [] checked := by
  sorry

/-- For the scalar fragment, annotation preserves procedure headers, bodies,
and contracts after expression type annotations are erased. -/
private theorem checked_lowering_preserves_procedureSyntax
    {source : Boole.Program} {names : GlobalContext} {raw checked : Core.Program}
    (fragment : inConcreteCoreFragment source names)
    (lowered : toCoreProgram source names = .ok raw)
    (typeChecked : checkedCoreProgram source names = .ok checked) :
    procedureSyntax checked = procedureSyntax raw := by
  sorry

/-- The independent Boole meaning agrees with concrete Core execution of the
checked lowering: every accepted invocation has exactly the same returned
values and reachable assertion failures, and the declared contracts have the
same meaning. Equality supplies both behavior directions.

The fragment gate is syntactic. No caller supplies an assumption of simulation,
expression correctness, or representability. Those are internal proof tasks.
This theorem does not claim termination, runtime-error freedom, full traces,
or that any particular procedure satisfies its specification. -/
theorem denotation_agrees_with_core
    (source : Boole.Program) (names : GlobalContext)
    (meaning : ProgramMeaning) (checked : Core.Program)
    (fragment : inConcreteCoreFragment source names)
    (denoted : denoteProgram source names = .ok meaning)
    (typeChecked : checkedCoreProgram source names = .ok checked) :
    (∀ input, meaning.accepts input →
      meaning.observes input = coreObservations checked meaning.globals input) ∧
    contractsAgree meaning checked := by
  obtain ⟨raw, lowered⟩ : ∃ raw, toCoreProgram source names = .ok raw := by
    cases result : toCoreProgram source names with
    | error error => simp [checkedCoreProgram, result, bind, Except.bind] at typeChecked
    | ok raw => exact ⟨raw, rfl⟩
  exact denotation_agrees_with_typed_lowering source names meaning raw checked fragment denoted
    lowered (checked_lowering_wellTyped typeChecked)
    (checked_lowering_preserves_procedureSyntax fragment lowered typeChecked)

end Strata.Boole
