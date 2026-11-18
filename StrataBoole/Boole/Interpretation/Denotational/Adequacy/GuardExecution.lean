/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.Execution
import all StrataBoole.Boole.Semantics.Adequacy.SourceState
import all StrataBoole.Boole.Semantics.Adequacy.Statements
import all StrataBoole.Boole.Semantics.Semantics
import StrataBoole.Boole.Semantics.Adequacy.ExpressionExecution

public section

namespace Strata.Boole

/-- A deterministic guard with matching Boolean evaluations makes the same
choice in both semantics. Testing the guard preserves the entry state. -/
theorem deterministicGuard_execution (condition : Expression) (target : Core.Expression.Expr)
    (state : State) (actual : Bool)
    (sourceRun : condition state = .ok (.bool actual))
    (coreRun : coreGuardAllows (.det target) state actual) :
    (∀ outcome, (Computation.test (some condition)).run state outcome →
      ∃ result, outcome = .returned result state ∧ coreGuardAllows (.det target) state result) ∧
    (∀ result, coreGuardAllows (.det target) state result →
      (Computation.test (some condition)).run state (.returned result state)) := by
  have testRun (outcome : Outcome Bool) :
      (Computation.test (some condition)).run state outcome ↔ outcome = .returned actual state := by
    unfold Computation.test
    rw [Computation.run_evaluate_bind, sourceRun]
    rfl
  constructor
  · intro outcome ran
    exact ⟨actual, (testRun _).mp ran, coreRun⟩
  · intro result allowed
    have matched := (boolean_execution_iff sourceRun coreRun result).mpr allowed
    have eq : actual = result := by
      have same := Except.ok.inj (sourceRun.symm.trans matched)
      cases actual <;> cases result <;> simp_all [Value.bool]
    exact (testRun _).mpr (by rw [eq])

/-- A nondeterministic guard chooses either Boolean on both sides without
changing the state. -/
theorem nondeterministicGuard_execution (state : State) :
    (∀ outcome, (Computation.test none).run state outcome →
      ∃ result, outcome = .returned result state ∧ coreGuardAllows .nondet state result) ∧
    (∀ result, coreGuardAllows .nondet state result →
      (Computation.test none).run state (.returned result state)) := by
  constructor
  · intro outcome ran
    rcases ran with h | h
    · exact ⟨true, h, trivial⟩
    · exact ⟨false, h, trivial⟩
  · intro result _
    cases result
    · exact Or.inr rfl
    · exact Or.inl rfl

end Strata.Boole
