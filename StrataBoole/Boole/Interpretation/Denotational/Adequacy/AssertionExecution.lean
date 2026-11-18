/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.Execution
public import StrataBoole.Boole.Semantics.Adequacy.ReplayCommands
import all StrataBoole.Boole.Semantics.Adequacy.Bodies
import all StrataBoole.Boole.Semantics.Adequacy.Statements
import all StrataBoole.Boole.Semantics.Semantics

public section

namespace Strata.Boole

/-- An assertion preserves the input state when true and emits a failure when
false. The premise relates the two evaluations on states in the entry invariant. -/
theorem assertion_executionAgreement (procedures : String → Option Core.Procedure)
    (valid : State → Prop) (sourceLabel targetLabel : String) (condition : Expression)
    (target : Core.Expression.Expr) (md : Imperative.MetaData Core.Expression)
    (booleanTotal : ∀ state, valid state → ∃ result, condition state = .ok (.bool result))
    (evaluationAgreement : ∀ state, valid state → ∀ result,
      condition state = .ok (.bool result) ↔
        Core.Expression.eval coreRuntimeFactory (coreStore state) target =
          some (if result then Imperative.HasBool.ttVal coreRuntimeFactory
            else Imperative.HasBool.ffVal coreRuntimeFactory)) :
    ExecutionAgreement procedures [.cmd (.cmd (.assert targetLabel target md))]
      (Computation.assertion sourceLabel condition) valid valid := by
  have replay := assertion_coreReplay procedures valid sourceLabel targetLabel condition target md
    evaluationAgreement
  refine ⟨?_, ?_, ?_⟩
  · intro initial ready outcome ran
    obtain ⟨result, source⟩ := booleanTotal initial ready
    have core := (evaluationAgreement initial ready result).1 source
    have step := (assertion_forward procedures initial sourceLabel targetLabel condition target md
      result outcome source core ran).1
    have shape := (assertion_run_iff source).mp ran
    let check : Imperative.EventArg Core.Expression :=
      ⟨coreRuntimeFactory, coreStore initial, targetLabel, target, md⟩
    have traced : Core.CoreStepStarE procedures
        (.stmt (.cmd (.cmd (.assert targetLabel target md))) (coreEnv initial))
        [Imperative.Event.assert check] (.terminal (coreEnv initial)) :=
      .step _ [Imperative.Event.assert check] _ [] _ step (.refl _)
    apply forward_singleton
    cases result <;> subst outcome
    · exact ⟨[], check, _, traced, by simp [coreChecksPass], core⟩
    · exact ⟨[Imperative.Event.assert check], traced, by simpa [coreChecksPass, check] using core⟩
  · intro initial final ready ran
    obtain ⟨result, source⟩ := booleanTotal initial ready
    have shape := (assertion_run_iff source).mp ran
    cases result
    · contradiction
    · exact (Outcome.returned.inj shape).2.symm ▸ ready
  · exact {
      returns := fun initial final trace ready ran passed =>
        replay.returns initial final trace ready (coreSingleton_terminal_inside ran) passed
      exits := fun initial label final trace ready ran passed =>
        replay.exits initial label final trace ready (coreSingleton_exit_inside ran) passed
      fails := fun initial prior check reached ready ran passed failed => by
        obtain ⟨inner, inside⟩ := coreSingleton_trace_inside ran
        exact replay.fails initial prior check inner ready inside passed failed
    }

end Strata.Boole
