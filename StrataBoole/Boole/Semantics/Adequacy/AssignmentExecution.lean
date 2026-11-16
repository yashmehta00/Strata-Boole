/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.Execution
import all StrataBoole.Boole.Semantics.Adequacy.Bodies
import all StrataBoole.Boole.Semantics.Adequacy.Statements
import all StrataBoole.Boole.Semantics.Semantics

public section

namespace Strata.Boole

private theorem coreSet_trace (procedures : String → Option Core.Procedure)
    (state : State) (reference : Variable) (rhs : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (trace : Imperative.Trace Core.Expression) (reached : Core.CoreConfig)
    (run : Core.CoreStepStarE procedures
      (.stmt (.cmd (.cmd (.set reference.coreIdent (.det rhs) md))) (coreEnv state)) trace reached) :
    (trace = [] ∧ reached = .stmt (.cmd (.cmd (.set reference.coreIdent (.det rhs) md)))
      (coreEnv state)) ∨
    (∃ finalStore, trace = [] ∧ reached = .terminal ⟨finalStore, coreRuntimeFactory⟩ ∧
      Imperative.EvalCmdE Core.Expression coreRuntimeFactory (coreStore state)
        (.set reference.coreIdent (.det rhs) md) finalStore []) := by
  cases run with
  | refl => exact .inl ⟨rfl, rfl⟩
  | step _ _ _ _ _ first rest =>
    cases first with
    | step_cmd command =>
      cases command with
      | cmd_sem command =>
        cases command with
        | eval_set evaluated updated typed wellFormed =>
          obtain ⟨sameConfig, emptyRest⟩ := Imperative.stepStmtStarE_from_terminal rest
          exact .inr ⟨_, by simp [emptyRest], by simpa [coreEnv] using sameConfig,
            .eval_set evaluated updated typed wellFormed⟩

/-- A deterministic assignment agrees in both directions when the source and
Core expressions evaluate to the same represented value. The invariant must
provide a typed, unshadowed target slot and be preserved by the resulting
source update. -/
theorem assignment_executionAgreement (procedures : String → Option Core.Procedure)
    (valid : State → Prop) (reference : Variable) (rhs : Expression)
    (coreRhs : Core.Expression.Expr) (md : Imperative.MetaData Core.Expression)
    (assignmentFacts : ∀ state, valid state →
      ∃ (previous value : Value) (oldValue newValue : Core.Expression.Val),
        state.lookup reference = some previous ∧
        (∀ name, reference = .global name → state.locals.lookup name = none) ∧
        rhs state = .ok value ∧ previous.sort = value.sort ∧
        coreValue? previous = some oldValue ∧ coreValue? value = some newValue ∧
        Core.Expression.eval coreRuntimeFactory (coreStore state) coreRhs = some newValue)
    (preserved : ∀ state, valid state → ∀ value,
      rhs state = .ok value → valid (state.update reference value)) :
    ExecutionAgreement procedures [.cmd (.cmd (.set reference.coreIdent (.det coreRhs) md))]
      (Computation.assign reference rhs) valid valid := by
  have replay : CoreReplay procedures
      (fun state => .stmt (.cmd (.cmd (.set reference.coreIdent (.det coreRhs) md))) (coreEnv state))
      (Computation.assign reference rhs) valid valid := by
    constructor
    · intro initial final trace ready run passing
      obtain ⟨previous, value, oldValue, newValue, slot, unshadowed,
        rhsEval, sameType, oldRep, newRep, coreEval⟩ := assignmentFacts initial ready
      let updated := initial.update reference value
      rcases coreSet_trace procedures initial reference coreRhs md trace (.terminal final) run with
        ⟨_, impossible⟩ | ⟨finalStore, traceEmpty, reachedEq, commandRun⟩
      · cases impossible
      · have agreement := assignment_agrees initial reference rhs coreRhs md finalStore
          slot unshadowed rhsEval sameType oldRep newRep coreEval
        have sourceExists := agreement.mpr commandRun
        obtain ⟨sourceFinal, sourceRun, storeEq⟩ := sourceExists
        have sourceShape := (assign_run_iff slot rhsEval sameType).mp sourceRun
        have sourceEq := (Outcome.returned.inj sourceShape).2
        have resultStoreEq : finalStore = coreStore updated := by
          rw [sourceEq] at storeEq
          exact storeEq.symm
        have finalEq : final = coreEnv updated := by
          have finalEnvEq := Imperative.Config.terminal.inj reachedEq
          cases final
          cases finalEnvEq
          simp [coreEnv, resultStoreEq]
        subst sourceFinal
        exact ⟨updated, sourceRun, finalEq, preserved initial ready value rhsEval⟩
    · intro initial label final trace ready run _
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := assignmentFacts initial ready
      rcases coreSet_trace procedures initial reference coreRhs md trace (.exiting label final) run with
        ⟨_, impossible⟩ | ⟨_, _, impossible, _⟩
      · cases impossible
      · cases impossible
    · intro initial prior check reached ready run _ _
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _⟩ := assignmentFacts initial ready
      rcases coreSet_trace procedures initial reference coreRhs md (prior ++ [.assert check]) reached run with
        ⟨traceEmpty, _⟩ | ⟨_, traceEmpty, _, _⟩ <;> simp at traceEmpty

  refine ⟨?_, ?_, ?_⟩
  · intro initial ready outcome run
    obtain ⟨previous, value, oldValue, newValue, slot, unshadowed,
      rhsEval, sameType, oldRep, newRep, coreEval⟩ := assignmentFacts initial ready
    let updated := initial.update reference value
    have outcomeEq := (assign_run_iff slot rhsEval sameType).mp run
    subst outcome
    have agreement := assignment_agrees initial reference rhs coreRhs md (coreStore updated)
      slot unshadowed rhsEval sameType oldRep newRep coreEval
    have commandRun := agreement.mp ⟨updated,
      (assign_run_iff slot rhsEval sameType).mpr rfl, rfl⟩
    have step : Core.CoreStepE procedures
        (.stmt (.cmd (.cmd (.set reference.coreIdent (.det coreRhs) md))) (coreEnv initial)) []
        (.terminal (coreEnv updated)) :=
      .step_cmd (Core.EvalCommandE.cmd_sem commandRun)
    apply forward_singleton
    exact ⟨[], ReflTransTrace.step _ _ _ _ _ step (.refl _), by simp [coreChecksPass]⟩
  · intro initial final ready run
    obtain ⟨previous, value, _, _, slot, _, rhsEval, sameType, _, _, _⟩ := assignmentFacts initial ready
    have outcomeEq := (assign_run_iff slot rhsEval sameType).mp run
    have sourceEq := (Outcome.returned.inj outcomeEq).2
    exact sourceEq.symm ▸ preserved initial ready value rhsEval
  · exact {
      returns := fun initial final trace ready run passing =>
        replay.returns initial final trace ready (coreSingleton_terminal_inside run) passing
      exits := fun initial label final trace ready run passing =>
        replay.exits initial label final trace ready (coreSingleton_exit_inside run) passing
      fails := fun initial prior check reached ready run passing failed => by
        obtain ⟨inner, inside⟩ := coreSingleton_trace_inside run
        exact replay.fails initial prior check inner ready inside passing failed
    }

end Strata.Boole
