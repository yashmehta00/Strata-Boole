/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.HavocExecution
public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.ReplayCommands
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Execution
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Bodies
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Statements
import all StrataBoole.Boole.Interpretation.Legacy.Semantics

public section

namespace Strata.Boole

private theorem havoc_run_iff {state : State} {reference : Variable} {sort : ValueType}
    {prior : Value} {outcome : Outcome Unit}
    (slot : state.lookup reference = some prior) (priorSort : prior.sort = sort) :
    (Computation.havoc reference sort).run state outcome ↔
      ∃ value, value.sort = sort ∧ outcome = .returned () (state.update reference value) := by
  change (Computation.bind (Computation.choose sort)
    (fun value => Computation.assign reference (fun _ => .ok value))).run state outcome ↔ _
  constructor
  · intro run
    rcases (Computation.run_bind _ _ _ _).mp run with
      ⟨value, middle, chooseRun, assignRun⟩ | no | no | no
    · simp only [Computation.choose] at chooseRun
      obtain ⟨selected, selectedSort, chooseEq⟩ := chooseRun
      have retEq := Outcome.returned.inj chooseEq
      cases retEq.2
      rw [retEq.1] at assignRun
      have assigned := (assign_run_iff slot rfl (priorSort.trans selectedSort.symm)).mp assignRun
      exact ⟨selected, selectedSort, assigned⟩
    · simp [Computation.choose] at no
    · simp [Computation.choose] at no
    · simp [Computation.choose] at no
  · rintro ⟨value, valueSort, rfl⟩
    apply (Computation.run_bind _ _ _ _).mpr
    left
    exact ⟨value, state, ⟨value, valueSort, rfl⟩,
      (assign_run_iff slot rfl (priorSort.trans valueSort.symm)).mpr rfl⟩

private theorem coreHavoc_trace (procedures : String → Option Core.Procedure)
    (state : State) (reference : Variable) (metadata : Imperative.MetaData Core.Expression)
    (trace : Imperative.Trace Core.Expression) (reached : Core.CoreConfig)
    (run : Core.CoreStepStarE procedures
      (.stmt (.cmd (.cmd (.set reference.coreIdent .nondet metadata))) (coreEnv state)) trace reached) :
    (trace = [] ∧ reached = .stmt (.cmd (.cmd (.set reference.coreIdent .nondet metadata)))
      (coreEnv state)) ∨
    (∃ final, trace = [] ∧ reached = .terminal ⟨final, coreRuntimeFactory⟩ ∧
      Imperative.EvalCmdE Core.Expression coreRuntimeFactory (coreStore state)
        (.set reference.coreIdent .nondet metadata) final []) := by
  cases run with
  | refl => exact .inl ⟨rfl, rfl⟩
  | step _ _ _ _ _ first rest =>
    cases first with
    | step_cmd command =>
      cases command with
      | cmd_sem command =>
        cases command with
        | eval_set_nondet update typed wf =>
          obtain ⟨sameConfig, emptyRest⟩ := Imperative.stepStmtStarE_from_terminal rest
          exact .inr ⟨_, by simp [emptyRest], by simpa [coreEnv] using sameConfig,
            .eval_set_nondet update typed wf⟩

/-- A Core nondeterministic assignment implements source havoc when every
valid entry state has a represented slot of the requested sort, Core can
reify each source choice, and validity is preserved by havoc updates. -/
theorem havoc_executionAgreement (procedures : String → Option Core.Procedure)
    (reference : Variable) (sort : ValueType) (metadata : Imperative.MetaData Core.Expression)
    (valid : State → Prop)
    (havocFacts : ∀ state, valid state → ∃ prior old,
      state.lookup reference = some prior ∧ prior.sort = sort ∧
      (∀ name, reference = .global name → state.locals.lookup name = none) ∧
      coreStore state reference.coreIdent = some old ∧ coreValue? prior = some old)
    (reifies : ∀ value, value.sort = sort → ∃ chosen : Core.Expression.Val,
      coreValue? value = some chosen)
    (preserves : ∀ state, valid state → ∀ value, value.sort = sort →
      valid (state.update reference value)) :
    ExecutionAgreement procedures [.cmd (.cmd (.set reference.coreIdent .nondet metadata))]
      (Computation.havoc reference sort) valid valid := by
  have replay : CoreReplay procedures
      (fun state => .stmt (.cmd (.cmd (.set reference.coreIdent .nondet metadata))) (coreEnv state))
      (Computation.havoc reference sort) valid valid := by
    constructor
    · intro initial final trace ready run passing
      obtain ⟨prior, old, slot, sameSort, unshadowed, coreSlot, encoded⟩ :=
        havocFacts initial ready
      rcases coreHavoc_trace procedures initial reference metadata trace (.terminal final) run with
        ⟨_, impossible⟩ | ⟨finalStore, traceEmpty, reachedEq, command⟩
      · cases impossible
      · have agreement := havoc_choice_correspondence initial reference metadata prior
          slot unshadowed coreSlot encoded
        obtain ⟨value, chosen, valueSort, represented, sourceRun, resultStoreEq⟩ :=
          agreement.2 finalStore command
        have sourceRunSort : (Computation.havoc reference sort).run initial
            (.returned () (initial.update reference value)) := by
          simpa [sameSort] using sourceRun
        have envEq := Imperative.Config.terminal.inj reachedEq
        have finalEq : final = coreEnv (initial.update reference value) := by
          cases final
          cases envEq
          simp [coreEnv, resultStoreEq]
        exact ⟨initial.update reference value, sourceRunSort, finalEq, preserves initial ready value
          (valueSort.trans sameSort)⟩
    · intro initial label final trace ready run _
      rcases coreHavoc_trace procedures initial reference metadata trace (.exiting label final) run with
        ⟨_, impossible⟩ | ⟨_, _, impossible, _⟩
      · cases impossible
      · cases impossible
    · intro initial prior check reached ready run _ _
      rcases coreHavoc_trace procedures initial reference metadata
        (prior ++ [.assert check]) reached run with
        ⟨empty, _⟩ | ⟨_, traceEmpty, _, _⟩
      · simp at empty
      · simp at traceEmpty

  refine ⟨?_, ?_, ?_⟩
  · intro initial ready outcome run
    obtain ⟨prior, old, slot, sameSort, unshadowed, coreSlot, encoded⟩ :=
      havocFacts initial ready
    obtain ⟨value, valueSort, rfl⟩ := (havoc_run_iff slot sameSort).mp run
    obtain ⟨chosen, represented⟩ := reifies value valueSort
    obtain ⟨target, command, targetEq⟩ :=
      (havoc_choice_correspondence initial reference metadata prior slot unshadowed coreSlot encoded).1
        value (valueSort.trans sameSort.symm) chosen represented
    have coreStep : Core.CoreStepE procedures
        (.stmt (.cmd (.cmd (.set reference.coreIdent .nondet metadata))) (coreEnv initial)) []
        (.terminal (coreEnv (initial.update reference value))) := by
      subst target
      exact .step_cmd (Core.EvalCommandE.cmd_sem command)
    apply forward_singleton
    exact ⟨[], ReflTransTrace.step _ _ _ _ _ coreStep (.refl _), by simp [coreChecksPass]⟩
  · intro initial final ready run
    obtain ⟨prior, _, slot, sameSort, _, _, _⟩ := havocFacts initial ready
    obtain ⟨value, valueSort, same⟩ := (havoc_run_iff slot sameSort).mp run
    exact (Outcome.returned.inj same).2.symm ▸ preserves initial ready value valueSort
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
