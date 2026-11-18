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

private theorem coreInit_trace (procedures : String → Option Core.Procedure)
    (state : State) (binding : Binding) (ty : Lambda.LTy)
    (md : Imperative.MetaData Core.Expression)
    (trace : Imperative.Trace Core.Expression) (reached : Core.CoreConfig)
    (run : Core.CoreStepStarE procedures
      (.stmt (Core.Statement.init ⟨binding.name, ()⟩ ty .nondet md) (coreEnv state)) trace reached) :
    (trace = [] ∧ reached = .stmt (Core.Statement.init ⟨binding.name, ()⟩ ty .nondet md)
      (coreEnv state)) ∨
    (∃ finalStore, trace = [] ∧ reached = .terminal ⟨finalStore, coreRuntimeFactory⟩ ∧
      Imperative.EvalCmdE Core.Expression coreRuntimeFactory (coreStore state)
        (.init ⟨binding.name, ()⟩ ty .nondet md) finalStore []) := by
  cases run with
  | refl => exact .inl ⟨rfl, rfl⟩
  | step _ _ _ _ _ first rest =>
    cases first with
    | step_cmd command =>
      cases command with
      | cmd_sem command =>
        cases command with
        | eval_init_unconstrained initialized typed wellFormed =>
          obtain ⟨sameConfig, emptyRest⟩ := Imperative.stepStmtStarE_from_terminal rest
          exact .inr ⟨_, by simp [emptyRest], by simpa [coreEnv] using sameConfig,
            .eval_init_unconstrained initialized typed wellFormed⟩

private theorem declare_nondet_run_shape (state : State) (binding : Binding)
    (localAbsent : state.locals.lookup binding.name = none) (outcome : Outcome Unit)
    (run : (Computation.declare binding none).run state outcome) :
    ∃ value, value.sort = binding.sort ∧
      outcome = .returned () { state with locals := state.locals ++ [(binding.name, value)] } := by
  unfold Computation.declare at run
  rcases (Computation.run_bind _ _ _ _).mp run with
    ⟨_, middle, getRun, restRun⟩ | ⟨_, _, getExits, _⟩ |
    ⟨_, _, getFails, _⟩ | ⟨_, _, getStuck, _⟩
  · simp [Computation.get] at getRun
    rcases getRun with ⟨rfl, rfl⟩
    simp only [localAbsent, Option.isSome_none, Bool.false_eq_true, ite_false] at restRun
    rcases (Computation.run_bind _ _ _ _).mp restRun with
      ⟨value, afterChoice, choiceRun, typeRun⟩ | ⟨_, _, chooseExits, _⟩ |
      ⟨_, _, chooseFails, _⟩ | ⟨_, _, chooseStuck, _⟩
    · simp [Computation.choose] at choiceRun
      rcases choiceRun with ⟨chosen, sameType, equalities⟩
      rcases equalities with ⟨valueEq, afterEq⟩
      subst value
      subst afterChoice
      simp [Computation.put, sameType] at typeRun
      exact ⟨chosen, sameType, typeRun⟩
    · simp [Computation.choose] at chooseExits
    · simp [Computation.choose] at chooseFails
    · simp [Computation.choose] at chooseStuck
  · simp [Computation.get] at getExits
  · simp [Computation.get] at getFails
  · simp [Computation.get] at getStuck

/-- A Core nondeterministic local initialization and a Boole uninitialized
declaration agree in both directions, provided the declared type is represented
on both sides and the entry state does not already contain that local. -/
theorem declaration_executionAgreement (procedures : String → Option Core.Procedure)
    (binding : Binding) (ty : Lambda.LTy) (md : Imperative.MetaData Core.Expression)
    (valid : State → Prop)
    (anchors : ∀ state, valid state → ∃ anchor literal,
      state.locals.lookup binding.name = none ∧
      coreStore state ⟨binding.name, ()⟩ = none ∧
      anchor.sort = binding.sort ∧ coreValue? anchor = some literal ∧
      Imperative.HasVal.valueOfTy (P := Core.Expression) coreRuntimeFactory literal ty)
    (representations : ∀ value, value.sort = binding.sort → ∃ literal,
      coreValue? value = some literal ∧
      Imperative.HasVal.valueOfTy (P := Core.Expression) coreRuntimeFactory literal ty)
    (preserved : ∀ state value, valid state → value.sort = binding.sort →
      valid { state with locals := state.locals ++ [(binding.name, value)] }) :
    ExecutionAgreement procedures [Core.Statement.init ⟨binding.name, ()⟩ ty .nondet md]
      (Computation.declare binding none) valid valid := by
  have replay : CoreReplay procedures
      (fun state => .stmt (Core.Statement.init ⟨binding.name, ()⟩ ty .nondet md) (coreEnv state))
      (Computation.declare binding none) valid valid := by
    constructor
    · intro initial final trace ready run passing
      rcases coreInit_trace procedures initial binding ty md trace (.terminal final) run with
        ⟨_, impossible⟩ | ⟨finalStore, traceEmpty, reachedEq, initRun⟩
      · cases impossible
      · obtain ⟨anchor, anchorRuntime, localAbsent, coreAbsent, anchorSort,
          anchorRep, anchorTyped⟩ := anchors initial ready
        cases initRun with
        | eval_init_unconstrained initialized chosenTyped wellFormed =>
          obtain ⟨value, valueRep, valueSort, sourceRun, finalStoreEq⟩ :=
            init_nondet_replays_choice initial binding ty anchor anchorRuntime _ finalStore
              initialized chosenTyped localAbsent anchorSort anchorRep anchorTyped
          have finalEq : final = coreEnv
              { initial with locals := initial.locals ++ [(binding.name, value)] } := by
            cases final
            simpa [coreEnv, ← finalStoreEq] using reachedEq
          exact ⟨_, sourceRun, finalEq, preserved initial value ready valueSort⟩
    · intro initial label final trace ready run _
      rcases coreInit_trace procedures initial binding ty md trace (.exiting label final) run with
        ⟨_, impossible⟩ | ⟨_, _, impossible, _⟩
      · cases impossible
      · cases impossible
    · intro initial prior check reached ready run _ _
      rcases coreInit_trace procedures initial binding ty md (prior ++ [.assert check]) reached run with
        ⟨empty, _⟩ | ⟨_, traceEmpty, _, _⟩ <;> simp at *

  refine ⟨?_, ?_, ?_⟩
  · intro initial ready outcome run
    obtain ⟨anchor, anchorRuntime, localAbsent, coreAbsent, anchorSort, anchorRep,
      anchorTyped⟩ := anchors initial ready
    obtain ⟨value, valueSort, outcomeEq⟩ := declare_nondet_run_shape initial binding
      localAbsent outcome run
    subst outcome
    obtain ⟨literal, represented, typed⟩ := representations value valueSort
    obtain ⟨_, coreRun⟩ := declare_nondet_forward initial binding value md ty
      coreAbsent localAbsent valueSort represented typed
    exact forward_singleton ⟨[], .step _ [] _ [] _ (.step_cmd (.cmd_sem coreRun)) (.refl _),
      by simp [coreChecksPass]⟩
  · intro initial final ready run
    obtain ⟨_, _, localAbsent, _, _, _, _⟩ := anchors initial ready
    obtain ⟨value, valueSort, outcomeEq⟩ := declare_nondet_run_shape initial binding
      localAbsent (.returned () final) run
    have finalEq : final = { initial with locals := initial.locals ++ [(binding.name, value)] } :=
      (Outcome.returned.inj outcomeEq).2
    rw [finalEq]
    exact preserved initial value ready valueSort
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
