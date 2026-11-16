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

private theorem coreInitDet_trace (procedures : String → Option Core.Procedure)
    (state : State) (binding : Binding) (ty : Lambda.LTy)
    (rhs : Core.Expression.Expr) (md : Imperative.MetaData Core.Expression)
    (trace : Imperative.Trace Core.Expression) (reached : Core.CoreConfig)
    (run : Core.CoreStepStarE procedures
      (.stmt (Core.Statement.init ⟨binding.name, ()⟩ ty (.det rhs) md) (coreEnv state)) trace reached) :
    (trace = [] ∧ reached = .stmt (Core.Statement.init ⟨binding.name, ()⟩ ty (.det rhs) md)
      (coreEnv state)) ∨
    (∃ finalStore, trace = [] ∧ reached = .terminal ⟨finalStore, coreRuntimeFactory⟩ ∧
      Imperative.EvalCmdE Core.Expression coreRuntimeFactory (coreStore state)
        (.init ⟨binding.name, ()⟩ ty (.det rhs) md) finalStore []) := by
  cases run with
  | refl => exact .inl ⟨rfl, rfl⟩
  | step _ _ _ _ _ first rest =>
    cases first with
    | step_cmd command =>
      cases command with
      | cmd_sem command =>
        cases command with
        | eval_init evaluated initialized typed wellFormed =>
          obtain ⟨sameConfig, emptyRest⟩ := Imperative.stepStmtStarE_from_terminal rest
          exact .inr ⟨_, by simp [emptyRest], by simpa [coreEnv] using sameConfig,
            .eval_init evaluated initialized typed wellFormed⟩

private theorem declare_det_run_shape (state : State) (binding : Binding)
    (initializer : Expression) (value : Value)
    (localAbsent : state.locals.lookup binding.name = none)
    (sameType : value.sort = binding.sort) (evaluated : initializer state = .ok value)
    (outcome : Outcome Unit)
    (run : (Computation.declare binding (some initializer)).run state outcome) :
    outcome = .returned () { state with locals := state.locals ++ [(binding.name, value)] } := by
  unfold Computation.declare at run
  rcases (Computation.run_bind _ _ _ _).mp run with
    ⟨_, middle, getRun, restRun⟩ | ⟨_, _, getExits, _⟩ |
    ⟨_, _, getFails, _⟩ | ⟨_, _, getStuck, _⟩
  · simp [Computation.get] at getRun
    rcases getRun with ⟨rfl, rfl⟩
    simp only [localAbsent, Option.isSome_none, Bool.false_eq_true, ite_false] at restRun
    rcases (Computation.run_bind _ _ _ _).mp restRun with
      ⟨value', afterEval, evalRun, typeRun⟩ | ⟨_, _, evalExits, _⟩ |
      ⟨_, _, evalFails, _⟩ | ⟨_, _, evalStuck, _⟩
    · simp [Computation.evaluate, evaluated] at evalRun
      rcases evalRun with ⟨rfl, rfl⟩
      simp [Computation.put, sameType] at typeRun
      exact typeRun
    · simp [Computation.evaluate, evaluated] at evalExits
    · simp [Computation.evaluate, evaluated] at evalFails
    · simp [Computation.evaluate, evaluated] at evalStuck
  · simp [Computation.get] at getExits
  · simp [Computation.get] at getFails
  · simp [Computation.get] at getStuck

/-- A deterministic local initialization agrees in both directions when the
source and Core initializers denote the same typed value. Entry and return
invariants are stated separately so callers can reflect source-state updates. -/
theorem deterministicDeclaration_executionAgreement
    (procedures : String → Option Core.Procedure) (binding : Binding)
    (initializer : Expression) (coreInitializer : Core.Expression.Expr)
    (ty : Lambda.LTy) (md : Imperative.MetaData Core.Expression)
    (entryValid returnValid : State → Prop)
    (initializerFacts : ∀ state, entryValid state → ∃ value literal,
      state.locals.lookup binding.name = none ∧
      coreStore state ⟨binding.name, ()⟩ = none ∧
      initializer state = .ok value ∧ value.sort = binding.sort ∧
      coreValue? value = some literal ∧
      Imperative.HasVal.valueOfTy (P := Core.Expression) coreRuntimeFactory literal ty ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state) coreInitializer = some literal)
    (preserved : ∀ state value, entryValid state → value.sort = binding.sort →
      returnValid { state with locals := state.locals ++ [(binding.name, value)] }) :
    ExecutionAgreement procedures
      [Core.Statement.init ⟨binding.name, ()⟩ ty (.det coreInitializer) md]
      (Computation.declare binding (some initializer)) entryValid returnValid := by
  have replay : CoreReplay procedures
      (fun state => .stmt
        (Core.Statement.init ⟨binding.name, ()⟩ ty (.det coreInitializer) md) (coreEnv state))
      (Computation.declare binding (some initializer)) entryValid returnValid := by
    constructor
    · intro initial final trace ready run passing
      rcases coreInitDet_trace procedures initial binding ty coreInitializer md trace
        (.terminal final) run with ⟨_, impossible⟩ | ⟨finalStore, _, reachedEq, initRun⟩
      · cases impossible
      · obtain ⟨value, literal, localAbsent, coreAbsent, sourceEval, sourceSort,
          represented, typed, coreEval⟩ := initializerFacts initial ready
        cases initRun with
        | eval_init actualCoreEval initialised actualTyped wellFormed =>
          have sameLiteral := Option.some.inj (actualCoreEval.symm.trans coreEval)
          obtain ⟨sourceRun, generatedCoreRun⟩ := declare_det_forward initial binding value
            initializer coreInitializer md ty coreAbsent localAbsent sourceSort represented
            typed sourceEval coreEval
          cases generatedCoreRun with
          | eval_init generatedEval generatedInitialised _ _ =>
            have sameGenerated := Option.some.inj (generatedEval.symm.trans coreEval)
            rw [sameLiteral] at initialised
            rw [sameGenerated] at generatedInitialised
            have sameStore := Imperative.InitStateUniqueResult initialised generatedInitialised
            have finalEq : final = coreEnv
                { initial with locals := initial.locals ++ [(binding.name, value)] } := by
              cases final
              simpa [coreEnv, sameStore] using reachedEq
            exact ⟨_, sourceRun, finalEq, preserved initial value ready sourceSort⟩
    · intro initial label final trace ready run _
      rcases coreInitDet_trace procedures initial binding ty coreInitializer md trace
        (.exiting label final) run with ⟨_, impossible⟩ | ⟨_, _, impossible, _⟩
      · cases impossible
      · cases impossible
    · intro initial prior check reached ready run _ _
      rcases coreInitDet_trace procedures initial binding ty coreInitializer md
        (prior ++ [.assert check]) reached run with
        ⟨empty, _⟩ | ⟨_, traceEmpty, _, _⟩ <;> simp at *

  refine ⟨?_, ?_, ?_⟩
  · intro initial ready outcome run
    obtain ⟨value, literal, localAbsent, coreAbsent, sourceEval, sourceSort,
      represented, typed, coreEval⟩ := initializerFacts initial ready
    have outcomeEq := declare_det_run_shape initial binding initializer value
      localAbsent sourceSort sourceEval outcome run
    subst outcome
    obtain ⟨_, coreRun⟩ := declare_det_forward initial binding value initializer
      coreInitializer md ty coreAbsent localAbsent sourceSort represented typed sourceEval coreEval
    exact forward_singleton ⟨[], .step _ [] _ [] _ (.step_cmd (.cmd_sem coreRun)) (.refl _),
      by simp [coreChecksPass]⟩
  · intro initial final ready run
    obtain ⟨value, _, localAbsent, _, sourceEval, sourceSort, _, _, _⟩ :=
      initializerFacts initial ready
    have outcomeEq := declare_det_run_shape initial binding initializer value
      localAbsent sourceSort sourceEval (.returned () final) run
    have finalEq : final = { initial with locals := initial.locals ++ [(binding.name, value)] } :=
      (Outcome.returned.inj outcomeEq).2
    rw [finalEq]
    exact preserved initial value ready sourceSort
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
