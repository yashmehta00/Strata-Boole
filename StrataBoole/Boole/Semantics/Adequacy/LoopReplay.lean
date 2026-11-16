/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.Execution
import all StrataBoole.Boole.Semantics.Adequacy.Bodies
import all StrataBoole.Boole.Semantics.Semantics
import Strata.DL.Imperative.StmtSemanticsProps
import Strata.Util.RelationsProps

import all StrataBoole.Boole.Semantics.Adequacy.Statements

public section

namespace Strata.Boole

/-- If Core's deterministic loop guard is false at entry, a run either has
not taken a step or has immediately returned with no events or state changes.
This is the zero-iteration case used when replaying loops. -/
theorem coreLoop_false_shape (procedures : String → Option Core.Procedure)
    (guard : Core.Expression.Expr) (measure : Option Core.Expression.Expr)
    (invariants : List (String × Core.Expression.Expr)) (body : List Core.Statement)
    (metadata : Imperative.MetaData Core.Expression) (state : State)
    (trace : Imperative.Trace Core.Expression) (reached : Core.CoreConfig)
    (guardFalse : Core.Expression.eval coreRuntimeFactory (coreStore state) guard =
      some (Imperative.HasBool.ffVal coreRuntimeFactory))
    (run : Core.CoreStepStarE procedures
      (.stmt (.loop (.det guard) measure invariants body metadata) (coreEnv state)) trace reached) :
    (trace = [] ∧ reached = .stmt (.loop (.det guard) measure invariants body metadata)
      (coreEnv state)) ∨ (trace = [] ∧ reached = .terminal (coreEnv state)) := by
  cases run with
  | refl => exact .inl ⟨rfl, rfl⟩
  | step _ emitted _ restTrace _ first rest =>
    cases first with
    | step_loop_enter entered =>
      have falseEval : Core.Expression.eval (coreEnv state).factory (coreEnv state).store guard =
          some (Imperative.HasBool.ffVal (coreEnv state).factory) := by
        simpa [coreEnv] using guardFalse
      rw [falseEval] at entered
      cases entered
    | step_loop_exit _ =>
      have same := Imperative.stepStmtStarE_from_terminal rest
      exact .inr ⟨by simpa [same.2] using (show trace = emitted ++ restTrace from rfl), same.1⟩

/-- Any terminating Core run of a loop with a false deterministic guard is
its immediate zero-iteration return. -/
theorem coreLoop_false_return (procedures : String → Option Core.Procedure)
    (guard : Core.Expression.Expr) (measure : Option Core.Expression.Expr)
    (invariants : List (String × Core.Expression.Expr)) (body : List Core.Statement)
    (metadata : Imperative.MetaData Core.Expression) (state : State)
    (trace : Imperative.Trace Core.Expression) (final : Imperative.Env Core.Expression)
    (guardFalse : Core.Expression.eval coreRuntimeFactory (coreStore state) guard =
      some (Imperative.HasBool.ffVal coreRuntimeFactory))
    (run : Core.CoreStepStarE procedures
      (.stmt (.loop (.det guard) measure invariants body metadata) (coreEnv state)) trace
      (.terminal final)) : trace = [] ∧ final = coreEnv state := by
  rcases coreLoop_false_shape procedures guard measure invariants body metadata state trace
    (.terminal final) guardFalse run with ⟨empty, impossible⟩ | ⟨empty, same⟩
  · cases impossible
  · exact ⟨empty, Imperative.Config.terminal.inj same⟩

/-- Reverse simulation for normal loop returns. Each Core iteration first
runs the scoped body block and then recursively runs the same loop. The source
`Iteration.next` rule mirrors exactly that decomposition. -/
private theorem coreLoop_returnsT (procedures : String → Option Core.Procedure)
    (guard : Computation (model := .builtins) Bool)
    (bodyComputation : Computation (model := .builtins) Unit)
    (coreGuard : Imperative.ExprOrNondet Core.Expression) (measure : Option Core.Expression.Expr)
    (invariants : List (String × Core.Expression.Expr)) (body : List Core.Statement)
    (metadata : Imperative.MetaData Core.Expression) (valid : State → Prop)
    (guardAgreement : ∀ state, valid state → ∀ value,
      guard.run state (.returned value state) ↔
        coreGuardAllows coreGuard state value)
    (bodyReplay : ∀ state, valid state → ∀ trace final,
      Core.CoreStepStarE procedures
        (.block .none (coreStore state) (.stmts body (coreEnv state))) trace (.terminal final) →
      coreChecksPass trace →
      ∃ next, bodyComputation.run state (.returned () next) ∧
        final = coreEnv next ∧ valid next)
    (fuel : Nat)
    {state : State} {trace : Imperative.Trace Core.Expression}
    {final : Imperative.Env Core.Expression}
    (ready : valid state)
    (run : ReflTransTraceT (Imperative.StepStmtE Core.Expression
      (Imperative.EvalCmdExtE procedures))
      (.stmt (.loop coreGuard measure invariants body metadata) (coreEnv state)) trace
      (.terminal final))
    (runBound : run.len ≤ fuel)
    (passing : coreChecksPass trace) :
    ∃ result, Computation.Iteration guard bodyComputation state (.returned () result) ∧
      final = coreEnv result ∧ valid result := by
  let totalLen := run.len
  cases run with
  | step _ emitted _ restTrace _ first rest =>
    have totalLenEq : totalLen = rest.len + 1 := by simp [totalLen, ReflTransTraceT.len.eq_2]; omega
    have restBound : rest.len < fuel := by omega
    cases first with
    | step_loop_exit evalFalse =>
      have sourceFalse := (guardAgreement state ready false).2 evalFalse
      have done := Imperative.stepStmtStarE_from_terminal (reflTransTraceT_to_prop rest)
      exact ⟨state, .stop sourceFalse, Imperative.Config.terminal.inj done.1, ready⟩
    | step_loop_nondet_exit =>
      have sourceFalse := (guardAgreement state ready false).2 True.intro
      have done := Imperative.stepStmtStarE_from_terminal (reflTransTraceT_to_prop rest)
      exact ⟨state, .stop sourceFalse, Imperative.Config.terminal.inj done.1, ready⟩
    | step_loop_enter evalTrue | step_loop_nondet_enter =>
      have sourceTrue := (guardAgreement state ready true).2 (by first | exact evalTrue | exact True.intro)
      obtain ⟨middleEnv, bodyTrace, loopTrace, traceSplit, bodyRun, tailRun, splitLength⟩ :=
        Imperative.seqT_reaches_terminalE rest
      have passRest : coreChecksPass restTrace := by simpa using passing
      have passParts := (coreChecksPass_append _ _).mp (traceSplit ▸ passRest)
      obtain ⟨bodyState, bodySourceRun, bodyFinalEq, bodyValid⟩ :=
        bodyReplay state ready bodyTrace middleEnv
          (reflTransTraceT_to_prop bodyRun) passParts.1
      subst middleEnv
      obtain ⟨loopEnv, loopTrace', nilTrace, tailSplit, loopRun, nilRun, tailLength⟩ :=
        Imperative.stmtsT_cons_terminalE tailRun
      have nilInfo := Imperative.stmts_nil_runE _
        (reflTransTraceT_to_prop nilRun)
      have nilEmpty := nilInfo.1
      have loopFinalEq : final = loopEnv := by
        rcases nilInfo.2 with stuck | same
        · cases stuck
        · exact Imperative.Config.terminal.inj same
      have loopTraceEq : loopTrace = loopTrace' := by
        simpa [nilEmpty] using tailSplit
      obtain ⟨result, recursive, finalEq, resultValid⟩ :=
        coreLoop_returnsT procedures guard bodyComputation _ measure invariants body
          metadata valid guardAgreement bodyReplay rest.len bodyValid loopRun (by
            have loopBound : loopRun.len ≤ rest.len := by omega
            exact loopBound) (by
            simpa [← loopTraceEq] using passParts.2)
      exact ⟨result, .next sourceTrue bodySourceRun recursive, loopFinalEq.trans finalEq, resultValid⟩
termination_by fuel

decreasing_by
  all_goals first | assumption | omega

/-- A finite Core loop return, with every checked Core block iteration
replayed by the source body, yields a source loop return. -/
theorem coreLoop_return_replays (procedures : String → Option Core.Procedure)
    (guard : Computation (model := .builtins) Bool)
    (bodyComputation : Computation (model := .builtins) Unit)
    (coreGuard : Imperative.ExprOrNondet Core.Expression) (measure : Option Core.Expression.Expr)
    (invariants : List (String × Core.Expression.Expr)) (body : List Core.Statement)
    (metadata : Imperative.MetaData Core.Expression) (valid : State → Prop)
    (guardAgreement : ∀ state, valid state → ∀ value,
      guard.run state (.returned value state) ↔
        coreGuardAllows coreGuard state value)
    (bodyReplay : ∀ state, valid state → ∀ trace final,
      Core.CoreStepStarE procedures
        (.block .none (coreStore state) (.stmts body (coreEnv state))) trace (.terminal final) →
      coreChecksPass trace →
      ∃ next, bodyComputation.run state (.returned () next) ∧
        final = coreEnv next ∧ valid next)
    {state : State} {trace : Imperative.Trace Core.Expression}
    {final : Imperative.Env Core.Expression}
    (ready : valid state)
    (run : Core.CoreStepStarE procedures
      (.stmt (.loop coreGuard measure invariants body metadata) (coreEnv state)) trace
      (.terminal final)) (passing : coreChecksPass trace) :
    ∃ result, (Computation.loop guard bodyComputation).run state (.returned () result) ∧
      final = coreEnv result ∧ valid result := by
  obtain ⟨traceT⟩ := reflTransTrace_nonempty_T run
  obtain ⟨result, iteration, same, resultValid⟩ :=
    coreLoop_returnsT procedures guard bodyComputation coreGuard measure invariants body metadata
      valid guardAgreement bodyReplay traceT.len ready traceT (Nat.le_refl _) passing
  exact ⟨result, iteration, same, resultValid⟩

/-- With a guard known false at every valid entry, the zero-iteration Core
loop replays as the source loop's finite normal result. Body behavior is
irrelevant because the guard never admits an iteration. -/
theorem loop_false_coreReplay (procedures : String → Option Core.Procedure)
    (guard : Computation (model := .builtins) Bool)
    (bodyComputation : Computation (model := .builtins) Unit)
    (coreGuard : Core.Expression.Expr) (measure : Option Core.Expression.Expr)
    (invariants : List (String × Core.Expression.Expr)) (body : List Core.Statement)
    (metadata : Imperative.MetaData Core.Expression) (valid : State → Prop)
    (guardFalse : ∀ state, valid state →
      Core.Expression.eval coreRuntimeFactory (coreStore state) coreGuard =
        some (Imperative.HasBool.ffVal coreRuntimeFactory))
    (sourceGuardFalse : ∀ state, valid state → guard.run state (.returned false state)) :
    CoreReplay procedures
      (fun state => .stmt (.loop (.det coreGuard) measure invariants body metadata) (coreEnv state))
      (Computation.loop guard bodyComputation) valid valid := by
  constructor
  · intro initial final trace ready run passing
    have shape := coreLoop_false_return procedures coreGuard measure invariants body metadata
      initial trace final (guardFalse initial ready) run
    rcases shape with ⟨traceEmpty, finalEq⟩
    subst trace
    exact ⟨initial, Computation.Iteration.stop (sourceGuardFalse initial ready), finalEq, ready⟩
  · intro initial label final trace ready run passing
    rcases coreLoop_false_shape procedures coreGuard measure invariants body metadata
      initial trace (.exiting label final) (guardFalse initial ready) run with
      ⟨_, impossible⟩ | ⟨_, impossible⟩ <;> cases impossible
  · intro initial prior check reached ready run passing failed
    rcases coreLoop_false_shape procedures coreGuard measure invariants body metadata
      initial (prior ++ [.assert check]) reached (guardFalse initial ready) run with
      ⟨empty, _⟩ | ⟨empty, _⟩ <;> simp at empty

end Strata.Boole
