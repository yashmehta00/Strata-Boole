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

private theorem assumption_run_iff {state : State} {condition : Expression}
    {result : Bool} {outcome : Outcome Unit}
    (evaluated : condition state = .ok (.bool result)) :
    (Computation.assumption condition).run state outcome ↔
      result = true ∧ outcome = .returned () state := by
  cases result <;>
    simp [Computation.assumption, Computation.test, Computation.run_bind,
      Computation.evaluate, evaluated, Computation.pure, Value.bool, and_assoc]

/-- A Core assume event records the condition and leaves the environment
unchanged. There is no other step from this statement. -/
private theorem coreAssumption_trace (procedures : String → Option Core.Procedure)
    (state : State) (label : String) (condition : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (trace : Imperative.Trace Core.Expression) (reached : Core.CoreConfig)
    (run : Core.CoreStepStarE procedures
      (.stmt (.cmd (.cmd (.assume label condition md))) (coreEnv state)) trace reached) :
    (trace = [] ∧ reached = .stmt (.cmd (.cmd (.assume label condition md))) (coreEnv state)) ∨
    (trace = [.assume ⟨coreRuntimeFactory, coreStore state, label, condition, md⟩] ∧
      reached = .terminal (coreEnv state)) := by
  cases run with
  | refl => exact .inl ⟨rfl, rfl⟩
  | step _ _ _ _ _ first rest =>
    cases first with
    | step_cmd executed =>
      cases executed with
      | cmd_sem executed =>
        cases executed with
        | eval_assume =>
          obtain ⟨reachedEq, rfl⟩ := Imperative.stepStmtStarE_from_terminal rest
          exact .inr ⟨by simp [coreEnv], by simpa [coreEnv] using reachedEq⟩

/-- A Core assumption is equivalent to the source assumption whenever their
Boolean evaluations agree on states in the invariant. Both normal return and
the invariant are preserved; false assumptions have no execution outcome. -/
theorem assumption_executionAgreement (procedures : String → Option Core.Procedure)
    (valid : State → Prop) (targetLabel : String) (condition : Expression)
    (target : Core.Expression.Expr) (md : Imperative.MetaData Core.Expression)
    (booleanTotal : ∀ state, valid state → ∃ result, condition state = .ok (.bool result))
    (evaluationAgreement : ∀ state, valid state → ∀ result,
      condition state = .ok (.bool result) ↔
        Core.Expression.eval coreRuntimeFactory (coreStore state) target =
          some (if result then Imperative.HasBool.ttVal coreRuntimeFactory
            else Imperative.HasBool.ffVal coreRuntimeFactory)) :
    ExecutionAgreement procedures [.cmd (.cmd (.assume targetLabel target md))]
      (Computation.assumption condition) valid valid := by
  have replay : CoreReplay procedures
      (fun state => .stmt (.cmd (.cmd (.assume targetLabel target md))) (coreEnv state))
      (Computation.assumption condition) valid valid := by
    constructor
    · intro initial final trace ready run passing
      rcases coreAssumption_trace procedures initial targetLabel target md trace
        (.terminal final) run with ⟨empty, reached⟩ | ⟨traceEq, reached⟩
      · cases reached
      · have finalEq : final = coreEnv initial := by
          have same := Imperative.Config.terminal.inj reached
          simpa [coreEnv] using same
        have targetTrue : Core.Expression.eval coreRuntimeFactory (coreStore initial) target =
            some (Imperative.HasBool.ttVal coreRuntimeFactory) := by
          have eventPass := passing (.assume
            ⟨coreRuntimeFactory, coreStore initial, targetLabel, target, md⟩) (by simp [traceEq])
          simpa using eventPass
        have sourceTrue := (evaluationAgreement initial ready true).2 targetTrue
        exact ⟨initial, assumption_replays_true condition initial sourceTrue, finalEq, ready⟩
    · intro initial label final trace ready run _
      rcases coreAssumption_trace procedures initial targetLabel target md trace
        (.exiting label final) run with ⟨_, reached⟩ | ⟨_, reached⟩
      · cases reached
      · cases reached
    · intro initial prior check reached ready run _ _
      rcases coreAssumption_trace procedures initial targetLabel target md
        (prior ++ [.assert check]) reached run with ⟨empty, _⟩ | ⟨traceEq, _⟩
      · simp at empty
      · have appendEq : prior ++ [.assert check] = [] ++
          [.assume ⟨coreRuntimeFactory, coreStore initial, targetLabel, target, md⟩] := by
            simpa using traceEq
        obtain ⟨priorEmpty, differentEvents⟩ := List.append_singleton_inj.mp appendEq
        cases differentEvents

  have singletonReplay : CoreReplay procedures
      (fun state => .stmts [.cmd (.cmd (.assume targetLabel target md))] (coreEnv state))
      (Computation.assumption condition) valid valid := {
    returns := fun initial final trace ready ran passing =>
      replay.returns initial final trace ready (coreSingleton_terminal_inside ran) passing
    exits := fun initial label final trace ready ran passing =>
      replay.exits initial label final trace ready (coreSingleton_exit_inside ran) passing
    fails := fun initial prior check reached ready ran passing failed => by
      obtain ⟨inner, inside⟩ := coreSingleton_trace_inside ran
      exact replay.fails initial prior check inner ready inside passing failed
  }

  refine ⟨?_, ?_, singletonReplay⟩
  · intro initial ready outcome ran
    obtain ⟨result, sourceEval⟩ := booleanTotal initial ready
    have targetEval := (evaluationAgreement initial ready result).1 sourceEval
    have forward := assumption_forward procedures initial condition target targetLabel md
      result outcome sourceEval targetEval ran
    exact forward_singleton forward
  · intro initial final ready ran
    obtain ⟨result, sourceEval⟩ := booleanTotal initial ready
    have shape := (assumption_run_iff sourceEval).mp ran
    exact (Outcome.returned.inj shape.2).2.symm ▸ ready

end Strata.Boole
