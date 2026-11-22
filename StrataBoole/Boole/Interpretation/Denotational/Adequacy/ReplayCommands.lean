/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.Statements
public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.Bodies
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Statements
import all StrataBoole.Boole.Interpretation.Legacy.Semantics
import all StrataBoole.Boole.Interpretation.Legacy.Runtime
import all StrataBoole.Boole.Interpretation.Runtime
import all StrataBoole.Boole.Interpretation.Denotational.CoreReference
import all Strata.DL.Imperative.CmdSemanticsProps
import Strata.DL.Imperative.StmtSemanticsProps

public section

namespace Strata.Boole

/-- A passing Core assumption has the same successful source outcome whenever
the source condition evaluates to true. The expression correspondence proof
supplies the shared Boolean value. -/
theorem assumption_replays_true (condition : Expression) (state : State)
    (sourceEval : condition state = .ok (.bool true)) :
    (Computation.assumption condition).run state (.returned () state) := by
  have testRun : (Computation.test (some condition)).run state (.returned true state) := by
    unfold Computation.test
    apply (Computation.run_bind _ _ _ _).mpr
    left
    refine ⟨.bool true, state, ?_, ?_⟩
    · simp [Computation.evaluate, sourceEval]
    · exact Computation.run_pure true state (.returned true state) |>.2 rfl
  unfold Computation.assumption
  apply (Computation.run_bind _ _ _ _).mpr
  left
  exact ⟨true, state, testRun, by simp⟩

/-- A false Core assertion corresponds to the source assertion-failure outcome
at that state, once both evaluators agree on the condition. -/
theorem assertion_replays_false (label : String) (condition : Expression) (state : State)
    (sourceEval : condition state = .ok (.bool false)) :
    (Computation.assertion label condition).run state (.assertionFailed label state) := by
  have testRun : (Computation.test (some condition)).run state (.returned false state) := by
    unfold Computation.test
    apply (Computation.run_bind _ _ _ _).mpr
    left
    refine ⟨.bool false, state, ?_, ?_⟩
    · simp [Computation.evaluate, sourceEval]
    · exact Computation.run_pure false state (.returned false state) |>.2 rfl
  unfold Computation.assertion
  apply (Computation.run_bind _ _ _ _).mpr
  left
  exact ⟨false, state, testRun, by simp⟩

/-- The only event a single Core assertion can emit is its captured check.
Executing the assertion itself leaves the environment unchanged. -/
private theorem coreAssertion_trace (procedures : String → Option Core.Procedure)
    (state : State) (label : String) (condition : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression)
    (trace : Imperative.Trace Core.Expression) (reached : Core.CoreConfig)
    (run : Core.CoreStepStarE procedures
      (.stmt (.cmd (.cmd (.assert label condition md))) (coreEnv state)) trace reached) :
    (trace = [] ∧ reached = .stmt (.cmd (.cmd (.assert label condition md))) (coreEnv state)) ∨
    (trace = [.assert ⟨coreRuntimeFactory, coreStore state, label, condition, md⟩] ∧
      reached = .terminal (coreEnv state)) := by
  cases run with
  | refl => exact .inl ⟨rfl, rfl⟩
  | step _ _ _ _ _ first rest =>
    cases first with
    | step_cmd executed =>
      cases executed with
      | cmd_sem executed =>
        cases executed with
        | eval_assert =>
          obtain ⟨reachedEq, rfl⟩ := Imperative.stepStmtStarE_from_terminal rest
          exact .inr ⟨by simp [coreEnv], by simpa [coreEnv] using reachedEq⟩

/-- An assertion failure on the Core side replays at the same Boole state
when the source and Core conditions denote the same Boolean. -/
theorem coreAssertion_failure_replays (procedures : String → Option Core.Procedure)
    (state : State) (sourceLabel targetLabel : String) (condition : Expression)
    (target : Core.Expression.Expr) (md : Imperative.MetaData Core.Expression) (value : Bool)
    (sourceEval : condition state = .ok (.bool value))
    (targetEval : Core.Expression.eval coreRuntimeFactory (coreStore state) target =
      some (if value then Imperative.HasBool.ttVal coreRuntimeFactory
        else Imperative.HasBool.ffVal coreRuntimeFactory))
    (prior : Imperative.Trace Core.Expression) (check : Imperative.EventArg Core.Expression)
    (reached : Core.CoreConfig)
    (run : Core.CoreStepStarE procedures
      (.stmt (.cmd (.cmd (.assert targetLabel target md))) (coreEnv state))
      (prior ++ [.assert check]) reached)
    (failed : Core.Expression.eval check.factory check.store check.expr =
      some (Imperative.HasBool.ffVal check.factory)) :
    (Computation.assertion sourceLabel condition).run state (.assertionFailed sourceLabel state) := by
  rcases coreAssertion_trace procedures state targetLabel target md _ _ run with ⟨empty, _⟩ | ⟨traceEq, _⟩
  · simp at empty
  · have sameCheck := Imperative.Event.assert.inj (List.append_singleton_inj.mp
      (show prior ++ [.assert check] = [] ++ [.assert ⟨coreRuntimeFactory, coreStore state, targetLabel, target, md⟩]
        from traceEq)).2
    subst check
    change Core.Expression.eval coreRuntimeFactory (coreStore state) target =
      some (Imperative.HasBool.ffVal coreRuntimeFactory) at failed
    cases value with
    | false => exact assertion_replays_false sourceLabel condition state sourceEval
    | true =>
      have equal := Option.some.inj (targetEval.symm.trans failed)
      exact False.elim (Imperative.HasBool.ttVal_ne_ffVal coreRuntimeFactory equal)

/-- Replay a Core assertion in Boole when their Boolean evaluations agree on
valid entry states. A true assertion returns unchanged, a false assertion
fails, and an assertion cannot exit. -/
theorem assertion_coreReplay (procedures : String → Option Core.Procedure)
    (valid : State → Prop) (sourceLabel targetLabel : String) (condition : Expression)
    (target : Core.Expression.Expr) (md : Imperative.MetaData Core.Expression)
    (evaluationAgreement : ∀ state, valid state → ∀ result,
      (condition state = .ok (.bool result)) ↔
        Core.Expression.eval coreRuntimeFactory (coreStore state) target =
          some (if result then Imperative.HasBool.ttVal coreRuntimeFactory
            else Imperative.HasBool.ffVal coreRuntimeFactory)) :
    CoreReplay procedures
      (fun state => .stmt (.cmd (.cmd (.assert targetLabel target md))) (coreEnv state))
      (Computation.assertion sourceLabel condition) valid valid := by
  constructor
  · intro initial final trace ready run passing
    rcases coreAssertion_trace procedures initial targetLabel target md trace
        (.terminal final) run with ⟨empty, reached⟩ | ⟨traceEq, reached⟩
    · cases reached
    ·
      have finalEq : final = coreEnv initial := by
        have := Imperative.Config.terminal.inj reached
        simpa [coreEnv] using this
      have coreTrue : Core.Expression.eval coreRuntimeFactory (coreStore initial) target =
          some (Imperative.HasBool.ttVal coreRuntimeFactory) := by
        have eventPass := passing (.assert
          ⟨coreRuntimeFactory, coreStore initial, targetLabel, target, md⟩) (by simp [traceEq])
        simpa using eventPass
      have sourceTrue := (evaluationAgreement initial ready true).2 coreTrue
      have sourceRun : (Computation.assertion sourceLabel condition).run initial
          (.returned () initial) :=
        (assertion_run_iff (state := initial) (label := sourceLabel)
          (condition := condition) (result := true) (outcome := .returned () initial)
          sourceTrue).2 rfl
      exact ⟨initial, sourceRun, finalEq, ready⟩
  · intro initial label final trace ready run passing
    rcases coreAssertion_trace procedures initial targetLabel target md trace
        (.exiting label final) run with ⟨_, reached⟩ | ⟨_, reached⟩
    · cases reached
    · cases reached
  · intro initial prior check reached ready run passing failed
    rcases coreAssertion_trace procedures initial targetLabel target md
        (prior ++ [.assert check]) reached run with ⟨traceEq, _⟩ | ⟨traceEq, _⟩
    · simp at traceEq
    · have appendEq : prior ++ [.assert check] = [] ++
          [.assert ⟨coreRuntimeFactory, coreStore initial, targetLabel, target, md⟩] := by
        simpa using traceEq
      have sameEvent := List.append_singleton_inj.mp appendEq
      have priorEmpty : prior = [] := sameEvent.1
      have checkEq := Imperative.Event.assert.inj sameEvent.2
      subst prior
      subst check
      have sourceFalse := (evaluationAgreement initial ready false).2 failed
      exact ⟨sourceLabel, initial, assertion_replays_false sourceLabel condition initial sourceFalse⟩

private theorem initialSlot_absent {P : Imperative.PureExpr}
    {store final : Imperative.SemanticStore P} {id : P.Ident} {value : P.Val}
    (run : Imperative.InitState P store id value final) : store id = none :=
  match run with
  | .init missing _ _ => missing

/-- Reify Core's arbitrary typed choice for a fresh local as a Boole value.
The anchor value represents the declared source sort, and the two Core typing
witnesses show that Core chose a value of that same sort. -/
theorem init_nondet_replays_choice (state : State) (binding : Binding)
    (ty : Lambda.LTy) (anchor : Value) (anchorRuntime chosen : Core.Expression.Val)
    (final : Core.CoreStore)
    (init : Imperative.InitState (P := Core.Expression) (coreStore state)
      ⟨binding.name, ()⟩ chosen final)
    (chosenTyped : Imperative.HasVal.valueOfTy
      (P := Core.Expression) coreRuntimeFactory chosen ty)
    (nameFresh : state.locals.lookup binding.name = none)
    (anchorSort : anchor.sort = binding.sort)
    (anchorRep : coreValue? anchor = some anchorRuntime)
    (anchorTyped : Imperative.HasVal.valueOfTy
      (P := Core.Expression) coreRuntimeFactory anchorRuntime ty) :
    ∃ value,
      coreValue? value = some chosen ∧
      value.sort = binding.sort ∧
      (Computation.declare binding none).run state
        (.returned () { state with locals := state.locals ++ [(binding.name, value)] }) ∧
      final = coreStore { state with locals := state.locals ++ [(binding.name, value)] } := by
  have absent := initialSlot_absent init
  obtain ⟨value, valueSort, representation⟩ :=
    coreTypedChoice_reifies anchorRep chosen chosenTyped.1
      (Option.some.inj (chosenTyped.2.symm.trans anchorTyped.2))
  have sourceType : value.sort = binding.sort := valueSort.trans anchorSort
  exact ⟨value, representation, sourceType,
    declare_runs_with_value state binding value none nameFresh sourceType ⟨value, sourceType, rfl⟩,
    Imperative.InitStateUniqueResult init (coreInit_local state binding.name value absent nameFresh representation)⟩


end Strata.Boole
