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

/-- A conditional matches the chosen branch in both directions. Both
branches run with the scope projection of a Core anonymous block. -/
theorem branch_executionAgreement (procedures : String → Option Core.Procedure)
    (test : Computation (model := .builtins) Bool)
    (yes no : Computation (model := .builtins) Unit)
    (guard : Imperative.ExprOrNondet Core.Expression)
    (yesBody noBody : List Core.Statement) (md : Imperative.MetaData Core.Expression)
    (entryValid returnValid : State → Prop)
    (tests : ∀ state, entryValid state → ∀ outcome, test.run state outcome →
      (∃ result, outcome = .returned result state ∧ coreGuardAllows guard state result) ∨
      ∃ reason, outcome = .stuck reason state)
    (replayTest : ∀ state, entryValid state → ∀ result, coreGuardAllows guard state result →
      test.run state (.returned result state))
    (yesForward : ∀ initial, entryValid initial → ∀ outcome, yes.run initial outcome →
      CoreForwardOutcome procedures (.block none (coreStore initial) (.stmts yesBody (coreEnv initial))) outcome)
    (noForward : ∀ initial, entryValid initial → ∀ outcome, no.run initial outcome →
      CoreForwardOutcome procedures (.block none (coreStore initial) (.stmts noBody (coreEnv initial))) outcome)
    (yesValid : ∀ initial final, entryValid initial → yes.run initial (.returned () final) → returnValid final)
    (noValid : ∀ initial final, entryValid initial → no.run initial (.returned () final) → returnValid final)
    (yesReplay : CoreReplay procedures
      (fun initial => .block none (coreStore initial) (.stmts yesBody (coreEnv initial)))
      yes entryValid returnValid)
    (noReplay : CoreReplay procedures
      (fun initial => .block none (coreStore initial) (.stmts noBody (coreEnv initial)))
      no entryValid returnValid) :
    ExecutionAgreement procedures [.ite guard yesBody noBody md]
      (test >>= fun taken => if taken then yes else no) entryValid returnValid := by
  have splitRun (initial : State) (trace : Imperative.Trace Core.Expression)
      (reached : Core.CoreConfig)
      (ran : Core.CoreStepStarE procedures
        (.stmt (.ite guard yesBody noBody md) (coreEnv initial)) trace reached) :
      (trace = [] ∧ reached = .stmt (.ite guard yesBody noBody md) (coreEnv initial)) ∨
      (coreGuardAllows guard initial true ∧ Core.CoreStepStarE procedures
        (.block none (coreStore initial) (.stmts yesBody (coreEnv initial))) trace reached) ∨
      (coreGuardAllows guard initial false ∧ Core.CoreStepStarE procedures
        (.block none (coreStore initial) (.stmts noBody (coreEnv initial))) trace reached) := by
    cases ran with
    | refl => exact .inl ⟨rfl, rfl⟩
    | step _ _ _ _ _ first rest =>
      cases first with
      | step_ite_true allowed => exact .inr (.inl ⟨allowed, rest⟩)
      | step_ite_false allowed => exact .inr (.inr ⟨allowed, rest⟩)
      | step_ite_nondet_true => exact .inr (.inl ⟨trivial, rest⟩)
      | step_ite_nondet_false => exact .inr (.inr ⟨trivial, rest⟩)
  have branchRun {initial : State} (ready : entryValid initial) {outcome : Outcome Unit}
      (taken : Bool) (allowed : coreGuardAllows guard initial taken)
      (ran : (if taken then yes else no).run initial outcome) :
      (test >>= fun taken => if taken then yes else no).run initial outcome :=
    (Computation.run_bind _ _ _ _).2 (.inl ⟨taken, initial, replayTest _ ready _ allowed, ran⟩)
  constructor
  · intro initial ready outcome ran
    exact forward_singleton (branch_forward procedures test yes no guard yesBody noBody md
      (tests initial ready) (yesForward initial ready outcome) (noForward initial ready outcome) ran)
  · intro initial final ready ran
    rcases (Computation.run_bind _ _ _ _).1 ran with
      ⟨taken, middle, tested, branch⟩ | ⟨_, _, _, impossible⟩ |
      ⟨_, _, _, impossible⟩ | ⟨_, _, _, impossible⟩
    · rcases tests initial ready _ tested with ⟨result, same, _⟩ | ⟨_, impossible⟩
      · obtain ⟨rfl, rfl⟩ := Outcome.returned.inj same
        cases taken
        · exact noValid _ _ ready branch
        · exact yesValid _ _ ready branch
      · contradiction
    all_goals contradiction
  · constructor
    · intro initial final trace ready ran passed
      rcases splitRun _ _ _ (coreSingleton_terminal_inside ran) with
        ⟨_, impossible⟩ | ⟨allowed, inner⟩ | ⟨allowed, inner⟩
      · contradiction
      · obtain ⟨result, done, same, valid⟩ := yesReplay.returns _ _ _ ready inner passed
        exact ⟨result, branchRun ready true allowed done, same, valid⟩
      · obtain ⟨result, done, same, valid⟩ := noReplay.returns _ _ _ ready inner passed
        exact ⟨result, branchRun ready false allowed done, same, valid⟩
    · intro initial label final trace ready ran passed
      rcases splitRun _ _ _ (coreSingleton_exit_inside ran) with
        ⟨_, impossible⟩ | ⟨allowed, inner⟩ | ⟨allowed, inner⟩
      · contradiction
      · obtain ⟨result, exited, same⟩ := yesReplay.exits _ _ _ _ ready inner passed
        exact ⟨result, branchRun ready true allowed exited, same⟩
      · obtain ⟨result, exited, same⟩ := noReplay.exits _ _ _ _ ready inner passed
        exact ⟨result, branchRun ready false allowed exited, same⟩
    · intro initial prior check reached ready ran passed failed
      obtain ⟨inside, ranInside⟩ := coreSingleton_trace_inside ran
      rcases splitRun _ _ inside ranInside with
        ⟨impossible, _⟩ | ⟨allowed, inner⟩ | ⟨allowed, inner⟩
      · simp at impossible
      · obtain ⟨label, result, failure⟩ := yesReplay.fails _ _ _ _ ready inner passed failed
        exact ⟨label, result, branchRun ready true allowed failure⟩
      · obtain ⟨label, result, failure⟩ := noReplay.fails _ _ _ _ ready inner passed failed
        exact ⟨label, result, branchRun ready false allowed failure⟩

end Strata.Boole
