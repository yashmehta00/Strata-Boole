/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.Execution
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Bodies
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Statements
import all StrataBoole.Boole.Interpretation.Legacy.Semantics
import Strata.DL.Imperative.StmtSemanticsProps

public section
namespace Strata.Boole

/-- A branch or loop's anonymous scope replays a body execution and drops
the new locals, including when the body exits or hits an assertion. -/
theorem anonymousScope_replays {procedures : String → Option Core.Procedure}
    {statements : List Core.Statement} {body : Computation Unit}
    {valid innerValid returnValid : State → Prop}
    (replay : CoreReplay procedures (fun state => .stmts statements (coreEnv state))
      body valid innerValid)
    (projection : ∀ initial outcome, valid initial → body.run initial outcome →
      coreStore { outcome.state with locals := outcome.state.locals.restrict initial.locals } =
        Imperative.projectStore (coreStore initial) (coreStore outcome.state))
    (preserved : ∀ initial state, valid initial → body.run initial (.returned () state) →
      innerValid state → returnValid { state with locals := state.locals.restrict initial.locals }) :
    CoreReplay procedures
      (fun initial => .block none (coreStore initial) (.stmts statements (coreEnv initial)))
      (Computation.scope body) valid returnValid := by
  constructor
  · intro initial final trace ready ran passed
    rcases Imperative.block_run_to_finalE ran with
      ⟨_, impossible, _⟩ | ⟨inner, inside, same⟩ |
      ⟨_, _, impossible, _, _⟩ | ⟨_, _, _, _, impossible⟩
    · contradiction
    · obtain ⟨state, returned, rfl, validState⟩ := replay.returns _ _ _ ready inside passed
      let restricted := { state with locals := state.locals.restrict initial.locals }
      have projected : coreStore restricted =
          Imperative.projectStore (coreStore initial) (coreStore state) :=
        projection initial (.returned () state) ready returned
      exact ⟨restricted, ⟨.returned () state, returned, rfl⟩,
        by cases same; simp only [coreEnv, projected],
        preserved initial state ready returned validState⟩
    · contradiction
    · contradiction
  · intro initial label final trace ready ran passed
    rcases Imperative.block_run_to_finalE ran with
      ⟨_, impossible, _⟩ | ⟨_, _, impossible⟩ |
      ⟨_, _, _, _, impossible⟩ | ⟨_, inner, _, inside, same⟩
    · contradiction
    · contradiction
    · contradiction
    · obtain ⟨rfl, rfl⟩ := Imperative.Config.exiting.inj same
      obtain ⟨state, exited, rfl⟩ := replay.exits _ _ _ _ ready inside passed
      let restricted := { state with locals := state.locals.restrict initial.locals }
      have projected : coreStore restricted =
          Imperative.projectStore (coreStore initial) (coreStore state) :=
        projection initial (.exited label state) ready exited
      exact ⟨restricted, ⟨.exited label state, exited, rfl⟩, by simp only [coreEnv, projected]⟩
  · intro initial prior check reached ready ran passed failed
    have ⟨inside, traceRun⟩ : ∃ inside,
        Core.CoreStepStarE procedures (.stmts statements (coreEnv initial))
          (prior ++ [Imperative.Event.assert check]) inside := by
      rcases Imperative.block_run_to_finalE ran with
        ⟨inside, _, steps⟩ | ⟨_, steps, _⟩ |
        ⟨_, _, _, steps, _⟩ | ⟨_, _, _, steps, _⟩
      all_goals exact ⟨_, steps⟩
    obtain ⟨label, state, failure⟩ := replay.fails _ _ _ inside ready traceRun passed failed
    exact ⟨label, { state with locals := state.locals.restrict initial.locals },
      .assertionFailed label state, failure, rfl⟩

/-- The forward scope step projects the same slots as the reverse replay. -/
theorem anonymousScope_forward {procedures : String → Option Core.Procedure}
    {statements : List Core.Statement} {body : Computation Unit}
    {entryValid returnValid : State → Prop}
    (agreement : ExecutionAgreement procedures statements body entryValid returnValid)
    (projection : ∀ initial outcome, entryValid initial → body.run initial outcome →
      coreStore { outcome.state with locals := outcome.state.locals.restrict initial.locals } =
        Imperative.projectStore (coreStore initial) (coreStore outcome.state))
    (initial : State) (ready : entryValid initial) (outcome : Outcome Unit)
    (ran : (Computation.scope body).run initial outcome) :
    CoreForwardOutcome procedures
      (.block none (coreStore initial) (.stmts statements (coreEnv initial))) outcome := by
  obtain ⟨inner, ran, rfl⟩ := ran
  have forward := agreement.forward initial ready inner ran
  have projected := scope_forward procedures none initial statements inner forward
    (projection initial inner ready ran)
  cases inner <;> exact projected

end Strata.Boole
