/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.Statements
import all StrataBoole.Boole.Semantics.Adequacy.Statements
import all StrataBoole.Boole.Semantics.Adequacy.Lowering
import all StrataBoole.Boole.Semantics.Adequacy.SourceState
import all StrataBoole.Boole.Semantics.Adequacy.Entry
import all StrataBoole.Boole.Semantics.CoreReference
import all StrataBoole.Boole.Semantics.Semantics
import all StrataBoole.Boole.Interp
import all StrataBoole.Boole.Runtime
import StrataBoole.Boole.Semantics.Adequacy.CheckedExits
import StrataBoole.Boole.Semantics.Adequacy.BodyAlignment
import StrataBoole.Boole.Semantics.Adequacy.SourceFreshness
import Strata.DL.Imperative.StmtSemanticsProps
import Strata.Languages.Core.StatementSemanticsProps
import Strata.Util.RelationsProps

public section

/-! ## Executing a matched procedure body -/

namespace Strata.Boole

private theorem Store.lookup_isSome_iff (store : Store) (name : String) :
    (store.lookup name).isSome ↔ name ∈ store.map Prod.fst := by
  induction store with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨key, value⟩ := head
    by_cases same : key = name
    · simp [Store.lookup_cons, same]
    · simp [Store.lookup_cons, same, Ne.symm same, ih]

private theorem Store.restrict_self (store : Store) : store.restrict store = store :=
  List.filter_eq_self.mpr fun _ present =>
    (Store.lookup_isSome_iff _ _).mpr (List.mem_map_of_mem present)

private theorem emptyBlock_run (range annotation : SourceRange) (entry final : Scope)
    (body : Computation (model := .builtins) Unit) (state : State) (outcome : Outcome Unit)
    (interpreted : interpBlock (denotation .builtins) (.block range ⟨annotation, #[]⟩) entry =
      .ok (body, final)) : body.run state outcome ↔ outcome = .returned () state := by
  rw [interpBlock] at interpreted
  obtain ⟨_, inner⟩ := withScope_success interpreted
  simp only [interpStmts, denotation, bind, StateT.bind, Except.bind, pure, StateT.pure,
    Except.pure] at inner
  have bodyEq : _ = body := congrArg Prod.fst (Except.ok.inj inner)
  rw [← bodyEq]
  change (Computation.scope (Computation.pure ())).run state outcome ↔ _
  simp [Computation.scope, Computation.pure, Outcome.mapState, Store.restrict_self]

/-- A passing Core trace can be replayed as a Boole return or exit with
the same final store. A trace ending at a false assertion replays as a Boole
assertion failure. -/
structure CoreReplay (procedures : String → Option Core.Procedure)
    (start : State → Core.CoreConfig) (body : Computation (model := .builtins) Unit)
    (entryValid returnValid : State → Prop) : Prop where
  returns : ∀ initial final trace,
    entryValid initial →
    Core.CoreStepStarE procedures (start initial) trace (.terminal final) →
    coreChecksPass trace →
    ∃ state, body.run initial (.returned () state) ∧ final = coreEnv state ∧ returnValid state
  exits : ∀ initial label final trace,
    entryValid initial →
    Core.CoreStepStarE procedures (start initial) trace (.exiting label final) →
    coreChecksPass trace →
    ∃ state, body.run initial (.exited label state) ∧ final = coreEnv state
  fails : ∀ initial prior check reached,
    entryValid initial →
    Core.CoreStepStarE procedures (start initial) (prior ++ [.assert check]) reached →
    coreChecksPass prior →
    Core.Expression.eval check.factory check.store check.expr =
      some (Imperative.HasBool.ffVal check.factory) →
    ∃ label state, body.run initial (.assertionFailed label state)

/-- An empty statement list returns its input state without any events. -/
theorem nil_replays (procedures : String → Option Core.Procedure) (valid : State → Prop) :
    CoreReplay procedures (fun state => .stmts [] (coreEnv state))
      (Computation.pure ()) valid valid := by
  constructor
  · intro initial final trace ready run _
    rcases (Imperative.stmts_nil_runE _ run).2 with impossible | same
    · contradiction
    · exact ⟨initial, rfl, Imperative.Config.terminal.inj same, ready⟩
  · intro initial label final trace _ run _
    rcases (Imperative.stmts_nil_runE _ run).2 with impossible | impossible <;> contradiction
  · intro initial prior check reached _ run _ _
    have empty := (Imperative.stmts_nil_runE _ run).1
    simp at empty

/-- A traced run of a nonempty statement list splits at the end of its first
statement. The run can also stop inside the first statement or exit from it. -/
theorem sequence_replays {procedures : String → Option Core.Procedure}
    {statement : Core.Statement} {rest : List Core.Statement}
    {first tail : Computation (model := .builtins) Unit}
    {entryValid middleValid returnValid : State → Prop}
    (headReplay : CoreReplay procedures (fun state => .stmt statement (coreEnv state)) first entryValid middleValid)
    (tailReplay : CoreReplay procedures (fun state => .stmts rest (coreEnv state)) tail middleValid returnValid) :
    CoreReplay procedures (fun state => .stmts (statement :: rest) (coreEnv state))
      (first >>= fun _ => tail) entryValid returnValid := by
  constructor
  · intro initial final trace valid run passing
    rcases Imperative.stmts_cons_headE _ run with ⟨impossible, _⟩ | stepped
    · contradiction
    rcases Imperative.seq_run_decomposeE _ stepped with
      ⟨_, impossible, _⟩ | ⟨_, _, _, rfl, headRun, tailRun⟩ | ⟨_, _, impossible, _⟩
    · contradiction
    · obtain ⟨headPass, tailPass⟩ := (coreChecksPass_append _ _).mp passing
      obtain ⟨middle, firstRan, rfl, middleValid⟩ := headReplay.returns _ _ _ valid headRun headPass
      obtain ⟨state, tailRan, rfl, returnValid⟩ := tailReplay.returns _ _ _ middleValid tailRun tailPass
      exact ⟨state, (Computation.run_bind _ _ _ _).mpr (.inl ⟨(), middle, firstRan, tailRan⟩), rfl, returnValid⟩
    · contradiction
  · intro initial label final trace valid run passing
    rcases Imperative.stmts_cons_headE _ run with ⟨impossible, _⟩ | stepped
    · contradiction
    rcases Imperative.seq_run_decomposeE _ stepped with
      ⟨_, impossible, _⟩ | ⟨_, _, _, rfl, headRun, tailRun⟩ | ⟨_, _, same, headRun⟩
    · contradiction
    · obtain ⟨headPass, tailPass⟩ := (coreChecksPass_append _ _).mp passing
      obtain ⟨middle, firstRan, rfl, middleValid⟩ := headReplay.returns _ _ _ valid headRun headPass
      obtain ⟨state, tailRan, rfl⟩ := tailReplay.exits _ _ _ _ middleValid tailRun tailPass
      exact ⟨state, (Computation.run_bind _ _ _ _).mpr (.inl ⟨(), middle, firstRan, tailRan⟩), rfl⟩
    · cases same
      obtain ⟨state, firstRan, rfl⟩ := headReplay.exits _ _ _ _ valid headRun passing
      exact ⟨state, (Computation.run_bind _ _ _ _).mpr (.inr (.inl ⟨_, state, firstRan, rfl⟩)), rfl⟩
  · intro initial prior check reached valid run passing failed
    have liftFailure : ∀ headReached,
        Core.CoreStepStarE procedures (.stmt statement (coreEnv initial))
          (prior ++ [.assert check]) headReached →
        ∃ label state, (first >>= fun _ => tail).run initial (.assertionFailed label state) := by
      intro headReached headRun
      obtain ⟨label, state, firstRan⟩ := headReplay.fails _ _ _ _ valid headRun passing failed
      exact ⟨label, state, (Computation.run_bind _ _ _ _).mpr
        (.inr (.inr (.inl ⟨label, state, firstRan, rfl⟩)))⟩
    rcases Imperative.stmts_cons_headE _ run with ⟨_, impossible⟩ | stepped
    · simp at impossible
    rcases Imperative.seq_run_decomposeE _ stepped with
      ⟨_, _, headRun⟩ | ⟨middle, headTrace, tailTrace, splitTrace, headRun, tailRun⟩ |
      ⟨_, _, _, headRun⟩
    · exact liftFailure _ headRun
    · cases suffix : tailTrace.reverse with
      | nil =>
        have empty : tailTrace = [] := List.reverse_eq_nil_iff.mp suffix
        subst tailTrace
        rw [List.append_nil] at splitTrace
        rw [← splitTrace] at headRun
        exact liftFailure _ headRun
      | cons event tailPrior =>
        have tailSplit : tailTrace = tailPrior.reverse ++ [event] := by
          simpa only [List.reverse_reverse, List.reverse_cons] using congrArg List.reverse suffix
        rw [tailSplit, ← List.append_assoc] at splitTrace
        obtain ⟨prefixSplit, sameEvent⟩ := List.append_singleton_inj.mp splitTrace
        subst event
        rw [prefixSplit] at passing
        obtain ⟨headPass, tailPass⟩ := (coreChecksPass_append _ _).mp passing
        obtain ⟨state, firstRan, rfl, middleValid⟩ := headReplay.returns _ _ _ valid headRun headPass
        rw [tailSplit] at tailRun
        obtain ⟨label, final, tailRan⟩ := tailReplay.fails _ _ _ _ middleValid tailRun tailPass failed
        exact ⟨label, final, (Computation.run_bind _ _ _ _).mpr (.inl ⟨(), state, firstRan, tailRan⟩)⟩
    · exact liftFailure _ headRun

/-- The wrapper's entry and exit steps do not emit events. In particular, a
trace ending in a false assertion can be replayed inside the labeled block. -/
private theorem coreBlock_trace_inside {procedures : String → Option Core.Procedure}
    {name : String} {statements : List Core.Statement} {md : Imperative.MetaData Core.Expression}
    {entry : Imperative.Env Core.Expression} {trace : Imperative.Trace Core.Expression}
    {reached : Core.CoreConfig}
    (run : Core.CoreStepStarE procedures (.stmt (.block name statements md) entry) trace reached) :
    ∃ inside, Core.CoreStepStarE procedures (.stmts statements entry) trace inside := by
  cases run with
  | refl => exact ⟨_, .refl _⟩
  | step _ _ _ _ _ first rest =>
    cases first with
    | step_block =>
      rcases Imperative.block_run_to_finalE rest with
        ⟨inside, _, steps⟩ | ⟨_, steps, _⟩ | ⟨_, _, _, steps, _⟩ | ⟨_, _, _, steps, _⟩
      all_goals exact ⟨_, by simpa only [List.nil_append] using steps⟩

/-- A singleton statement list and its statement have the same nonempty
traces. The list's administrative steps can only add a silent suffix. -/
private theorem coreSingleton_trace_inside {procedures : String → Option Core.Procedure}
    {statement : Core.Statement} {entry : Imperative.Env Core.Expression}
    {trace : Imperative.Trace Core.Expression} {reached : Core.CoreConfig}
    (run : Core.CoreStepStarE procedures (.stmts [statement] entry) trace reached) :
    ∃ inside, Core.CoreStepStarE procedures (.stmt statement entry) trace inside := by
  rcases Imperative.stmts_cons_headE _ run with ⟨_, rfl⟩ | stepped
  · exact ⟨_, .refl _⟩
  rcases Imperative.seq_run_decomposeE _ stepped with
    ⟨_, _, inside⟩ | ⟨_, _, _, rfl, inside, suffix⟩ | ⟨_, _, _, inside⟩
  · exact ⟨_, inside⟩
  · obtain ⟨rfl, _⟩ := Imperative.stmts_nil_runE _ suffix
    exact ⟨_, by simpa only [List.append_nil] using inside⟩
  · exact ⟨_, inside⟩

/-- Strip the block's wrapper and recover the exit label, if its body
returned by exiting the block. The store is projected in either case. -/
private theorem coreBlock_terminal_inside {procedures : String → Option Core.Procedure}
    {name : String} {statements : List Core.Statement} {md : Imperative.MetaData Core.Expression}
    {entry final : Imperative.Env Core.Expression} {trace : Imperative.Trace Core.Expression}
    (run : Core.CoreStepStarE procedures (.stmt (.block name statements md) entry) trace (.terminal final)) :
    ∃ inner,
      (Core.CoreStepStarE procedures (.stmts statements entry) trace (.terminal inner) ∨
        Core.CoreStepStarE procedures (.stmts statements entry) trace (.exiting name inner)) ∧
      final = { inner with store := Imperative.projectStore entry.store inner.store } := by
  cases run with
  | step _ _ _ _ _ first rest =>
    cases first with
    | step_block =>
      rcases Imperative.block_run_to_finalE rest with
        ⟨_, impossible, _⟩ | ⟨_, steps, same⟩ |
        ⟨label, _, caught, steps, same⟩ | ⟨_, _, _, _, impossible⟩
      · contradiction
      · exact ⟨_, .inl (by simpa only [List.nil_append] using steps),
          Imperative.Config.terminal.inj same⟩
      · cases caught
        exact ⟨_, .inr (by simpa only [List.nil_append] using steps),
          Imperative.Config.terminal.inj same⟩
      · contradiction

/-- Finishing a singleton list normally requires the statement itself to
finish normally, with the same environment and trace. -/
private theorem coreSingleton_terminal_inside {procedures : String → Option Core.Procedure}
    {statement : Core.Statement} {entry final : Imperative.Env Core.Expression}
    {trace : Imperative.Trace Core.Expression}
    (run : Core.CoreStepStarE procedures (.stmts [statement] entry) trace (.terminal final)) :
    Core.CoreStepStarE procedures (.stmt statement entry) trace (.terminal final) := by
  rcases Imperative.stmts_cons_headE _ run with ⟨impossible, _⟩ | stepped
  · contradiction
  rcases Imperative.seq_run_decomposeE _ stepped with
    ⟨_, impossible, _⟩ | ⟨_, _, _, rfl, inside, suffix⟩ | ⟨_, _, impossible, _⟩
  · contradiction
  · obtain ⟨rfl, impossible | same⟩ := Imperative.stmts_nil_runE _ suffix
    · contradiction
    · obtain rfl := Imperative.Config.terminal.inj same
      simpa only [List.append_nil] using inside
  · contradiction

/-- A named Core block scopes the store and catches its own exit. The body
replay accounts for the emitted events, including a failing assertion. -/
private theorem namedBlock_replays {procedures : String → Option Core.Procedure}
    (name : String) (statements : List Core.Statement)
    (body : Computation (model := .builtins) Unit) (valid : State → Prop)
    (replay : CoreReplay procedures (fun state => .stmts statements (coreEnv state)) body
      valid (fun _ => True))
    (projection : ∀ initial outcome, valid initial → body.run initial outcome →
      coreStore { outcome.state with locals := outcome.state.locals.restrict initial.locals } =
        Imperative.projectStore (coreStore initial) (coreStore outcome.state)) :
    CoreReplay procedures (fun state => .stmt (.block name statements .empty) (coreEnv state))
      (Computation.block name (Computation.scope body)) valid (fun _ => True) := by
  constructor
  · intro initial final trace ready run passing
    obtain ⟨inner, done | exited, projected⟩ := coreBlock_terminal_inside run
    · obtain ⟨state, ran, rfl, _⟩ := replay.returns _ _ _ ready done passing
      let restricted := { state with locals := state.locals.restrict initial.locals }
      have same : coreStore restricted = Imperative.projectStore (coreStore initial) (coreStore state) :=
        projection initial _ ready ran
      exact ⟨restricted, ⟨.returned () restricted, ⟨.returned () state, ran, rfl⟩, rfl⟩,
        by simpa only [coreEnv, same] using projected, trivial⟩
    · obtain ⟨state, ran, rfl⟩ := replay.exits _ _ _ _ ready exited passing
      let restricted := { state with locals := state.locals.restrict initial.locals }
      have same : coreStore restricted = Imperative.projectStore (coreStore initial) (coreStore state) :=
        projection initial _ ready ran
      exact ⟨restricted, ⟨.exited name restricted, ⟨.exited name state, ran, rfl⟩, by simp⟩,
        by simpa only [coreEnv, same] using projected, trivial⟩
  · intro initial label final trace ready run passing
    cases run with
    | step _ _ _ _ _ first rest =>
      cases first with
      | step_block =>
        rcases Imperative.block_run_to_finalE rest with
          ⟨_, impossible, _⟩ | ⟨_, _, impossible⟩ |
          ⟨_, _, _, _, impossible⟩ | ⟨_, inner, different, steps, eq⟩
        · contradiction
        · contradiction
        · contradiction
        · obtain ⟨rfl, rfl⟩ := Imperative.Config.exiting.inj eq
          rw [List.nil_append] at passing
          obtain ⟨state, ran, rfl⟩ := replay.exits _ _ _ _ ready steps passing
          let restricted := { state with locals := state.locals.restrict initial.locals }
          have mismatch : label ≠ name := fun same => different (congrArg some same.symm)
          have same : coreStore restricted = Imperative.projectStore (coreStore initial) (coreStore state) :=
            projection initial _ ready ran
          exact ⟨restricted, ⟨.exited label restricted, ⟨.exited label state, ran, rfl⟩, by simp [mismatch]⟩,
            by simp only [coreEnv, same]⟩
  · intro initial prior check reached ready run passing failed
    obtain ⟨inner, steps⟩ := coreBlock_trace_inside run
    obtain ⟨label, state, ran⟩ := replay.fails _ _ _ _ ready steps passing failed
    let restricted := { state with locals := state.locals.restrict initial.locals }
    exact ⟨label, restricted, .assertionFailed label restricted,
      ⟨.assertionFailed label state, ran, rfl⟩, rfl⟩

private theorem coreSingleton_exit_inside {procedures : String → Option Core.Procedure}
    {statement : Core.Statement} {entry final : Imperative.Env Core.Expression}
    {label : String} {trace : Imperative.Trace Core.Expression}
    (run : Core.CoreStepStarE procedures (.stmts [statement] entry) trace (.exiting label final)) :
    Core.CoreStepStarE procedures (.stmt statement entry) trace (.exiting label final) := by
  rcases Imperative.stmts_cons_headE _ run with ⟨impossible, _⟩ | stepped
  · contradiction
  rcases Imperative.seq_run_decomposeE _ stepped with
    ⟨_, impossible, _⟩ | ⟨_, _, _, _, _, suffix⟩ | ⟨_, _, same, inside⟩
  · contradiction
  · rcases (Imperative.stmts_nil_runE _ suffix).2 with impossible | impossible <;> contradiction
  · cases same
    exact inside

/-- Once the inner block has projected its store, the procedure's additional
operational wrapper projects through the same entry store and leaves it unchanged. -/
private theorem coreBlock_projection_id {procedures : String → Option Core.Procedure}
    {name : String} {body : List Core.Statement} {md : Imperative.MetaData Core.Expression}
    {entry final : Imperative.Env Core.Expression} {trace : Imperative.Trace Core.Expression}
    (run : Core.CoreStepStarE procedures (.stmt (.block name body md) entry) trace (.terminal final) ∨
      ∃ label, Core.CoreStepStarE procedures (.stmt (.block name body md) entry) trace
        (.exiting label final)) :
    Imperative.projectStore entry.store final.store = final.store := by
  obtain ⟨inner, _, finalEq⟩ := Imperative.stmt_block_reaches_doneE run
  rw [finalEq]
  funext id
  by_cases present : (entry.store id).isSome <;> simp [Imperative.projectStore, present]

/-- Recover the checked procedure's inner run and the same final environment
from Core's outer block wrapper. An exit caught by that wrapper is explicit. -/
private theorem coreProcedureWrapper_terminal_inside {procedures : String → Option Core.Procedure}
    {name : String} {body : List Core.Statement}
    {entry final : Imperative.Env Core.Expression} {trace : Imperative.Trace Core.Expression}
    (run : Core.CoreStepStarE procedures
      (.stmt (.block "" [.block name body .empty] .empty) entry) trace (.terminal final)) :
    Core.CoreStepStarE procedures (.stmt (.block name body .empty) entry) trace (.terminal final) ∨
    Core.CoreStepStarE procedures (.stmt (.block name body .empty) entry) trace (.exiting "" final) := by
  obtain ⟨inner, done | exited, projection⟩ := coreBlock_terminal_inside run
  · have done := coreSingleton_terminal_inside done
    have unchanged := coreBlock_projection_id (.inl done)
    rw [unchanged] at projection
    cases inner
    exact .inl (projection ▸ done)
  · have exited := coreSingleton_exit_inside exited
    have unchanged := coreBlock_projection_id (.inr ⟨"", exited⟩)
    rw [unchanged] at projection
    cases inner
    exact .inr (projection ▸ exited)

/-- Core runs a structured procedure inside an extra, silent block. For a
closed inner block, that step preserves the already projected final store. -/
private theorem procedureWrapper_forward {procedures : String → Option Core.Procedure}
    {name : String} {body : List Core.Statement} {initial : State} {outcome : Outcome Unit}
    (closed : (Imperative.Stmt.block name body .empty : Core.Statement).exitsCoveredByBlocks [])
    (run : CoreForwardOutcome procedures (.stmt (.block name body .empty) (coreEnv initial)) outcome) :
    CoreForwardOutcome procedures (.stmt (.block "" [.block name body .empty] .empty) (coreEnv initial))
      outcome := by
  cases outcome with
  | returned value final =>
    cases value
    obtain ⟨trace, steps, passing⟩ := run
    have sameStore := coreBlock_projection_id (.inl steps)
    change Imperative.projectStore (coreStore initial) (coreStore final) = coreStore final at sameStore
    apply forward_admin .step_block
    apply forward_prepend (Imperative.block_inner_starE (Imperative.stmtRun_to_singletonE _ steps)) passing
    refine forward_admin .step_block_done ⟨[], ?_, by simp [coreChecksPass]⟩
    simpa only [coreEnv, sameStore] using
      (ReflTransTrace.refl (r := Core.CoreStepE procedures) (.terminal (coreEnv final)))
  | exited label final =>
    obtain ⟨_, steps, _⟩ := run
    exact False.elim (Imperative.exitsCoveredByBlocks_noEscapeE _ _ closed _ _ _ steps)
  | assertionFailed label final =>
    have inside := forward_singleton run
    obtain ⟨prior, check, reached, steps, passing, failed⟩ := inside
    apply forward_admin .step_block
    exact ⟨prior, check, _, Imperative.block_inner_starE steps, passing, failed⟩
  | stuck => trivial

private theorem procedureWrapper_replays {procedures : String → Option Core.Procedure}
    {name : String} {body : List Core.Statement} {source : Computation (model := .builtins) Unit}
    {entryValid returnValid : State → Prop}
    (closed : (Imperative.Stmt.block name body .empty : Core.Statement).exitsCoveredByBlocks [])
    (replay : CoreReplay procedures (fun initial => .stmt (.block name body .empty) (coreEnv initial))
      source entryValid returnValid) :
    CoreReplay procedures (fun initial => .stmt (.block "" [.block name body .empty] .empty) (coreEnv initial))
      source entryValid returnValid := by
  constructor
  · intro initial final trace valid run passing
    rcases coreProcedureWrapper_terminal_inside run with done | exited
    · exact replay.returns _ _ _ valid done passing
    · exact False.elim (Imperative.exitsCoveredByBlocks_noEscapeE _ _ closed _ _ _ exited)
  · intro initial label final trace _ run _
    have nested : (Imperative.Stmt.block name body .empty : Core.Statement).exitsCoveredByBlocks [""] :=
      (Imperative.exitsCoveredByBlocks_weaken [] [""] (by simp)).1 _ closed
    exact False.elim (Imperative.exitsCoveredByBlocks_noEscapeE _
      (.block "" [.block name body .empty] .empty) ⟨nested, trivial⟩ _ _ _ run)
  · intro initial prior check reached valid run passing failed
    obtain ⟨_, innerList⟩ := coreBlock_trace_inside run
    obtain ⟨_, innerRun⟩ := coreSingleton_trace_inside innerList
    exact replay.fails _ _ _ _ valid innerRun passing failed

/-- A wrapper around an empty Core body emits no events. A run that
finishes keeps the original environment. -/
private theorem coreEmptyBody_run {procedures : String → Option Core.Procedure}
    {env : Imperative.Env Core.Expression} {trace : Imperative.Trace Core.Expression}
    {reached : Core.CoreConfig}
    (run : Core.CoreStepStarE procedures (.stmt (.block "" [] .empty) env) trace reached) :
    trace = [] ∧ (∀ final, reached = .terminal final → final = env) := by
  cases run with
  | refl => exact ⟨rfl, by simp⟩
  | step _ _ _ tail _ first rest =>
    cases first with
    | step_block =>
    simp only [List.nil_append]
    rcases Imperative.block_run_to_finalE rest with
      ⟨_, rfl, inner⟩ | ⟨middle, inner, rfl⟩ |
      ⟨_, _, _, inner, _⟩ | ⟨_, _, _, inner, _⟩
    · exact ⟨(Imperative.stmts_nil_runE _ inner).1, by simp⟩
    · obtain ⟨silent, impossible | same⟩ := Imperative.stmts_nil_runE _ inner
      · contradiction
      · obtain rfl := Imperative.Config.terminal.inj same
        refine ⟨silent, fun final equal => ?_⟩
        have sameEnv := (Imperative.Config.terminal.inj equal).symm
        cases middle
        simpa only [Imperative.projectStore_self] using sameEnv
    · rcases (Imperative.stmts_nil_runE _ inner).2 with impossible | impossible <;> contradiction
    · rcases (Imperative.stmts_nil_runE _ inner).2 with impossible | impossible <;> contradiction

private theorem bindValues_names {bindings : List Binding} {values : List Value}
    (count : bindings.length = values.length) :
    (bindValues bindings values).map Prod.fst = bindings.map Binding.name := by
  simpa [bindValues, List.map_map, Function.comp_def] using
    congrArg (List.map Binding.name) (List.map_fst_zip (Nat.le_of_eq count))

private theorem readValues_of_coreStoresValues
    (bindings : List Binding) (source : Store) (target : Core.CoreStore)
    (values : List Value)
    (represented : ∀ b ∈ bindings,
      target ⟨b.name, ()⟩ = (source.lookup b.name).bind coreValue?)
    (observed : coreStoresValues (bindings.map Binding.name) values target) :
    readValues bindings source = some values := by
  induction bindings generalizing values with
  | nil =>
    have empty := List.length_eq_zero_iff.mp (by simpa using observed.1.symm)
    simp [empty, readValues]
  | cons binding rest ih =>
    cases values with
    | nil =>
      have count := observed.1
      simp at count
    | cons value values =>
      obtain ⟨count, equalities⟩ := observed
      obtain ⟨literal, encoded, inStore⟩ := equalities binding.name value (by simp)
      have equal := represented binding (by simp)
      rw [inStore] at equal
      cases hit : source.lookup binding.name with
      | none => simp [hit] at equal
      | some stored =>
        have same := coreValue?_injective_some (by simpa [hit] using equal.symm) encoded
        subst stored
        have tail := ih values (fun b present => represented b (List.mem_cons_of_mem _ present))
          ⟨by simpa using count, fun name val zipped =>
            equalities name val (List.mem_cons_of_mem _ zipped)⟩
        unfold readValues at tail ⊢
        simp [List.mapM_cons, bind, Option.bind, hit, tail]

private theorem return_reads {interfaceGlobals : List Binding} {source : ProcedureMeaning} {target : Core.Procedure}
    (layout : ProcedureLayout interfaceGlobals source target) (initial final : State)
    (typed : procedureStateWellTyped interfaceGlobals source initial)
    (globalFrame : ∀ name, (final.globals.lookup name).map Value.sort =
      (initial.globals.lookup name).map Value.sort)
    (localFrame : ∀ name, (final.locals.lookup name).map Value.sort =
      (initial.locals.lookup name).map Value.sort)
    (globals outputs : List Value)
    (globalSlots : coreStoresValues (interfaceGlobals.map Binding.name) globals (coreStore final))
    (outputSlots : coreStoresValues (source.outputs.map Binding.name) outputs (coreStore final)) :
    readValues interfaceGlobals final.globals = some globals ∧
      readValues source.outputs final.locals = some outputs := by
  obtain ⟨⟨globalValues, globalsTyped, globalsEq⟩, ⟨localValues, localsTyped, localsEq⟩, _, _⟩ := typed
  have globalNames := bindValues_names (valuesMatch_iff _ _ |>.mp globalsTyped).1
  have localNames := bindValues_names (valuesMatch_iff _ _ |>.mp localsTyped).1
  have distinct := layout.distinct
  simp only [List.append_assoc, List.map_append] at distinct
  have disjoint := (List.nodup_append.mp distinct).2.2
  constructor
  · apply readValues_of_coreStoresValues _ _ _ _ _ globalSlots
    intro binding present
    have globalName := List.mem_map_of_mem (f := Binding.name) present
    have noInitialLocal : initial.locals.lookup binding.name = none := by
      cases h : initial.locals.lookup binding.name with
      | none => rfl
      | some value =>
        have hit := (Store.lookup_isSome_iff initial.locals binding.name).mp (by simp [h])
        rw [localsEq, localNames, List.map_append] at hit
        exact False.elim (disjoint _ globalName _ hit rfl)
    have hit := (Store.lookup_isSome_iff initial.globals binding.name).mpr (by
      rw [globalsEq, globalNames]
      exact globalName)
    have noLocal : final.locals.lookup binding.name = none := by
      simpa [noInitialLocal] using localFrame binding.name
    have finalHit : (final.globals.lookup binding.name).isSome := by
      have same := congrArg Option.isSome (globalFrame binding.name)
      simp only [Option.isSome_map] at same
      exact same.trans hit
    cases h : final.globals.lookup binding.name with
    | none => simp [h] at finalHit
    | some value => exact (coreStore_of_global final _ value noLocal h).trans rfl
  · apply readValues_of_coreStoresValues _ _ _ _ _ outputSlots
    intro binding present
    have hit := (Store.lookup_isSome_iff initial.locals binding.name).mpr (by
      rw [localsEq, localNames]
      exact List.mem_map_of_mem (List.mem_append_right _ present))
    have finalHit : (final.locals.lookup binding.name).isSome := by
      have same := congrArg Option.isSome (localFrame binding.name)
      simp only [Option.isSome_map] at same
      exact same.trans hit
    cases h : final.locals.lookup binding.name with
    | none => simp [h] at finalHit
    | some value => exact (coreStore_of_local final _ value h).trans rfl

private theorem procedure_scope_fresh (globals : List Binding) (source : ProcedureMeaning)
    (sourceStatements : List (BooleDDM.Statement SourceRange))
    (scopeEntry scopeFinal : Scope) (body : Computation (model := .builtins) Unit)
    (interpreted : interpStmts (denotation .builtins) sourceStatements scopeEntry =
      .ok (body, scopeFinal))
    (scopeGlobals : scopeEntry.globals = globals)
    (initial : State) (outcome : Outcome Unit)
    (typed : procedureStateWellTyped globals source initial)
    (ran : body.run initial outcome) :
    ∀ name value, initial.locals.lookup name = none → outcome.state.locals.lookup name = some value →
      coreStore initial ⟨name, ()⟩ = none := by
  intro name value absent allocated
  by_cases occupied : coreStore initial ⟨name, ()⟩ = none
  · exact occupied
  exfalso
  have reserved : name.contains ' ' = true ∨ name ∈ scopeEntry.globals.map Binding.name := by
    simp only [coreStore, absent] at occupied
    cases global : initial.globals.lookup name with
    | some g =>
      obtain ⟨⟨values, wellTyped, stateGlobals⟩, _⟩ := typed
      rw [stateGlobals] at global
      obtain ⟨binding, present, same, _⟩ := lookup_bindValues_binding wellTyped global
      exact Or.inr (by rw [scopeGlobals]; exact List.mem_map.mpr ⟨binding, present, same⟩)
    | none =>
      simp only [global] at occupied
      obtain ⟨represented, found⟩ := Option.ne_none_iff_exists'.mp occupied
      obtain ⟨⟨globalName, globalValue⟩, _, found⟩ := List.exists_of_findSome?_eq_some found
      dsimp only at found
      split at found
      · rename_i equal
        have named : name = (Core.CoreIdent.mkOld globalName).name := beq_iff_eq.mp equal
        exact Or.inl (by simp [named, Core.CoreIdent.mkOld, Core.CoreIdent.oldStr, String.contains_char_eq])
      · contradiction
  have noneFound := interpStmts_no_new_reserved_local sourceStatements scopeEntry scopeFinal body
    interpreted name reserved initial outcome absent ran
  rw [noneFound] at allocated
  contradiction

/-- At a procedure's inner scope boundary, projecting Core's store drops the
same locals as the Boole denotation. Initial locals are reifiable, and each
new local is fresh for the entry globals and snapshots. -/
private theorem procedure_scope_projection (globals : List Binding) (source : ProcedureMeaning)
    {target : Core.Procedure} (layout : ProcedureLayout globals source target)
    (sourceStatements : List (BooleDDM.Statement SourceRange))
    (scopeEntry scopeFinal : Scope) (body : Computation (model := .builtins) Unit)
    (interpreted : interpStmts (denotation .builtins) sourceStatements scopeEntry =
      .ok (body, scopeFinal))
    (scopeGlobals : scopeEntry.globals = globals) :
    ∀ initial outcome, procedureStateWellTyped globals source initial →
      body.run initial outcome →
      coreStore { outcome.state with locals := outcome.state.locals.restrict initial.locals } =
        Imperative.projectStore (coreStore initial) (coreStore outcome.state) := by
  intro initial outcome typed ran
  have frame := interpStmts_frames sourceStatements scopeEntry scopeFinal body interpreted initial outcome ran
  apply coreStore_scope
  · obtain ⟨_, ⟨values, valuesTyped, stateLocals⟩, _⟩ := typed
    intro slot value present
    rw [stateLocals] at present
    obtain ⟨binding, declared, _, sameSort⟩ := lookup_bindValues_binding valuesTyped present
    have scalar : binding.sort.hasCoreLiteral = true := by
      rcases List.mem_append.mp declared with input | output
      · exact scalarFormals_are_scalar _ _ layout.explicitInputs binding input
      · exact scalarFormals_are_scalar _ _ layout.outputOnly binding output
    rw [coreValue?_isSome_iff]
    exact sameSort ▸ scalar
  · rintro ⟨slot, ⟨⟩⟩
    have globalFrame := frame.1 slot
    have snapshots := frame.2.2
    unfold Store.slotType at globalFrame
    cases before : initial.globals.lookup slot <;> cases after : outcome.state.globals.lookup slot
    all_goals simp only [before, after, Option.map_none, Option.map_some] at globalFrame
    all_goals try contradiction
    · simp [coreStore, before, after, snapshots]
    · simp only [Option.some.injEq] at globalFrame
      simp only [coreStore, Store.lookup_nil, before, after]
      rw [coreValue?_isSome_iff, coreValue?_isSome_iff, globalFrame]
  · exact procedure_scope_fresh globals source _ scopeEntry scopeFinal body interpreted scopeGlobals initial outcome typed ran

end Strata.Boole
