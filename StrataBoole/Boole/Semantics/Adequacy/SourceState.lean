/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.Statements
import all StrataBoole.Boole.Semantics.Adequacy.Statements
import all StrataBoole.Boole.Semantics.Adequacy.Lowering
import all StrataBoole.Boole.Interp
import all StrataBoole.Boole.Semantics.Semantics

public section
namespace Strata.Boole
variable {model : TypeModel}

/-! ## State shape across source execution -/

/-- Names and declared types visible at runtime. The value of a slot may change. -/
private def Store.slotType (store : Store model) (name : String) : Option ValueType :=
  (store.lookup name).map Value.sort

/-- A statement retains the types of existing slots and the entry snapshots.
It may add local slots. -/
private def State.ExtendsSlots (before after : State model) : Prop :=
  (∀ name, after.globals.slotType name = before.globals.slotType name) ∧
  (∀ name sort, before.locals.slotType name = some sort → after.locals.slotType name = some sort) ∧
  after.snapshots = before.snapshots

private theorem State.ExtendsSlots.refl (state : State model) : state.ExtendsSlots state :=
  ⟨fun _ => rfl, fun _ _ h => h, rfl⟩

private theorem State.ExtendsSlots.trans {a b c : State model}
    (first : a.ExtendsSlots b) (second : b.ExtendsSlots c) : a.ExtendsSlots c :=
  ⟨fun name => (second.1 name).trans (first.1 name),
   fun name sort h => second.2.1 name sort (first.2.1 name sort h),
   second.2.2.trans first.2.2⟩

private theorem State.ExtendsSlots.restrict {initial final : State model}
    (frame : initial.ExtendsSlots final) :
    ∀ name, (final.locals.restrict initial.locals).slotType name = initial.locals.slotType name := by
  intro name
  unfold Store.slotType
  rw [Store.lookup_restrict]
  cases found : initial.locals.lookup name with
  | none => rfl
  | some value =>
    simpa [Store.slotType, found] using frame.2.1 name value.sort (by simp [Store.slotType, found])

private def Computation.FramesSlots (computation : Computation (model := model) α) : Prop :=
  ∀ initial outcome, computation.run initial outcome → initial.ExtendsSlots outcome.state

private theorem Computation.Preserves.framesSlots {computation : Computation (model := model) α}
    (preserved : computation.Preserves id) : computation.FramesSlots := by
  intro state outcome ran
  have equal : outcome.state = state := preserved _ _ ran
  rw [equal]
  exact .refl _

private theorem Computation.frames_pure (value : α) :
    (Computation.pure (model := model) value).FramesSlots :=
  (Computation.pure_preserves value id).framesSlots

private theorem Computation.frames_bind {first : Computation (model := model) α}
    {next : α → Computation (model := model) β}
    (firstFrame : first.FramesSlots) (nextFrame : ∀ value, (next value).FramesSlots) :
    (first >>= next).FramesSlots := by
  intro initial outcome ran
  rcases (Computation.run_bind first next initial outcome).mp ran with
    ⟨value, middle, firstRan, nextRan⟩ | ⟨_, _, firstRan, rfl⟩ |
    ⟨_, _, firstRan, rfl⟩ | ⟨_, _, firstRan, rfl⟩
  · exact (firstFrame _ _ firstRan).trans (nextFrame value _ _ nextRan)
  all_goals exact firstFrame _ _ firstRan

private theorem Computation.frames_loop {guard : Computation (model := model) Bool}
    {body : Computation (model := model) Unit}
    (guardFrame : guard.FramesSlots) (bodyFrame : body.FramesSlots) :
    (Computation.loop guard body).FramesSlots := by
  intro initial outcome ran
  change Computation.Iteration guard body initial outcome at ran
  induction ran with
  | next hg hb _ ih => exact (guardFrame _ _ hg).trans ((bodyFrame _ _ hb).trans ih)
  | bodyExit hg hb | bodyFailure hg hb | bodyStuck hg hb =>
    exact (guardFrame _ _ hg).trans (bodyFrame _ _ hb)
  | stop h | guardExit h | guardFailure h | guardStuck h => exact guardFrame _ _ h

private theorem Computation.scope_slotTypes {body : Computation (model := model) Unit}
    (frame : body.FramesSlots) {initial : State model} {outcome : Outcome Unit model}
    (ran : (Computation.scope body).run initial outcome) :
    (∀ name, outcome.state.globals.slotType name = initial.globals.slotType name) ∧
    (∀ name, outcome.state.locals.slotType name = initial.locals.slotType name) := by
  obtain ⟨inner, bodyRan, rfl⟩ := ran
  have kept := frame _ _ bodyRan
  cases inner <;> exact ⟨kept.1, kept.restrict⟩

private theorem Computation.frames_scope {body : Computation (model := model) Unit}
    (frame : body.FramesSlots) : (Computation.scope body).FramesSlots := by
  intro initial outcome ran
  obtain ⟨inner, bodyRan, rfl⟩ := ran
  have kept := frame _ _ bodyRan
  cases inner <;> exact ⟨kept.1, fun name sort h => (kept.restrict name).trans h, kept.2.2⟩

private theorem Computation.frames_block (name : String) {body : Computation (model := model) Unit}
    (frame : body.FramesSlots) : (Computation.block name body).FramesSlots := by
  intro initial outcome ran
  obtain ⟨inner, bodyRan, rfl⟩ := ran
  have kept := frame _ _ bodyRan
  cases inner with
  | exited label final =>
    by_cases same : (label == name) = true <;> simpa [same, Outcome.state] using kept
  | returned | assertionFailed | stuck => exact kept

private theorem Computation.run_get_bind (next : State model → Computation (model := model) α)
    (state : State model) (outcome : Outcome α model) :
    (Computation.get >>= next).run state outcome ↔ (next state).run state outcome := by
  simp only [Computation.run_bind, Computation.get, Outcome.returned.injEq, reduceCtorEq,
    false_and, exists_false, or_false]
  constructor
  · rintro ⟨_, _, ⟨rfl, rfl⟩, ran⟩
    exact ran
  · exact fun ran => ⟨state, state, ⟨rfl, rfl⟩, ran⟩

private theorem Computation.run_evaluate_bind (expression : Expression model)
    (next : Value model → Computation (model := model) α) (state : State model)
    (outcome : Outcome α model) :
    (Computation.evaluate expression >>= next).run state outcome ↔
      match expression state with
      | .ok value => (next value).run state outcome
      | .error reason => outcome = .stuck reason state := by
  cases evaluated : expression state with
  | ok value =>
    simp only [Computation.run_bind, Computation.evaluate, evaluated, Outcome.returned.injEq,
      reduceCtorEq, false_and, exists_false, or_false]
    constructor
    · rintro ⟨_, _, ⟨rfl, rfl⟩, ran⟩
      exact ran
    · exact fun ran => ⟨value, state, ⟨rfl, rfl⟩, ran⟩
  | error reason =>
    simp only [Computation.run_bind, Computation.evaluate, evaluated, Outcome.stuck.injEq,
      reduceCtorEq, false_and, exists_false, false_or]
    constructor
    · rintro ⟨_, _, ⟨rfl, rfl⟩, rfl⟩
      rfl
    · rintro rfl
      exact ⟨reason, state, ⟨rfl, rfl⟩, rfl⟩

private theorem Computation.frames_test (guard : Option (Expression model)) :
    (Computation.test guard).FramesSlots := by
  intro state outcome ran
  cases guard with
  | none =>
    rcases ran with rfl | rfl <;> exact .refl _
  | some expression =>
    unfold Computation.test at ran
    rw [Computation.run_evaluate_bind] at ran
    cases evaluated : expression state with
    | error reason =>
      rw [evaluated] at ran
      obtain rfl := ran
      exact .refl _
    | ok value =>
      rw [evaluated] at ran
      change ((match value with
        | .bool b => Computation.pure b
        | _ => Computation.stuck .wrongType)).run state outcome at ran
      split at ran <;> obtain rfl := ran <;> exact .refl _

private theorem Store.slotType_update {store : Store model} {name : String} {previous value : Value model}
    (found : store.lookup name = some previous) (sort : previous.sort = value.sort) (other : String) :
    (store.update name value).slotType other = store.slotType other := by
  by_cases same : other = name
  · subst other
    simp [Store.slotType, found, sort]
  · simp [Store.slotType, Store.lookup_update_other _ _ _ _ same]

private theorem State.extendsSlots_update (state : State model) (reference : Variable)
    (previous value : Value model) (found : state.lookup reference = some previous)
    (sort : previous.sort = value.sort) : state.ExtendsSlots (state.update reference value) := by
  cases reference with
  | «local» name => exact ⟨fun _ => rfl, fun other _ h => (Store.slotType_update found sort other).trans h, rfl⟩
  | global name => exact ⟨Store.slotType_update found sort, fun _ _ h => h, rfl⟩

private theorem Computation.frames_assign (reference : Variable) (expression : Expression model) :
    (Computation.assign reference expression).FramesSlots := by
  intro state outcome ran
  unfold Computation.assign at ran
  rw [Computation.run_get_bind, Computation.run_evaluate_bind] at ran
  unfold Expression.read at ran
  cases slot : state.lookup reference with
  | none =>
    simp only [slot] at ran
    obtain rfl := ran
    exact .refl _
  | some previous =>
    simp only [slot] at ran
    rw [Computation.run_evaluate_bind] at ran
    cases evaluated : expression state with
    | error reason =>
      rw [evaluated] at ran
      obtain rfl := ran
      exact .refl _
    | ok value =>
      rw [evaluated] at ran
      change (if previous.sort ≠ value.sort then Computation.stuck .wrongType
        else Computation.put (state.update reference value)).run state outcome at ran
      split at ran
      · obtain rfl := ran
        exact .refl _
      · rename_i same
        obtain rfl := ran
        exact state.extendsSlots_update reference previous value slot (Classical.not_not.mp same)

private theorem Store.slotType_append_of_some {store : Store model} {name : String} {sort : ValueType}
    (known : store.slotType name = some sort) (extra : Store model) :
    Store.slotType (store ++ extra) name = some sort := by
  have append : Store.lookup (store ++ extra) name = (store.lookup name).or (extra.lookup name) :=
    List.findSome?_append
  unfold Store.slotType at *
  rw [append]
  cases found : store.lookup name with
  | none => rw [found] at known; contradiction
  | some value => rw [found] at known; exact known

private theorem Computation.frames_declare (binding : Binding) (initializer : Option (Expression model)) :
    (Computation.declare binding initializer).FramesSlots := by
  intro state outcome ran
  have extension (value : Value model) : state.ExtendsSlots
      { state with locals := state.locals ++ [(binding.name, value)] } :=
    ⟨fun _ => rfl, fun _ _ known => Store.slotType_append_of_some known _, rfl⟩
  unfold Computation.declare at ran
  rw [Computation.run_get_bind] at ran
  split at ran
  · obtain rfl := ran
    exact .refl _
  · have write : ∀ value, (if value.sort ≠ binding.sort then Computation.stuck .wrongType
          else Computation.put { state with locals := state.locals ++ [(binding.name, value)] }).run
          state outcome → state.ExtendsSlots outcome.state := by
      intro value wrote
      split at wrote
      · obtain rfl := wrote
        exact .refl _
      · obtain rfl := wrote
        exact extension value
    cases initializer with
    | none =>
      simp only [Computation.run_bind, Computation.choose, reduceCtorEq, Outcome.returned.injEq,
        and_false, exists_false, false_and, or_false] at ran
      obtain ⟨value, middle, ⟨v, _, rfl, rfl⟩, rest⟩ := ran
      exact write value rest
    | some expression =>
      rw [Computation.run_evaluate_bind] at ran
      cases evaluated : expression state with
      | error reason =>
        rw [evaluated] at ran
        obtain rfl := ran
        exact .refl _
      | ok value => rw [evaluated] at ran; exact write value ran

private theorem Computation.frames_choose (sort : ValueType) :
    (Computation.choose (model := model) sort).FramesSlots := by
  rintro state _ ⟨_, _, rfl⟩
  exact .refl state

private theorem Computation.frames_assertion (label : String) (expression : Expression model) :
    (Computation.assertion label expression).FramesSlots := by
  apply Computation.frames_bind (Computation.frames_test _)
  intro b
  cases b with
  | true => exact Computation.frames_pure ()
  | false =>
    intro state outcome ran
    obtain rfl := ran
    exact .refl state

private theorem Computation.frames_assumption (expression : Expression model) :
    (Computation.assumption expression).FramesSlots := by
  apply Computation.frames_bind (Computation.frames_test _)
  intro b
  cases b with
  | true => exact Computation.frames_pure ()
  | false => exact fun _ _ impossible => False.elim impossible

private theorem forIn_framesSlots {α : Type} (items : List α)
    (step : α → Computation (model := model) Unit →
      InterpM (ForInStep (Computation (model := model) Unit)))
    (preserve : ∀ item before entry control final,
      step item before entry = .ok (control, final) →
      before.FramesSlots → control.value.FramesSlots)
    (before after : Computation (model := model) Unit) (entry final : Scope)
    (success : (forIn items before step) entry = .ok (after, final))
    (frame : before.FramesSlots) : after.FramesSlots := by
  induction items generalizing before entry with
  | nil =>
    have equal : before = after := congrArg Prod.fst (Except.ok.inj success)
    rw [← equal]
    exact frame
  | cons item items ih =>
    simp only [List.forIn_cons, bind, StateT.bind, Except.bind, pure] at success
    cases first : step item before entry with
    | error => simp [first] at success
    | ok result =>
      obtain ⟨control, next⟩ := result
      have kept := preserve _ _ _ _ _ first frame
      cases control with
      | done current =>
        have equal : current = after := by
          simpa [first, Except.map, StateT.pure, pure, Except.pure] using
            congrArg (Except.map Prod.fst) success
        exact equal ▸ kept
      | yield current =>
        exact ih current next (by simpa [first] using success) kept

private theorem declarations_frame (declarations : List (BooleDDM.Bind SourceRange))
    (range : SourceRange) (entry final : Scope) (body : Computation (model := .builtins) Unit)
    (success : (forIn declarations ((denotation .builtins).skip) (fun (declaration : BooleDDM.Bind SourceRange) (result : Computation (model := .builtins) Unit) => do
      let .bind_mk _ name _ ty := declaration
      let binding ← addLocal range name.val ty
      pure (.yield ((denotation .builtins).seq result ((denotation .builtins).declare binding none)))))
      entry = .ok (body, final)) : body.FramesSlots := by
  apply forIn_framesSlots _ _ _ _ _ _ _ success (Computation.frames_pure ())
  intro declaration before state control next ran frame
  cases declaration
  simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
  split at ran
  · contradiction
  · have equal := congrArg (fun pair => pair.1.value) (Except.ok.inj ran)
    change _ = control.value at equal
    rw [← equal]
    change (before >>= fun _ => Computation.declare _ none).FramesSlots
    exact Computation.frames_bind frame (fun _ => Computation.frames_declare _ _)

private theorem blockStatementList_size (range : SourceRange)
    (statements : StrataDDM.Ann (Array (BooleDDM.Statement SourceRange)) SourceRange) :
    sizeOf statements.val.toList < sizeOf (BooleDDM.Block.block range statements) := by
  obtain ⟨_, ⟨statements⟩⟩ := statements
  simp
  omega

mutual

private theorem interpStmt_frames (statement : BooleDDM.Statement SourceRange)
    (entry final : Scope) (body : Computation (model := .builtins) Unit)
    (success : interpStmt (denotation .builtins) statement entry = .ok (body, final)) :
    body.FramesSlots := by
  cases statement
  case' assign range annotations type lhs expression => cases lhs
  all_goals rw [interpStmt.eq_def] at success
  case' while_statement range annotations guard decreases invariants loopBody =>
    obtain ⟨measureRange, measure⟩ := decreases
    cases measure
    case' some measure => cases measure
  all_goals
    repeat' first
      | contradiction
      | simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
          get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet,
          reject, throw, throwThe, MonadExceptOf.throw] at success
      | (have same : _ = body := congrArg Prod.fst (Except.ok.inj success)
         try simp only [denotation] at same
         rw [← same]
         first
         | exact Computation.frames_declare _ _
         | exact Computation.frames_assign _ _
         | exact Computation.frames_bind (Computation.frames_choose _) (fun _ => Computation.frames_assign _ _)
         | exact Computation.frames_assertion _ _
         | exact Computation.frames_assumption _
         | exact declarations_frame _ _ _ _ _ (by assumption)
         | (apply Computation.frames_loop (Computation.frames_test _)
            exact interpBlock_frames _ _ _ _ (by assumption))
         | (apply Computation.frames_bind (Computation.frames_test _)
            intro taken
            cases taken
            · first | exact Computation.frames_pure () | exact interpBlock_frames _ _ _ _ (by assumption)
            · exact interpBlock_frames _ _ _ _ (by assumption))
         | (apply Computation.frames_block
            rename_i found
            obtain ⟨_, ran⟩ := withScope_success found
            simp only [StateT.bind, StateT.modifyGet] at ran
            exact interpBlock_frames _ _ _ _ ran)
         | (intro state outcome ran
            have equal : outcome = .exited _ state := ran
            obtain rfl := equal
            exact State.ExtendsSlots.refl _))
      | split at success
termination_by sizeOf statement
decreasing_by all_goals simp_all <;> omega

private theorem interpStmts_frames (statements : List (BooleDDM.Statement SourceRange))
    (entry final : Scope) (body : Computation (model := .builtins) Unit)
    (success : interpStmts (denotation .builtins) statements entry = .ok (body, final)) :
    body.FramesSlots := by
  cases statements with
  | nil =>
    rw [interpStmts] at success
    obtain rfl := congrArg Prod.fst (Except.ok.inj success)
    exact Computation.frames_pure ()
  | cons statement rest =>
    rw [interpStmts] at success
    simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at success
    split at success
    · contradiction
    · rename_i first headRan
      split at success
      · contradiction
      · rename_i remaining tailRan
        obtain rfl := congrArg Prod.fst (Except.ok.inj success)
        exact Computation.frames_bind (interpStmt_frames statement entry first.2 first.1 headRan)
          (fun _ => interpStmts_frames rest first.2 remaining.2 remaining.1 tailRan)
termination_by sizeOf statements

private theorem interpBlock_frames (block : BooleDDM.Block SourceRange)
    (entry final : Scope) (body : Computation (model := .builtins) Unit)
    (success : interpBlock (denotation .builtins) block entry = .ok (body, final)) :
    body.FramesSlots := by
  cases block with
  | block range statements =>
    have unfoldBlock : interpBlock (denotation .builtins) (.block range statements) =
        withScope (do
          let inside ← interpStmts (denotation .builtins) statements.val.toList
          pure (Computation.scope inside)) := by
      cases statements
      rw [interpBlock]
      rfl
    rw [unfoldBlock] at success
    obtain ⟨_, inner⟩ := withScope_success success
    simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at inner
    split at inner
    · contradiction
    · rename_i pair ran
      have equal : Computation.scope pair.1 = body := congrArg Prod.fst (Except.ok.inj inner)
      rw [← equal]
      exact Computation.frames_scope (interpStmts_frames statements.val.toList entry pair.2 pair.1 ran)
termination_by sizeOf block
decreasing_by
  subst_vars
  exact blockStatementList_size _ _

end

private theorem interpBlock_slotTypes (block : BooleDDM.Block SourceRange)
    (entry final : Scope) (body : Computation (model := .builtins) Unit)
    (success : interpBlock (denotation .builtins) block entry = .ok (body, final))
    {state : State} {outcome : Outcome Unit} (ran : body.run state outcome) :
    (∀ name, outcome.state.globals.slotType name = state.globals.slotType name) ∧
    (∀ name, outcome.state.locals.slotType name = state.locals.slotType name) := by
  cases block with
  | block range statements =>
    obtain ⟨_, statements⟩ := statements
    rw [interpBlock] at success
    obtain ⟨_, inner⟩ := withScope_success success
    simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at inner
    split at inner
    · contradiction
    · rename_i pair interpreted
      have same : Computation.scope pair.1 = body := congrArg Prod.fst (Except.ok.inj inner)
      rw [← same] at ran
      exact Computation.scope_slotTypes (interpStmts_frames _ _ _ _ interpreted) ran

private theorem interpProc_slotTypes (range : SourceRange) (name : String)
    (types : Option (BooleDDM.TypeArgs SourceRange)) (inputs : BooleDDM.Bindings SourceRange)
    (outputs : Option (BooleDDM.MonoDeclList SourceRange)) (spec : Option (BooleDDM.Spec SourceRange))
    (body : Option (BooleDDM.Block SourceRange)) (entry final : Scope) (procedure : ProcedureMeaning)
    (success : interpProc (denotation .builtins) range name types inputs outputs spec body entry =
      .ok (procedure, final)) {state : State} {outcome : Outcome Unit} (ran : procedure.body.run state outcome) :
    (∀ name, outcome.state.globals.slotType name = state.globals.slotType name) ∧
    (∀ name, outcome.state.locals.slotType name = state.locals.slotType name) := by
  unfold interpProc at success
  obtain ⟨_, success⟩ := withScope_success success
  cases types <;> cases outputs <;> cases body
  all_goals
    repeat' first
      | contradiction
      | simp only [Option.isSome, Bool.false_eq_true, ite_false,
          bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
          modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
          reject, throw, throwThe, MonadExceptOf.throw] at success
      | (have same : _ = procedure.body :=
           congrArg (fun p => p.1.body) (Except.ok.inj success)
         change Computation.block name _ = procedure.body at same
         rw [← same] at ran
         obtain ⟨inner, ran, rfl⟩ := ran
         have frame := interpBlock_slotTypes _ _ _ _ (by assumption) ran
         cases inner with
         | exited label state =>
           by_cases caught : (label == name) = true <;> simpa [caught, Outcome.state] using frame
         | returned | assertionFailed | stuck => exact frame)
      | split at success

/-- A procedure changes the values of existing globals and formals while
preserving their names and types. Its body-local slots are gone at return. -/
theorem interpretedProcedure_return_slotTypes {command : BooleDDM.Command SourceRange}
    {procedure : ProcedureMeaning}
    (interpreted : ProcedureWasInterpreted (denotation .builtins) command procedure)
    (initial final : State) (ran : procedure.body.run initial (.returned () final)) :
    (∀ name, (final.globals.lookup name).map Value.sort = (initial.globals.lookup name).map Value.sort) ∧
    (∀ name, (final.locals.lookup name).map Value.sort = (initial.locals.lookup name).map Value.sort) := by
  cases command <;> simp only [ProcedureWasInterpreted] at interpreted
  all_goals
    first
    | contradiction
    | obtain ⟨_, _, called⟩ := interpreted
      exact interpProc_slotTypes _ _ _ _ _ _ _ _ _ _ called ran

end Strata.Boole
