/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.Expressions
import all StrataBoole.Boole.Semantics.Adequacy.Lowering
import all StrataBoole.Boole.Interp
import StrataBoole.Boole.Semantics.Adequacy.SourceInterface
import all StrataBoole.Boole.Semantics.CoreReference
import all StrataBoole.Boole.Semantics.Semantics
import Strata.DL.Imperative.CmdSemanticsProps
import Strata.Languages.Core.IdentifiersProps
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.Languages.Core.StatementSemanticsProps
import Strata.DL.Imperative.StmtSemanticsProps
import Strata.Util.RelationsProps
import all StrataBoole.Boole.Runtime

public section

/-! ## Laws of Boole denotations -/

namespace Strata.Boole
variable {model : TypeModel}
namespace Computation

/-- Two computations are equal when they permit the same outcomes in every state. -/
@[ext] theorem ext {first second : Computation (model := model) α}
    (same : ∀ state outcome, first.run state outcome ↔ second.run state outcome) : first = second := by
  cases first; cases second
  congr
  funext state outcome
  exact propext (same state outcome)

/-- A pure computation returns its value and leaves the state unchanged. -/
@[simp] theorem run_pure (value : α) (state : State model) (outcome : Outcome α model) :
    (Computation.pure value).run state outcome ↔ outcome = .returned value state := Iff.rfl

/-- Sequencing either continues from a normal result or propagates an early outcome. -/
theorem run_bind (first : Computation (model := model) α) (next : α → Computation (model := model) β) (state : State model) (outcome : Outcome β model) :
    (first >>= next).run state outcome ↔
      (∃ value middle, first.run state (.returned value middle) ∧ (next value).run middle outcome) ∨
      (∃ label final, first.run state (.exited label final) ∧ outcome = .exited label final) ∨
      (∃ label final, first.run state (.assertionFailed label final) ∧ outcome = .assertionFailed label final) ∨
      (∃ reason final, first.run state (.stuck reason final) ∧ outcome = .stuck reason final) := Iff.rfl

/-- Running a continuation after a pure value is the continuation itself. -/
@[simp] theorem pure_bind (value : α) (next : α → Computation (model := model) β) :
    (Computation.pure value >>= next) = next value := by
  apply ext
  intro state outcome
  simp [run_bind, and_assoc]

/-- Returning the result of a computation does not change its meaning. -/
@[simp] theorem bind_pure (first : Computation (model := model) α) :
    (first >>= Computation.pure) = first := by
  apply ext
  intro state outcome
  cases outcome <;> simp [run_bind]

/-- Parenthesizing a sequence differently does not change its meaning. -/
theorem bind_assoc (first : Computation (model := model) α) (second : α → Computation (model := model) β) (third : β → Computation (model := model) γ) :
    ((first >>= second) >>= third) = (first >>= fun value => second value >>= third) := by
  apply ext
  intro state outcome
  cases outcome <;> simp [run_bind, exists_or,
    or_and_right, and_or_left] <;> grind

/-- A loop whose guard is false has the meaning of skip, for every body. -/
@[simp] theorem loop_false (body : Computation (model := model) Unit) :
    loop (Computation.pure false) body = Computation.pure () := by
  apply ext
  intro initial outcome
  constructor
  · intro h
    change Iteration _ _ _ _ at h
    cases h <;> simp_all [Computation.pure]
  · intro h
    obtain rfl := h
    exact .stop rfl

/-- An always-true loop with a skip body has no finite outcome. -/
theorem loop_true_skip_no_outcome (initial : State model) (outcome : Outcome Unit model) :
    ¬ (loop (Computation.pure true) (Computation.pure ())).run initial outcome := by
  intro h
  change Iteration _ _ _ _ at h
  induction h <;> simp_all [Computation.pure]

/-- The monadic notation obeys its standard laws; no additional axioms are used. -/
instance : LawfulMonad (Computation (model := model)) :=
  LawfulMonad.mk' (Computation (model := model))
    (id_map := by intro α first; change (first >>= fun a => Computation.pure (id a)) = first; simp)
    (pure_bind := by intro α β value next; exact pure_bind value next)
    (bind_assoc := by intro α β γ first second third; exact bind_assoc first second third)

/-- Every finite outcome preserves the selected observation of state. This can
express that one variable, all globals, or the snapshots remain unchanged. -/
def Preserves (computation : Computation (model := model) α) (observe : State model → β) : Prop :=
  ∀ initial outcome, computation.run initial outcome → observe outcome.state = observe initial

/-- A pure value preserves every observation of the state. -/
theorem pure_preserves (value : α) (observe : State model → β) :
    Preserves (Computation.pure value) observe := by
  intro initial outcome h
  obtain rfl := h
  rfl

/-- State preservation composes across sequencing, including early outcomes. -/
theorem bind_preserves {first : Computation (model := model) α}
    {next : α → Computation (model := model) β} {observe : State model → γ}
    (firstPreserves : Preserves first observe) (nextPreserves : ∀ value, Preserves (next value) observe) :
    Preserves (first >>= next) observe := by
  intro initial outcome h
  rcases run_bind first next initial outcome |>.mp h with
    ⟨value, middle, hfirst, hnext⟩ | ⟨label, final, hfirst, rfl⟩ |
    ⟨label, final, hfirst, rfl⟩ | ⟨reason, final, hfirst, rfl⟩
  · exact (nextPreserves value middle outcome hnext).trans (firstPreserves initial _ hfirst)
  · exact firstPreserves initial _ hfirst
  · exact firstPreserves initial _ hfirst
  · exact firstPreserves initial _ hfirst

/-- A loop preserves anything preserved by its guard and body. This is the frame
principle for finite loop outcomes, and includes failure and exit outcomes. -/
theorem loop_preserves {guard : Computation (model := model) Bool}
    {body : Computation (model := model) Unit} {observe : State model → α}
    (guardPreserves : Preserves guard observe) (bodyPreserves : Preserves body observe) :
    Preserves (loop guard body) observe := by
  intro initial outcome h
  change Iteration guard body initial outcome at h
  induction h with
  | stop h => exact guardPreserves _ _ h
  | next hg hb _ ih => exact ih.trans ((bodyPreserves _ _ hb).trans (guardPreserves _ _ hg))
  | guardExit h => exact guardPreserves _ _ h
  | guardFailure h => exact guardPreserves _ _ h
  | guardStuck h => exact guardPreserves _ _ h
  | bodyExit hg hb => exact (bodyPreserves _ _ hb).trans (guardPreserves _ _ hg)
  | bodyFailure hg hb => exact (bodyPreserves _ _ hb).trans (guardPreserves _ _ hg)
  | bodyStuck hg hb => exact (bodyPreserves _ _ hb).trans (guardPreserves _ _ hg)

end Computation
namespace Store

/-- Updating one name leaves every distinct name unchanged. -/
@[simp] theorem lookup_update_other (store : Store model) (name other : String) (value : Value model)
    (different : other ≠ name) : (store.update name value).lookup other = store.lookup other := by
  induction store with
  | nil => rfl
  | cons binding rest ih =>
      obtain ⟨key, previous⟩ := binding
      by_cases h : key = other
      · subst key; simp [Store.lookup, Store.update, different]
      · simpa [Store.lookup, Store.update, h] using ih

/-- An update changes existing values, but never creates a missing slot. -/
@[simp] theorem lookup_update (store : Store model) (name : String) (value : Value model) :
    (store.update name value).lookup name = (store.lookup name).map (fun _ => value) := by
  induction store with
  | nil => rfl
  | cons binding rest ih =>
      obtain ⟨key, previous⟩ := binding
      by_cases h : key = name
      · subst key; simp [Store.lookup, Store.update]
      · simpa [Store.lookup, Store.update, h] using ih

/-- Lookup in an empty store has no value. -/
@[simp] theorem lookup_nil (name : String) : Store.lookup ([] : Store model) name = none := by rfl

/-- Lookup first inspects the head slot, then the remaining store. -/
theorem lookup_cons (key name : String) (value : Value model) (rest : Store model) :
    Store.lookup ((key, value) :: rest) name = if key == name then some value else Store.lookup rest name := by
  by_cases h : key = name <;> simp [Store.lookup, h]

/-- Look up the first occurrence across two consecutive sets of bindings. -/
theorem lookup_append (first second : Store model) (name : String) :
    Store.lookup (first ++ second) name = (first.lookup name).or (second.lookup name) := by
  simp only [Store.lookup, List.findSome?_append]

/-- Scope cleanup retains the current value exactly for names present at entry. -/
theorem lookup_restrict (current entry : Store model) (name : String) :
    (current.restrict entry).lookup name =
      if (entry.lookup name).isSome then current.lookup name else none := by
  induction current with
  | nil => simp only [Store.restrict, List.filter_nil, lookup_nil, ite_self]
  | cons binding rest ih =>
      obtain ⟨key, value⟩ := binding
      by_cases h : key = name
      · subst key
        cases he : (entry.lookup name).isSome <;>
          simp only [Store.restrict, List.filter_cons, he, Bool.false_eq_true,
            ite_false, ite_true, lookup_cons, beq_self_eq_true] at ih ⊢
        exact ih
      · cases he : (entry.lookup key).isSome <;>
          simp only [Store.restrict, List.filter_cons, he, Bool.false_eq_true,
            ite_false, ite_true, lookup_cons, beq_iff_eq, h] <;> exact ih

end Store

/-- Updating a source variable never changes an entry snapshot. -/
@[simp] theorem State.update_snapshots (state : State model) (reference : Variable) (value : Value model) :
    (state.update reference value).snapshots = state.snapshots := by cases reference <;> rfl

/-- Assigning one source variable leaves every distinct variable unchanged. -/
theorem State.lookup_update_other (state : State model) (written observed : Variable) (value : Value model)
    (different : observed ≠ written) :
    (state.update written value).lookup observed = state.lookup observed := by
  cases written <;> cases observed <;> simp only [State.update, State.lookup]
  all_goals first
    | rfl
    | (apply Store.lookup_update_other; intro same; apply different; cases same; rfl)

/-- The executable interface check means equal lengths and equal declared/value
sorts at every corresponding position. -/
theorem valuesMatch_iff (bindings : List Binding) (values : List (Value model)) :
    valuesMatch bindings values = true ↔
      bindings.length = values.length ∧
      ∀ binding value, (binding, value) ∈ bindings.zip values → binding.sort = value.sort := by
  simp [valuesMatch, List.all_eq_true]

end Strata.Boole

/-! ## Store updates, snapshots, and assignment -/

namespace Strata.Boole

/-- Updating an existing local, then representing the store, is a valid
Core update of exactly that slot. -/
theorem coreUpdate_local (state : State) (name : String) (previous value : Value)
    (slot : state.locals.lookup name = some previous)
    {oldExpr newExpr : Core.Expression.Val}
    (oldRep : coreValue? previous = some oldExpr) (newRep : coreValue? value = some newExpr) :
    Imperative.UpdateState (P := Core.Expression) (coreStore state) ⟨name, ()⟩ newExpr
      (coreStore (state.update (.local name) value)) := by
  refine .update (v' := oldExpr) ((coreStore_of_local state name previous slot).trans oldRep) ?_ ?_
  · apply Eq.trans (coreStore_of_local _ name value _) newRep
    simp [State.update, slot]
  · rintro ⟨other, ⟨⟩⟩ different
    have names : other ≠ name := by
      intro same
      subst other
      exact different rfl
    simp only [coreStore, State.update, Store.lookup_update_other _ _ _ _ names]

/-- Updating an unshadowed global preserves the other Core slots, including the
separate slots containing saved entry values. -/
theorem coreUpdate_global (state : State) (name : String) (previous value : Value)
    (notLocal : state.locals.lookup name = none) (slot : state.globals.lookup name = some previous)
    {oldExpr newExpr : Core.Expression.Val}
    (oldRep : coreValue? previous = some oldExpr) (newRep : coreValue? value = some newExpr) :
    Imperative.UpdateState (P := Core.Expression) (coreStore state) ⟨name, ()⟩ newExpr
      (coreStore (state.update (.global name) value)) := by
  refine .update (v' := oldExpr) ((coreStore_of_global state name previous notLocal slot).trans oldRep) ?_ ?_
  · apply Eq.trans (coreStore_of_global (state.update (.global name) value) name value notLocal _) newRep
    simp [State.update, slot]
  · rintro ⟨other, ⟨⟩⟩ different
    have names : other ≠ name := by
      intro same
      subst other
      exact different rfl
    simp only [coreStore, State.update, Store.lookup_update_other _ _ _ _ names]

private theorem snapshotSlot (snapshots : Store) (name : String) (value : Value)
    (saved : snapshots.lookup name = some value) {expression : Core.Expression.Val}
    (represented : coreValue? value = some expression) :
    snapshots.findSome? (fun (key, current) =>
      if (Core.CoreIdent.mkOld name).name == (Core.CoreIdent.mkOld key).name
      then coreValue? current else none) = some expression := by
  induction snapshots with
  | nil => simp at saved
  | cons binding rest ih =>
      obtain ⟨key, current⟩ := binding
      by_cases same : key = name
      · subst key
        have sameValue : current = value := by simpa [Store.lookup_cons] using saved
        simp [sameValue, represented]
      · have distinct : (Core.CoreIdent.mkOld name).name ≠ (Core.CoreIdent.mkOld key).name := by
          intro names
          have ids : Core.CoreIdent.mkOld name = Core.CoreIdent.mkOld key := by
            simpa [Core.CoreIdent.mkOld] using congrArg (fun s => (⟨s, ()⟩ : Core.CoreIdent)) names
          exact same (Core.CoreIdent.mkOld_injective ids).symm
        simp [Store.lookup_cons, same] at saved
        simpa [distinct] using ih saved

/-- A saved global is represented under the reserved Core `old` name. -/
theorem coreStore_old (state : State) (name : String) (value : Value)
    (noLocal : state.locals.lookup (Core.CoreIdent.mkOld name).name = none)
    (noGlobal : state.globals.lookup (Core.CoreIdent.mkOld name).name = none)
    (saved : state.snapshots.lookup name = some value) {expression : Core.Expression.Val}
    (represented : coreValue? value = some expression) :
    coreStore state (Core.CoreIdent.mkOld name) = some expression := by
  simpa [coreStore, noLocal, noGlobal] using snapshotSlot state.snapshots name value saved represented

/-- When an assignment's operands are defined and typed, it returns exactly
the updated state in the source denotation. -/
theorem assign_run_iff {state : State} {reference : Variable} {expression : Expression}
    {previous value : Value} {outcome : Outcome Unit}
    (slot : state.lookup reference = some previous)
    (evaluated : expression state = .ok value) (sameType : previous.sort = value.sort) :
    (Computation.assign reference expression).run state outcome ↔
      outcome = .returned () (state.update reference value) := by
  simp [Computation.assign, Computation.run_bind, Computation.get, Computation.evaluate,
    Expression.read, slot, evaluated, sameType, Computation.put, and_assoc]

/-- A deterministic Core assignment with a known RHS and typed update has
exactly the represented update as its resulting store. -/
theorem coreSet_store_iff {store updated final : Core.CoreStore}
    {id : Core.CoreIdent} {rhs : Core.Expression.Expr} {value : Core.Expression.Val}
    (metadata : Imperative.MetaData Core.Expression)
    (evaluated : Core.Expression.eval coreRuntimeFactory store rhs = some value)
    (updatedSlot : Imperative.UpdateState (P := Core.Expression) store id value updated)
    (typed : Imperative.HasVal.valueOfStoredTy (P := Core.Expression) coreRuntimeFactory store id value) :
    Imperative.EvalCmdE Core.Expression coreRuntimeFactory store (.set id (.det rhs) metadata) final [] ↔
      final = updated := by
  constructor
  · intro command
    exact match command with
    | .eval_set rhsEval update _ _ => by
      obtain rfl := Option.some.inj (rhsEval.symm.trans evaluated)
      exact Imperative.UpdateStateUniqueResult update updatedSlot
  · rintro rfl
    exact .eval_set evaluated updatedSlot typed
      (Core.coreEvaluator_WellFormedSemanticEvalVar coreRuntimeFactory)

/-- Core uses one namespace for both global and local runtime slots. -/
def Variable.coreIdent : Variable → Core.CoreIdent
  | .local name | .global name => ⟨name, ()⟩

private theorem coreAssignment_update (state : State) (reference : Variable)
    {previous value : Value} {oldExpr newExpr : Core.Expression.Val}
    (slot : state.lookup reference = some previous)
    (unshadowed : ∀ name, reference = .global name → state.locals.lookup name = none)
    (sameType : previous.sort = value.sort)
    (oldRep : coreValue? previous = some oldExpr) (newRep : coreValue? value = some newExpr) :
    Imperative.UpdateState (P := Core.Expression) (coreStore state) reference.coreIdent newExpr
      (coreStore (state.update reference value)) ∧
    Imperative.HasVal.valueOfStoredTy (P := Core.Expression) coreRuntimeFactory
      (coreStore state) reference.coreIdent newExpr := by
  have updated : Imperative.UpdateState (P := Core.Expression) (coreStore state)
      reference.coreIdent newExpr (coreStore (state.update reference value)) := by
    cases reference with
    | «local» name => exact coreUpdate_local state name previous value slot oldRep newRep
    | global name =>
      exact coreUpdate_global state name previous value (unshadowed name rfl) slot oldRep newRep
  obtain ⟨ty, oldTyped, newTyped⟩ := coreValues_sameType sameType oldRep newRep
  have previousSlot : coreStore state reference.coreIdent = some oldExpr := by
    cases reference with
    | «local» name => exact (coreStore_of_local state name previous slot).trans oldRep
    | global name => exact
        (coreStore_of_global state name previous (unshadowed name rfl) slot).trans oldRep
  exact ⟨updated, oldExpr, ty, previousSlot, oldTyped, newTyped⟩

/-- Once the source and checked Core right-hand sides agree, assignment to a
local or an unshadowed global reaches the same represented store in both
semantics. The Core runtime typing premise follows from the source sorts. -/
theorem assignment_agrees (state : State) (reference : Variable)
    (rhs : Expression) (coreRhs : Core.Expression.Expr)
    (metadata : Imperative.MetaData Core.Expression) (target : Core.CoreStore)
    {previous value : Value} {oldExpr newExpr : Core.Expression.Val}
    (slot : state.lookup reference = some previous)
    (unshadowed : ∀ name, reference = .global name → state.locals.lookup name = none)
    (evaluated : rhs state = .ok value) (sameType : previous.sort = value.sort)
    (oldRep : coreValue? previous = some oldExpr) (newRep : coreValue? value = some newExpr)
    (coreEvaluated : Core.Expression.eval coreRuntimeFactory (coreStore state) coreRhs = some newExpr) :
    (∃ final, (Computation.assign reference rhs).run state (.returned () final) ∧
      coreStore final = target) ↔
    Imperative.EvalCmdE Core.Expression coreRuntimeFactory (coreStore state)
      (.set reference.coreIdent (.det coreRhs) metadata) target [] := by
  obtain ⟨updated, typed⟩ := coreAssignment_update state reference slot unshadowed sameType oldRep newRep
  rw [coreSet_store_iff metadata coreEvaluated updated typed]
  constructor
  · rintro ⟨final, ran, rfl⟩
    have eq := (assign_run_iff slot evaluated sameType).mp ran
    cases eq
    rfl
  · rintro rfl
    exact ⟨state.update reference value, (assign_run_iff slot evaluated sameType).mpr rfl, rfl⟩

/-- A Core havoc can choose any reified Boole value of the slot's sort and
reach exactly the resulting Boole store. -/
theorem havoc_reified (state : State) (reference : Variable)
    (metadata : Imperative.MetaData Core.Expression)
    {previous value : Value} {oldExpr newExpr : Core.Expression.Val}
    (slot : state.lookup reference = some previous)
    (unshadowed : ∀ name, reference = .global name → state.locals.lookup name = none)
    (sameType : previous.sort = value.sort)
    (oldRep : coreValue? previous = some oldExpr) (newRep : coreValue? value = some newExpr) :
    Imperative.EvalCmdE Core.Expression coreRuntimeFactory (coreStore state)
      (.set reference.coreIdent .nondet metadata) (coreStore (state.update reference value)) [] := by
  obtain ⟨updated, typed⟩ := coreAssignment_update state reference slot unshadowed sameType oldRep newRep
  exact .eval_set_nondet updated typed (Core.coreEvaluator_WellFormedSemanticEvalVar coreRuntimeFactory)

/-- Replay a Core havoc on the corresponding scalar Boole slot, keeping the
exact value chosen by Core and preserving the other Core slots. -/
theorem havoc_replays_choice (state : State) (reference : Variable) (priorValue : Value)
    (metadata : Imperative.MetaData Core.Expression) (store final : Core.CoreStore)
    {previous : Core.Expression.Val}
    (sourceSlot : state.lookup reference = some priorValue)
    (targetSlot : store reference.coreIdent = some previous)
    (encoded : coreValue? priorValue = some previous)
    (run : Imperative.EvalCmdE Core.Expression coreRuntimeFactory store
      (.set reference.coreIdent .nondet metadata) final []) :
    ∃ chosen value,
      final reference.coreIdent = some chosen ∧
      (∀ id, id ≠ reference.coreIdent → final id = store id) ∧
      coreValue? value = some chosen ∧
      (Computation.havoc reference priorValue.sort).run state
        (.returned () (state.update reference value)) := by
  match run with
  | .eval_set_nondet (v := chosen) updated sameType _ =>
    obtain ⟨old, ty, oldSlot, oldTyped, newTyped⟩ := sameType
    rw [targetSlot] at oldSlot
    obtain rfl := Option.some.inj oldSlot
    have sameSort := Option.some.inj (oldTyped.2.symm.trans newTyped.2)
    obtain ⟨value, valueSort, representation⟩ :=
      coreTypedChoice_reifies encoded chosen newTyped.1 sameSort.symm
    have ⟨written, unchanged⟩ :
        final reference.coreIdent = some chosen ∧
        (∀ id, id ≠ reference.coreIdent → final id = store id) :=
      match updated with
      | .update _ result untouched => ⟨result, fun id different => untouched id (Ne.symm different)⟩
    refine ⟨chosen, value, written, unchanged, representation, ?_⟩
    unfold Computation.havoc
    apply (Computation.run_bind _ _ _ _).mpr
    left
    exact ⟨value, state, ⟨value, valueSort, rfl⟩,
      (assign_run_iff sourceSlot rfl valueSort.symm).mpr rfl⟩

/-- Installing a fresh Boole local corresponds to initializing the same
Core slot. Freshness includes the names of saved snapshots. -/
private theorem coreInit_local (state : State) (name : String) (value : Value)
    {literal : Core.Expression.Val}
    (absent : coreStore state ⟨name, ()⟩ = none)
    (localAbsent : state.locals.lookup name = none)
    (represented : coreValue? value = some literal) :
    Imperative.InitState (P := Core.Expression) (coreStore state) ⟨name, ()⟩ literal
      (coreStore { state with locals := state.locals ++ [(name, value)] }) := by
  refine .init absent ?_ ?_
  · apply (coreStore_of_local _ _ _ _).trans represented
    simp [Store.lookup_append, Store.lookup_cons, localAbsent]
  · rintro ⟨other, ⟨⟩⟩ different
    have names : name ≠ other := by
      intro same
      subst other
      exact different rfl
    simp [coreStore, Store.lookup_append, Store.lookup_cons, names]

private theorem declare_runs_with_value (state : State) (binding : Binding) (value : Value)
    (initializer : Option Expression)
    (localAbsent : state.locals.lookup binding.name = none)
    (sameType : value.sort = binding.sort)
    (chosen : (match initializer with
      | none => Computation.choose binding.sort
      | some expression => Computation.evaluate expression).run state (.returned value state)) :
    (Computation.declare binding initializer).run state
      (.returned () { state with locals := state.locals ++ [(binding.name, value)] }) := by
  unfold Computation.declare
  apply (Computation.run_bind _ _ _ _).mpr
  left
  refine ⟨state, state, rfl, ?_⟩
  simp only [localAbsent, Option.isSome_none, Bool.false_eq_true, ite_false]
  cases initializer <;>
    apply (Computation.run_bind _ _ _ _).mpr <;>
    left <;> exact ⟨value, state, chosen, by simp [sameType]; rfl⟩

/-- A declaration without an initializer can make the same typed scalar
choice in both semantics. The represented store includes the fresh local. -/
theorem declare_nondet_forward (state : State) (binding : Binding) (value : Value)
    (metadata : Imperative.MetaData Core.Expression) (ty : Lambda.LTy)
    {literal : Core.Expression.Val}
    (absent : coreStore state ⟨binding.name, ()⟩ = none)
    (localAbsent : state.locals.lookup binding.name = none)
    (sameType : value.sort = binding.sort)
    (represented : coreValue? value = some literal)
    (typed : Imperative.HasVal.valueOfTy (P := Core.Expression) coreRuntimeFactory literal ty) :
    let final := { state with locals := state.locals ++ [(binding.name, value)] }
    (Computation.declare binding none).run state (.returned () final) ∧
      Imperative.EvalCmdE Core.Expression coreRuntimeFactory (coreStore state)
        (.init ⟨binding.name, ()⟩ ty .nondet metadata) (coreStore final) [] := by
  exact ⟨declare_runs_with_value state binding value none localAbsent sameType ⟨value, sameType, rfl⟩,
    .eval_init_unconstrained (coreInit_local state binding.name value absent localAbsent represented)
      typed (Core.coreEvaluator_WellFormedSemanticEvalVar coreRuntimeFactory)⟩

/-- An initializer that evaluates to the same scalar on both sides installs
the same fresh slot and emits no event. -/
theorem declare_det_forward (state : State) (binding : Binding) (value : Value)
    (initializer : Expression) (coreInitializer : Core.Expression.Expr)
    (metadata : Imperative.MetaData Core.Expression) (ty : Lambda.LTy)
    {literal : Core.Expression.Val}
    (absent : coreStore state ⟨binding.name, ()⟩ = none)
    (localAbsent : state.locals.lookup binding.name = none)
    (sameType : value.sort = binding.sort)
    (represented : coreValue? value = some literal)
    (typed : Imperative.HasVal.valueOfTy (P := Core.Expression) coreRuntimeFactory literal ty)
    (sourceEval : initializer state = .ok value)
    (coreEval : Core.Expression.eval coreRuntimeFactory (coreStore state) coreInitializer = some literal) :
    let final := { state with locals := state.locals ++ [(binding.name, value)] }
    (Computation.declare binding (some initializer)).run state (.returned () final) ∧
      Imperative.EvalCmdE Core.Expression coreRuntimeFactory (coreStore state)
        (.init ⟨binding.name, ()⟩ ty (.det coreInitializer) metadata) (coreStore final) [] := by
  refine ⟨declare_runs_with_value state binding value (some initializer) localAbsent sameType ?_,
    .eval_init coreEval (coreInit_local state binding.name value absent localAbsent represented)
      typed (Core.coreEvaluator_WellFormedSemanticEvalVar coreRuntimeFactory)⟩
  simp [Computation.evaluate, sourceEval]

/-- Passing checks compose across consecutive segments of an execution trace.
This is the same elementary trace fact used by the v1 adequacy development. -/
theorem coreChecksPass_append (first second : Imperative.Trace Core.Expression) :
    coreChecksPass (first ++ second) ↔ coreChecksPass first ∧ coreChecksPass second := by
  constructor
  · intro passing
    exact ⟨fun event present => passing event (List.mem_append_left second present),
      fun event present => passing event (List.mem_append_right first present)⟩
  · rintro ⟨prefixPasses, suffixPasses⟩ event present
    rcases List.mem_append.mp present with inPrefix | inSuffix
    · exact prefixPasses event inPrefix
    · exact suffixPasses event inSuffix

@[local simp] private theorem empty_lookup (name : String) :
    Store.lookup ([] : Store) name = none := rfl

/-- Closing a Boole scope and projecting a Core store keep exactly the entry
slots. Globals and snapshots keep their domain, and new locals occupy fresh
Core names. -/
theorem coreStore_scope (entry final : State)
    (entryLocals : ∀ name value, entry.locals.lookup name = some value →
      (coreValue? value).isSome = true)
    (baseDomain : ∀ id,
      (coreStore { entry with locals := [] } id).isSome =
      (coreStore { final with locals := [] } id).isSome)
    (newLocal : ∀ name value, entry.locals.lookup name = none →
      final.locals.lookup name = some value → coreStore entry ⟨name, ()⟩ = none) :
    coreStore { final with locals := final.locals.restrict entry.locals } =
      Imperative.projectStore (coreStore entry) (coreStore final) := by
  funext id
  obtain ⟨name, ⟨⟩⟩ := id
  cases before : entry.locals.lookup name with
  | some value =>
    have represented := entryLocals name value before
    simp [Imperative.projectStore, coreStore, Store.lookup_restrict, before, represented]
  | none =>
    let id : Core.CoreIdent := ⟨name, ()⟩
    have same : (coreStore entry id).isSome = (coreStore { final with locals := [] } id).isSome := by
      simpa [coreStore, id, before] using baseDomain id
    have cleared : coreStore { final with locals := final.locals.restrict entry.locals } id =
        coreStore { final with locals := [] } id := by
      simp [coreStore, id, Store.lookup_restrict, before]
    change coreStore { final with locals := final.locals.restrict entry.locals } id =
      Imperative.projectStore (coreStore entry) (coreStore final) id
    rw [cleared, Imperative.projectStore, same]
    cases after : final.locals.lookup name with
    | none =>
      have identical : coreStore final id = coreStore { final with locals := [] } id := by
        simp [coreStore, id, after]
      rw [identical]
      cases coreStore { final with locals := [] } id <;> rfl
    | some value =>
      have absent := newLocal name value before after
      have noBase : coreStore { final with locals := [] } id = none := by
        cases base : coreStore { final with locals := [] } id with
        | none => rfl
        | some _ => simp [base, show coreStore entry id = none from absent] at same
      simp [noBase]

/-- A Boolean assertion's source outcome is determined by its condition. -/
private theorem assertion_run_iff {state : State} {label : String} {condition : Expression}
    {result : Bool} {outcome : Outcome Unit}
    (evaluated : condition state = .ok (.bool result)) :
    (Computation.assertion label condition).run state outcome ↔
      outcome = if result then .returned () state else .assertionFailed label state := by
  cases result <;>
    simp [Computation.assertion, Computation.test, Computation.run_bind, Computation.evaluate,
      evaluated, Computation.pure, Value.bool, and_assoc]

/-- If the condition evaluations agree, a Boole assertion outcome gives a
Core step emitting the same Boolean check at the represented store. A return
gives a passing trace, and a failure gives a trace ending with a false check. -/
theorem assertion_forward (procedures : String → Option Core.Procedure)
    (state : State) (sourceLabel targetLabel : String) (sourceCondition : Expression)
    (targetCondition : Core.Expression.Expr) (metadata : Imperative.MetaData Core.Expression)
    (result : Bool) (outcome : Outcome Unit)
    (sourceEval : sourceCondition state = .ok (.bool result))
    (coreEval : Core.Expression.eval coreRuntimeFactory (coreStore state) targetCondition =
      some (if result then Imperative.HasBool.ttVal coreRuntimeFactory
        else Imperative.HasBool.ffVal coreRuntimeFactory))
    (run : (Computation.assertion sourceLabel sourceCondition).run state outcome) :
    let entry : Imperative.Env Core.Expression := ⟨coreStore state, coreRuntimeFactory⟩
    let check : Imperative.EventArg Core.Expression :=
      ⟨coreRuntimeFactory, coreStore state, targetLabel, targetCondition, metadata⟩
    Core.CoreStepE procedures (.stmt (.cmd (.cmd (.assert targetLabel targetCondition metadata))) entry)
      [.assert check] (.terminal entry) ∧
      match outcome with
      | .returned () _ => coreChecksPass [.assert check]
      | .assertionFailed _ _ =>
          Core.Expression.eval check.factory check.store check.expr = some (Imperative.HasBool.ffVal check.factory)
      | _ => False := by
  have determined := (assertion_run_iff sourceEval).mp run
  dsimp only
  constructor
  · exact .step_cmd (Core.EvalCommandE.cmd_sem .eval_assert)
  · cases result <;> subst outcome
    · exact coreEval
    · simpa [coreChecksPass] using coreEval

/-! ## Forward composition -/

noncomputable def coreEnv (state : State) : Imperative.Env Core.Expression :=
  ⟨coreStore state, coreRuntimeFactory⟩

/-- An operational witness for a finite Boole outcome. Normal returns and exits
preserve the represented final state. For assertion failure, Core need only
reach the failing check after a passing prefix. Runtime errors are outside
the observations compared here. -/
def CoreForwardOutcome (procedures : String → Option Core.Procedure)
    (start : Core.CoreConfig) : Outcome Unit → Prop
  | .returned () final =>
      ∃ trace, Core.CoreStepStarE procedures start trace (.terminal (coreEnv final)) ∧
        coreChecksPass trace
  | .exited label final =>
      ∃ trace, Core.CoreStepStarE procedures start trace (.exiting label (coreEnv final)) ∧
        coreChecksPass trace
  | .assertionFailed _ _ =>
      ∃ priorTrace check reached,
        Core.CoreStepStarE procedures start (priorTrace ++ [.assert check]) reached ∧
        coreChecksPass priorTrace ∧
        Core.Expression.eval check.factory check.store check.expr = some (Imperative.HasBool.ffVal check.factory)
  | .stuck .. => True

private theorem forward_prepend {procedures : String → Option Core.Procedure}
    {start next : Core.CoreConfig} {priorTrace : Imperative.Trace Core.Expression} {outcome : Outcome Unit}
    (before : Core.CoreStepStarE procedures start priorTrace next) (passing : coreChecksPass priorTrace)
    (after : CoreForwardOutcome procedures next outcome) :
    CoreForwardOutcome procedures start outcome := by
  cases outcome with
  | returned result state =>
    cases result
    obtain ⟨trace, ran, checks⟩ := after
    exact ⟨priorTrace ++ trace, ReflTransTrace.trans _ before ran,
      (coreChecksPass_append _ _).mpr ⟨passing, checks⟩⟩
  | exited label state =>
    obtain ⟨trace, ran, checks⟩ := after
    exact ⟨priorTrace ++ trace, ReflTransTrace.trans _ before ran,
      (coreChecksPass_append _ _).mpr ⟨passing, checks⟩⟩
  | assertionFailed label state =>
    obtain ⟨trace, check, reached, ran, checks, failed⟩ := after
    exact ⟨priorTrace ++ trace, check, reached,
      by simpa only [List.append_assoc] using ReflTransTrace.trans _ before ran,
      (coreChecksPass_append _ _).mpr ⟨passing, checks⟩, failed⟩
  | stuck => exact True.intro

private theorem forward_admin {procedures : String → Option Core.Procedure}
    {start next : Core.CoreConfig} {outcome : Outcome Unit}
    (step : Core.CoreStepE procedures start [] next)
    (rest : CoreForwardOutcome procedures next outcome) :
    CoreForwardOutcome procedures start outcome := by
  apply forward_prepend (priorTrace := []) ?_ (by simp [coreChecksPass]) rest
  simpa using ReflTransTrace.step _ _ _ _ _ step (.refl next)

private theorem forward_singleton {procedures : String → Option Core.Procedure}
    {statement : Core.Statement} {entry : Imperative.Env Core.Expression} {outcome : Outcome Unit}
    (run : CoreForwardOutcome procedures (.stmt statement entry) outcome) :
    CoreForwardOutcome procedures (.stmts [statement] entry) outcome := by
  cases outcome with
  | returned result state =>
    cases result
    obtain ⟨trace, ran, checks⟩ := run
    exact ⟨trace, Imperative.stmtRun_to_singletonE _ ran, checks⟩
  | exited label state =>
    obtain ⟨trace, ran, checks⟩ := run
    refine ⟨trace, ?_, checks⟩
    have head := Core.stmt_run_to_singleton_runE ran
    simpa using ReflTransTrace.trans _ head
      (show Core.CoreStepStarE procedures (.seq (.exiting label (coreEnv state)) []) []
        (.exiting label (coreEnv state)) from by
          simpa using ReflTransTrace.step _ _ _ _ _ .step_seq_exit (.refl _))
  | assertionFailed label state =>
    obtain ⟨trace, check, reached, ran, checks, failed⟩ := run
    exact ⟨trace, check, _, Core.stmt_run_to_singleton_runE ran, checks, failed⟩
  | stuck => exact True.intro

private theorem forward_seq_return {procedures : String → Option Core.Procedure}
    {first : Core.CoreConfig} {rest : List Core.Statement} {middle : State} {outcome : Outcome Unit}
    (ran : CoreForwardOutcome procedures first (.returned () middle))
    (continued : CoreForwardOutcome procedures (.stmts rest (coreEnv middle)) outcome) :
    CoreForwardOutcome procedures (.seq first rest) outcome := by
  obtain ⟨trace, run, checks⟩ := ran
  apply forward_prepend (Imperative.seq_inner_starE _ (ss := rest) run) checks
  exact forward_admin .step_seq_done continued

private theorem forward_seq_exit {procedures : String → Option Core.Procedure}
    {first : Core.CoreConfig} {rest : List Core.Statement} {label : String} {state : State}
    (ran : CoreForwardOutcome procedures first (.exited label state)) :
    CoreForwardOutcome procedures (.seq first rest) (.exited label state) := by
  obtain ⟨trace, run, checks⟩ := ran
  apply forward_prepend (Imperative.seq_inner_starE _ (ss := rest) run) checks
  exact forward_admin .step_seq_exit ⟨[], .refl _, by simp [coreChecksPass]⟩

private theorem forward_seq_failure {procedures : String → Option Core.Procedure}
    {first : Core.CoreConfig} {rest : List Core.Statement} {label : String} {state : State}
    (ran : CoreForwardOutcome procedures first (.assertionFailed label state)) :
    CoreForwardOutcome procedures (.seq first rest) (.assertionFailed label state) := by
  obtain ⟨trace, check, reached, run, checks, failed⟩ := ran
  exact ⟨trace, check, _, Imperative.seq_inner_starE _ (ss := rest) run, checks, failed⟩

/-- Adding a suffix preserves each trace through the prefix. If the prefix
finishes normally the new run is poised to start the suffix, and if it exits
the exit is propagated unchanged. -/
private theorem coreStmts_append_prefix {procedures : String → Option Core.Procedure}
    (first rest : List Core.Statement) {env : Imperative.Env Core.Expression}
    {trace : Imperative.Trace Core.Expression} {reached : Core.CoreConfig}
    (run : Core.CoreStepStarE procedures (.stmts first env) trace reached) :
    ∃ next, Core.CoreStepStarE procedures (.stmts (first ++ rest) env) trace next ∧
      (∀ final, reached = .terminal final → next = .stmts rest final) ∧
      (∀ label final, reached = .exiting label final → next = .exiting label final) := by
  induction first generalizing env trace reached with
  | nil =>
    obtain ⟨rfl, place⟩ := Imperative.stmts_nil_runE _ run
    rcases place with rfl | rfl <;>
      exact ⟨_, .refl _, by simp, by simp⟩
  | cons statement tail ih =>
    rcases Imperative.stmts_cons_headE _ run with ⟨rfl, rfl⟩ | inSeq
    · exact ⟨_, .refl _, by simp, by simp⟩
    rcases Imperative.seq_run_decomposeE _ inSeq with
      ⟨inner, rfl, inHead⟩ | ⟨middle, headTrace, tailTrace, rfl, headRun, tailRun⟩ |
      ⟨label, final, rfl, exitRun⟩
    · exact ⟨_, by
        simpa using ReflTransTrace.step _ [] _ _ _ .step_stmts_cons
          (Imperative.seq_inner_starE _ (ss := tail ++ rest) inHead), by simp, by simp⟩
    · obtain ⟨next, liftedTail, returned, exited⟩ := ih tailRun
      have liftedHead := Imperative.stmts_cons_stepE _ statement (tail ++ rest) _ _ headRun
      exact ⟨next, ReflTransTrace.trans _ liftedHead liftedTail, returned, exited⟩
    · have lifted := Imperative.seq_inner_starE _ (ss := tail ++ rest) exitRun
      have entered : Core.CoreStepStarE procedures (.stmts (statement :: (tail ++ rest)) env)
          trace (.seq (.exiting label final) (tail ++ rest)) := by
        simpa using ReflTransTrace.step _ [] _ _ _ .step_stmts_cons lifted
      have finished : Core.CoreStepStarE procedures (.seq (.exiting label final) (tail ++ rest))
          [] (.exiting label final) :=
        .step _ [] _ [] _ .step_seq_exit (.refl _)
      exact ⟨_, by simpa using ReflTransTrace.trans _ entered finished, by simp, by simp⟩

/-- The matching forward witnesses for two computations compose when their
Core statement lists are concatenated. The suffix runs only after a return
from the prefix. The prefix can itself represent multiple Core statements. -/
theorem sequence_forward (procedures : String → Option Core.Procedure)
    (first rest : Computation (model := .builtins) Unit)
    (firstStatements restStatements : List Core.Statement)
    (firstAgrees : ∀ state outcome, first.run state outcome →
      CoreForwardOutcome procedures (.stmts firstStatements (coreEnv state)) outcome)
    (restAgrees : ∀ state outcome, rest.run state outcome →
      CoreForwardOutcome procedures (.stmts restStatements (coreEnv state)) outcome)
    {entry : State} {outcome : Outcome Unit}
    (ran : (first >>= fun _ => rest).run entry outcome) :
    CoreForwardOutcome procedures (.stmts (firstStatements ++ restStatements) (coreEnv entry))
      outcome := by
  rcases (Computation.run_bind _ _ _ _).mp ran with
    ⟨⟨⟩, middle, firstRun, restRun⟩ | ⟨label, final, firstRun, rfl⟩ |
    ⟨label, final, firstRun, rfl⟩ | ⟨_, _, _, rfl⟩
  · obtain ⟨trace, witness, passing⟩ := firstAgrees _ _ firstRun
    obtain ⟨next, extended, returns, _⟩ := coreStmts_append_prefix _ _ witness
    rw [returns _ rfl] at extended
    exact forward_prepend extended passing (restAgrees _ _ restRun)
  · obtain ⟨trace, witness, passing⟩ := firstAgrees _ _ firstRun
    obtain ⟨next, extended, _, exits⟩ := coreStmts_append_prefix _ _ witness
    rw [exits _ _ rfl] at extended
    exact ⟨trace, extended, passing⟩
  · obtain ⟨prior, check, reached, witness, passing, failed⟩ := firstAgrees _ _ firstRun
    obtain ⟨next, extended, _, _⟩ := coreStmts_append_prefix _ _ witness
    exact ⟨prior, check, next, extended, passing, failed⟩
  · exact True.intro

/-- Lift a body witness through a Core scope. A matching label consumes an
exit, and a failing assertion remains observable while inside the scope. -/
theorem scope_forward (procedures : String → Option Core.Procedure)
    (label : Option String) (entry : State) (statements : List Core.Statement)
    (inner : Outcome Unit)
    (run : CoreForwardOutcome procedures (.stmts statements (coreEnv entry)) inner)
    (project : coreStore { inner.state with locals := inner.state.locals.restrict entry.locals } =
      Imperative.projectStore (coreStore entry) (coreStore inner.state)) :
    CoreForwardOutcome procedures (.block label (coreStore entry) (.stmts statements (coreEnv entry)))
      (match inner.mapState (fun state => { state with locals := state.locals.restrict entry.locals }) with
        | .exited name state => if label = some name then .returned () state else .exited name state
        | outcome => outcome) := by
  cases inner with
  | returned result final =>
    cases result
    simp only [Outcome.state] at project
    obtain ⟨trace, ran, passing⟩ := run
    apply forward_prepend (Imperative.block_inner_starE (label := label) (σ_parent := coreStore entry) ran) passing
    refine forward_admin .step_block_done ?_
    simp only [Outcome.mapState, CoreForwardOutcome]
    exact ⟨[], by simpa only [coreEnv, project] using
      (ReflTransTrace.refl (r := Core.CoreStepE procedures) (.terminal ({ coreEnv final with
        store := Imperative.projectStore (coreStore entry) (coreStore final) }))), by simp [coreChecksPass]⟩
  | exited name final =>
    simp only [Outcome.state] at project
    obtain ⟨trace, ran, passing⟩ := run
    apply forward_prepend (Imperative.block_inner_starE (label := label) (σ_parent := coreStore entry) ran) passing
    simp only [Outcome.mapState]
    split
    · rename_i same
      refine forward_admin (.step_block_exit_match same) ?_
      exact ⟨[], by simpa only [coreEnv, project] using
        (ReflTransTrace.refl (r := Core.CoreStepE procedures) (.terminal ({ coreEnv final with
          store := Imperative.projectStore (coreStore entry) (coreStore final) }))), by simp [coreChecksPass]⟩
    · rename_i different
      refine forward_admin (.step_block_exit_mismatch different) ?_
      exact ⟨[], by simpa only [coreEnv, project] using
        (ReflTransTrace.refl (r := Core.CoreStepE procedures) (.exiting name ({ coreEnv final with
          store := Imperative.projectStore (coreStore entry) (coreStore final) }))), by simp [coreChecksPass]⟩
  | assertionFailed name final =>
    obtain ⟨trace, check, reached, ran, passing, failed⟩ := run
    exact ⟨trace, check, _, Imperative.block_inner_starE (label := label) (σ_parent := coreStore entry) ran,
      passing, failed⟩
  | stuck => exact True.intro


/-- A source assumption that returns produces a passing Core assumption event
at the represented entry state. A false source assumption has no outcome. -/
theorem assumption_forward (procedures : String → Option Core.Procedure)
    (state : State) (condition : Expression) (coreCondition : Core.Expression.Expr)
    (label : String) (metadata : Imperative.MetaData Core.Expression)
    (result : Bool) (outcome : Outcome Unit)
    (sourceEval : condition state = .ok (.bool result))
    (targetEval : Core.Expression.eval coreRuntimeFactory (coreStore state) coreCondition =
      some (if result then Imperative.HasBool.ttVal coreRuntimeFactory
        else Imperative.HasBool.ffVal coreRuntimeFactory))
    (run : (Computation.assumption condition).run state outcome) :
    CoreForwardOutcome procedures
      (.stmt (.cmd (.cmd (.assume label coreCondition metadata))) (coreEnv state)) outcome := by
  have returned : result = true ∧ outcome = .returned () state := by
    cases result
    · simp [Computation.assumption, Computation.test, Computation.run_bind, Computation.evaluate,
        sourceEval, Computation.pure, Value.bool, and_assoc] at run
    · simpa [Computation.assumption, Computation.test, Computation.run_bind, Computation.evaluate,
        sourceEval, Computation.pure, Value.bool, and_assoc] using run
  obtain ⟨rfl, rfl⟩ := returned
  let check : Imperative.EventArg Core.Expression :=
    ⟨coreRuntimeFactory, coreStore state, label, coreCondition, metadata⟩
  refine ⟨[.assume check], ?_, ?_⟩
  · have step : Core.CoreStepE procedures
        (.stmt (.cmd (.cmd (.assume label coreCondition metadata))) (coreEnv state))
        [.assume check] (.terminal (coreEnv state)) :=
      .step_cmd (Core.EvalCommandE.cmd_sem .eval_assume)
    simpa only [List.append_nil] using ReflTransTrace.step _ _ _ _ _ step (.refl _)
  · simpa [check, coreChecksPass] using targetEval

/-- A deterministic Core guard must evaluate to the chosen Boolean.
A nondeterministic guard allows either choice. -/
def coreGuardAllows (guard : Imperative.ExprOrNondet Core.Expression) (state : State)
    (result : Bool) : Prop :=
  match guard with
  | .nondet => True
  | .det expression => Core.Expression.eval coreRuntimeFactory (coreStore state) expression =
      some (if result then Imperative.HasBool.ttVal coreRuntimeFactory
        else Imperative.HasBool.ffVal coreRuntimeFactory)


/-- Once the source guard and both branch bodies have operational witnesses,
the Core conditional takes the corresponding branch and preserves its outcome. -/
theorem branch_forward (procedures : String → Option Core.Procedure)
    (guard : Computation (model := .builtins) Bool)
    (yes no : Computation (model := .builtins) Unit)
    (targetGuard : Imperative.ExprOrNondet Core.Expression)
    (targetYes targetNo : List Core.Statement) (metadata : Imperative.MetaData Core.Expression)
    {initial : State} {outcome : Outcome Unit}
    (guardAgrees : ∀ result, guard.run initial result →
      (∃ taken, result = .returned taken initial ∧ coreGuardAllows targetGuard initial taken) ∨
      ∃ reason, result = .stuck reason initial)
    (yesAgrees : yes.run initial outcome →
      CoreForwardOutcome procedures (.block none (coreStore initial) (.stmts targetYes (coreEnv initial))) outcome)
    (noAgrees : no.run initial outcome →
      CoreForwardOutcome procedures (.block none (coreStore initial) (.stmts targetNo (coreEnv initial))) outcome)
    (ran : (guard >>= fun taken => if taken then yes else no).run initial outcome) :
    CoreForwardOutcome procedures (.stmt (.ite targetGuard targetYes targetNo metadata) (coreEnv initial))
      outcome := by
  rcases (Computation.run_bind _ _ _ _).mp ran with
    ⟨taken, middle, tested, chosen⟩ | ⟨_, _, tested, rfl⟩ |
    ⟨_, _, tested, rfl⟩ | ⟨_, _, tested, rfl⟩
  · rcases guardAgrees _ tested with ⟨other, equal, agrees⟩ | ⟨_, impossible⟩
    · obtain ⟨rfl, rfl⟩ := Outcome.returned.inj equal
      cases taken
      · apply forward_admin _ (noAgrees chosen)
        cases targetGuard
        · exact .step_ite_false agrees
        · exact .step_ite_nondet_false
      · apply forward_admin _ (yesAgrees chosen)
        cases targetGuard
        · exact .step_ite_true agrees
        · exact .step_ite_nondet_true
    · contradiction
  · rcases guardAgrees _ tested with ⟨_, impossible, _⟩ | ⟨_, impossible⟩ <;> contradiction
  · rcases guardAgrees _ tested with ⟨_, impossible, _⟩ | ⟨_, impossible⟩ <;> contradiction
  · exact True.intro

/-- A Boole loop outcome has a Core operational witness if its guard matches
Core's and each execution of the scoped body has a corresponding witness.
This includes failure during an iteration even when the loop never returns. -/
theorem loop_forward (procedures : String → Option Core.Procedure)
    (guard : Computation (model := .builtins) Bool) (body : Computation (model := .builtins) Unit)
    (targetGuard : Imperative.ExprOrNondet Core.Expression) (measure : Option Core.Expression.Expr)
    (invariants : List (String × Core.Expression.Expr)) (targetBody : List Core.Statement)
    (metadata : Imperative.MetaData Core.Expression)
    (guardAgrees : ∀ state outcome, guard.run state outcome →
      (∃ result, outcome = .returned result state ∧ coreGuardAllows targetGuard state result) ∨
      ∃ reason, outcome = .stuck reason state)
    (bodyAgrees : ∀ state outcome, body.run state outcome →
      CoreForwardOutcome procedures (.block none (coreStore state) (.stmts targetBody (coreEnv state))) outcome)
    {initial : State} {outcome : Outcome Unit}
    (ran : Computation.Iteration guard body initial outcome) :
    CoreForwardOutcome procedures
      (.stmt (.loop targetGuard measure invariants targetBody metadata) (coreEnv initial)) outcome := by
  let loop : Core.Statement := .loop targetGuard measure invariants targetBody metadata
  have guardReturn {state final : State} {result : Bool}
      (ran : guard.run state (.returned result final)) :
      final = state ∧ coreGuardAllows targetGuard state result := by
    rcases guardAgrees _ _ ran with ⟨value, same, matched⟩ | ⟨reason, impossible⟩
    · obtain ⟨sameValue, sameState⟩ := Outcome.returned.inj same
      subst value
      subst final
      exact ⟨rfl, matched⟩
    · contradiction
  have enter {state : State}
      (yes : coreGuardAllows targetGuard state true) :
      Core.CoreStepE procedures
        (.stmt loop (coreEnv state)) []
        (.seq (.block none (coreStore state) (.stmts targetBody (coreEnv state))) [loop]) := by
    cases targetGuard
    · exact .step_loop_enter yes
    · exact .step_loop_nondet_enter
  change CoreForwardOutcome procedures (.stmt loop (coreEnv initial)) outcome
  induction ran with
  | stop checked =>
    obtain ⟨rfl, no⟩ := guardReturn checked
    apply forward_admin
    · cases targetGuard
      · exact .step_loop_exit no
      · exact .step_loop_nondet_exit
    · exact ⟨[], .refl _, by simp [coreChecksPass]⟩
  | next checked bodyRan _ ih =>
    obtain ⟨rfl, yes⟩ := guardReturn checked
    exact forward_admin (enter yes)
      (forward_seq_return (bodyAgrees _ _ bodyRan) (forward_singleton ih))
  | guardExit checked =>
    rcases guardAgrees _ _ checked with ⟨_, impossible, _⟩ | ⟨_, impossible⟩ <;> contradiction
  | guardFailure checked =>
    rcases guardAgrees _ _ checked with ⟨_, impossible, _⟩ | ⟨_, impossible⟩ <;> contradiction
  | guardStuck => exact True.intro
  | bodyExit checked bodyRan =>
    obtain ⟨rfl, yes⟩ := guardReturn checked
    exact forward_admin (enter yes) (forward_seq_exit (bodyAgrees _ _ bodyRan))
  | bodyFailure checked bodyRan =>
    obtain ⟨rfl, yes⟩ := guardReturn checked
    exact forward_admin (enter yes) (forward_seq_failure (bodyAgrees _ _ bodyRan))
  | bodyStuck => exact True.intro

end Strata.Boole
