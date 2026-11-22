/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.ExpressionExecution
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.ExpressionExecution
public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.Entry
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Entry
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Statements
import all StrataBoole.Boole.Interpretation.Denotational.CoreReference
import all StrataBoole.Boole.Interpretation.Legacy.Runtime
import all StrataBoole.Boole.Interpretation.Runtime
import Strata.Util.HMaps
import Strata.DL.Imperative.CmdSemanticsProps
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Expressions

public section

namespace Strata.Boole

/-- The source declarations specify exactly the names and sorts of the
runtime slots. Snapshots have a separate domain fixed at procedure entry. -/
def SourceSlotsTyped (bindings : List Binding) (store : Store) : Prop :=
  ∀ name, (store.lookup name).map Value.sort =
    (bindings.find? (fun binding => binding.name == name)).map Binding.sort

/-- The runtime portion of the invariant for the statement induction. -/
structure ExecutionStateTyped (scope : Scope) (scopes : Core.TypeSpec.TypeScopes)
    (state : State) : Prop where
  locals : SourceSlotsTyped scope.locals state.locals
  globals : SourceSlotsTyped scope.globals state.globals
  snapshots : SourceSlotsTyped
    (scope.globals.filter fun binding => scope.modifies.contains binding.name) state.snapshots
  core : ScalarStoreTyped scopes state

private theorem slotType_update (store : Store) (name : String) (previous value : Value)
    (old : store.lookup name = some previous) (sort : value.sort = previous.sort) :
    ∀ observed, ((store.update name value).lookup observed).map Value.sort =
      (store.lookup observed).map Value.sort := by
  intro observed
  by_cases same : observed = name
  · subst observed
    rw [Store.lookup_update, old]
    simp [sort]
  · rw [Store.lookup_update_other _ _ _ _ same]

/-- A type-correct assignment preserves the source names and their sorts. -/
theorem sourceSlots_update {bindings : List Binding} {store : Store} {name : String}
    {previous value : Value} (typed : SourceSlotsTyped bindings store)
    (old : store.lookup name = some previous) (sort : value.sort = previous.sort) :
    SourceSlotsTyped bindings (store.update name value) := by
  intro observed
  rw [slotType_update store name previous value old sort]
  exact typed observed

/-- Extension by a fresh typed declaration preserves the slot correspondence. -/
theorem sourceSlots_append {bindings : List Binding} {store : Store}
    {binding : Binding} {value : Value} (typed : SourceSlotsTyped bindings store)
    (fresh : store.lookup binding.name = none) (sort : value.sort = binding.sort) :
    SourceSlotsTyped (bindings ++ [binding]) (store ++ [(binding.name, value)]) := by
  intro name
  rw [Store.lookup_append, List.find?_append]
  by_cases same : binding.name = name
  · subst name
    have absent : bindings.find? (fun b => b.name == binding.name) = none := by
      have noType := typed binding.name
      rw [fresh] at noType
      cases found : bindings.find? (fun b => b.name == binding.name) <;> simp_all
    simp [fresh, absent, Store.lookup_cons, sort]
  · simpa [Store.lookup_cons, same, beq_iff_eq] using typed name

/-- The Core store part of the invariant depends only on scope lookup. -/
theorem scalarStoreTyped_scopeEquiv {scopes other : Core.TypeSpec.TypeScopes}
    {state : State} (equiv : Strata.Util.HMaps.Equiv other scopes)
    (typed : ScalarStoreTyped scopes state) : ScalarStoreTyped other state := by
  intro id ty found
  exact typed id ty ((equiv.find? id).symm.trans found)

/-- A represented update of the same sort preserves the runtime invariant,
including the types required by the declarative Core scopes. -/
theorem executionStateTyped_update {scope : Scope} {scopes : Core.TypeSpec.TypeScopes}
    {state : State} {reference : Variable} {previous value : Value}
    {old new : Core.Expression.Val}
    (typed : ExecutionStateTyped scope scopes state)
    (found : state.lookup reference = some previous)
    (sameSort : previous.sort = value.sort)
    (unshadowed : ∀ name, reference = .global name → state.locals.lookup name = none)
    (oldRep : coreValue? previous = some old) (newRep : coreValue? value = some new) :
    ExecutionStateTyped scope scopes (state.update reference value) := by
  obtain ⟨update, storedType⟩ :=
    coreAssignment_update state reference found unshadowed sameSort oldRep newRep
  have nextCore : ScalarStoreTyped scopes (state.update reference value) := by
    intro id ty declared
    obtain ⟨represented, slot, sort⟩ := typed.core id ty declared
    have model : represented.tc = coreRuntimeFactory.model.tcInterp := by
      unfold coreStore at slot
      split at slot
      · exact coreValue?_isValue slot
      · split at slot
        · exact coreValue?_isValue slot
        · rw [List.findSome?_eq_some_iff] at slot
          obtain ⟨_, ⟨name, value⟩, _, _, found⟩ := slot
          have encoded : (if id.name == (Core.CoreIdent.mkOld name).name then coreValue? value else none) = some represented := found.1

          split at encoded
          · exact coreValue?_isValue encoded
          · contradiction
    have typedAt : Imperative.HasVal.valueOfTy (P := Core.Expression)
        coreRuntimeFactory represented (.forAll [] ty) :=
      ⟨model, by simp [Lambda.LTy.toMonoType?, sort]⟩
    obtain ⟨result, resultSlot, resultType⟩ :=
      Imperative.UpdateState_typedAt update storedType ⟨represented, slot, typedAt⟩
    exact ⟨result, resultSlot, (Option.some.inj resultType.2).symm⟩
  cases reference with
  | «local» name =>
    exact ⟨sourceSlots_update typed.locals found sameSort.symm, typed.globals, typed.snapshots, nextCore⟩
  | global name =>
    exact ⟨typed.locals, sourceSlots_update typed.globals found sameSort.symm, typed.snapshots, nextCore⟩

/-- Extending the lexical and Core scopes by a fresh binding preserves
the runtime invariant for the enlarged state. -/
theorem executionStateTyped_declare
    {scope : Scope} {scopes next : Core.TypeSpec.TypeScopes} {state : State}
    {binding : Binding} {value : Value} {ty : Lambda.LMonoTy} {literal : Core.Expression.Val}
    (typed : ExecutionStateTyped scope scopes state)
    (freshLocal : state.locals.lookup binding.name = none)
    (sort : value.sort = binding.sort)
    (reified : coreValue? value = some literal) (literalSort : literal.sort.toMonoTy = ty)
    (nextScopes : Strata.Util.HMaps.Equiv next (scopes.insert ⟨binding.name, ()⟩ (.forAll [] ty))) :
    ExecutionStateTyped { scope with locals := scope.locals ++ [binding] } next
      { state with locals := state.locals ++ [(binding.name, value)] } := by
  refine ⟨sourceSlots_append typed.locals freshLocal sort, typed.globals, typed.snapshots, ?_⟩
  apply scalarStoreTyped_scopeEquiv nextScopes
  intro id declared found
  rcases id with ⟨name, ⟨⟩⟩
  by_cases same : name = binding.name
  · subst name
    rw [Strata.Util.HMaps.find?_insert_self] at found
    obtain rfl := Lambda.LTy.forAll.inj (Option.some.inj found) |>.2
    refine ⟨literal, (coreStore_of_local _ _ _ ?_).trans reified, literalSort⟩
    simp [Store.lookup_append, Store.lookup_cons, freshLocal]
  · have different : (⟨name, ()⟩ : Core.CoreIdent) ≠ ⟨binding.name, ()⟩ :=
      fun eq => same (congrArg (·.name) eq)
    rw [Strata.Util.HMaps.find?_insert_ne _ _ _ _ different] at found
    obtain ⟨represented, previous, valueType⟩ := typed.core _ _ found
    refine ⟨represented, ?_, valueType⟩
    simpa [coreStore, Store.lookup_append, Store.lookup_cons, Ne.symm same] using previous

/-- Restricting an extended local store restores the original lexical
domain and keeps the new values of its original slots. -/
theorem sourceSlots_restrict {outer inner : List Binding} {entry final : Store}
    (before : SourceSlotsTyped outer entry) (after : SourceSlotsTyped inner final)
    (keeps : ∀ name binding, outer.find? (fun b => b.name == name) = some binding →
      inner.find? (fun b => b.name == name) = some binding) :
    SourceSlotsTyped outer (final.restrict entry) := by
  intro name
  rw [Store.lookup_restrict]
  cases outerSlot : outer.find? (fun b => b.name == name) with
  | none =>
    have absent := before name
    rw [outerSlot] at absent
    have empty : entry.lookup name = none := by cases lookup : entry.lookup name <;> simp [lookup] at absent ⊢
    simp [empty]
  | some binding =>
    have old := before name
    rw [outerSlot] at old
    have present : (entry.lookup name).isSome = true := by cases lookup : entry.lookup name <;> simp [lookup] at old ⊢
    have same := after name
    rw [keeps name binding outerSlot] at same
    simp [present, same]

/-- A scope exit restores the outer runtime invariant when the inner scope
keeps every outer binding and the two store projections coincide. -/
theorem executionStateTyped_restrict
    {outer inner : Scope} {scopes innerScopes : Core.TypeSpec.TypeScopes}
    {entry final : State}
    (before : ExecutionStateTyped outer scopes entry)
    (after : ExecutionStateTyped inner innerScopes final)
    (globals : inner.globals = outer.globals) (modifies : inner.modifies = outer.modifies)
    (keeps : ∀ name binding, outer.locals.find? (fun b => b.name == name) = some binding →
      inner.locals.find? (fun b => b.name == name) = some binding)
    (coreExtends : ∀ id ty, scopes.find? id = some (.forAll [] ty) →
      innerScopes.find? id = some (.forAll [] ty))
    (projection : coreStore { final with locals := final.locals.restrict entry.locals } =
      Imperative.projectStore (coreStore entry) (coreStore final)) :
    ExecutionStateTyped outer scopes { final with locals := final.locals.restrict entry.locals } := by
  refine ⟨sourceSlots_restrict before.locals after.locals keeps,
    globals ▸ after.globals, ?_, ?_⟩
  · simpa [globals, modifies] using after.snapshots
  · intro id ty declared
    obtain ⟨entryValue, entrySlot, _⟩ := before.core id ty declared
    obtain ⟨finalValue, finalSlot, finalType⟩ := after.core id ty (coreExtends id ty declared)
    exact ⟨finalValue, by simp [projection, Imperative.projectStore, entrySlot, finalSlot], finalType⟩

/-- Positional argument binding realizes the source lexical scope. -/
theorem sourceSlots_bindValues {bindings : List Binding} {values : List Value}
    (typed : valuesMatch bindings values = true) :
    SourceSlotsTyped bindings (bindValues bindings values) := by
  intro name
  induction bindings generalizing values with
  | nil => simp [bindValues]
  | cons binding rest ih =>
    cases values with
    | nil => simp [valuesMatch] at typed
    | cons value values =>
      have ⟨size, firstSort, tailSorts⟩ : rest.length = values.length ∧ binding.sort = value.sort ∧
          (rest.zip values).all (fun (b, v) => b.sort == v.sort) = true := by
        simpa [valuesMatch] using typed
      have tail : valuesMatch rest values = true := by simp [valuesMatch, size, tailSorts]
      change (Store.lookup ((binding.name, value) :: bindValues rest values) name).map Value.sort =
        ((binding :: rest).find? (fun b => b.name == name)).map Binding.sort
      rw [Store.lookup_cons, List.find?_cons]
      by_cases named : binding.name == name
      · simp [named, firstSort]
      · simp [named, ih tail]

/-- Positional inputs and outputs establish the source slots at entry.
The Core portion is supplied by the correspondence of the procedure header. -/
theorem initialState_currentSlots {globals : List Binding} {procedure : ProcedureMeaning}
    (input : Invocation) (outputs : List Value)
    (globalsTyped : valuesMatch globals input.globals = true)
    (inputsTyped : valuesMatch procedure.inputs input.arguments = true)
    (outputsTyped : valuesMatch procedure.outputs outputs = true) :
    SourceSlotsTyped globals (initialState globals procedure input outputs).globals ∧
    SourceSlotsTyped (procedure.inputs ++ procedure.outputs)
      (initialState globals procedure input outputs).locals := by
  refine ⟨sourceSlots_bindValues globalsTyped, ?_⟩
  have inputLength := (valuesMatch_iff _ _).mp inputsTyped |>.1
  change SourceSlotsTyped (procedure.inputs ++ procedure.outputs)
    (bindValues procedure.inputs input.arguments ++ bindValues procedure.outputs outputs)
  rw [← bindValues_append inputLength]
  exact sourceSlots_bindValues (valuesMatch_append inputsTyped outputsTyped)

private theorem sourceSlots_filter {bindings : List Binding} {store : Store}
    (typed : SourceSlotsTyped bindings store) (keep : String → Bool) :
    SourceSlotsTyped (bindings.filter fun b => keep b.name)
      (store.filter fun pair => keep pair.1) := by
  intro name
  have storeFilter (items : Store) :
      Store.lookup (items.filter fun pair => keep pair.1) name =
        if keep name then Store.lookup items name else none := by
    induction items with
    | nil => simp
    | cons pair rest ih =>
      obtain ⟨key, value⟩ := pair
      by_cases named : key = name
      · subst key
        cases kept : keep name <;> simp [kept, Store.lookup_cons, ih]
      · have different : (key == name) = false := beq_eq_false_iff_ne.mpr named
        cases kept : keep key <;> simp [kept, Store.lookup_cons, different, ih]
  have scopeFilter (items : List Binding) :
      (items.filter fun b => keep b.name).find? (fun b => b.name == name) =
        if keep name then items.find? (fun b => b.name == name) else none := by
    induction items with
    | nil => simp
    | cons binding rest ih =>
      by_cases named : binding.name = name
      · cases kept : keep name <;> simp [named, kept, List.find?_cons, ih]
      · have different : (binding.name == name) = false := beq_eq_false_iff_ne.mpr named
        cases kept : keep binding.name <;> simp [kept, List.find?_cons, different, ih]
  rw [storeFilter, scopeFilter]
  cases keep name <;> simp [typed name]

/-- The source half of the execution invariant holds at the actual initial
state, including the old values of precisely the modified globals. -/
theorem initialState_executionStateTyped {globals : List Binding} {procedure : ProcedureMeaning}
    {scope : Scope} {scopes : Core.TypeSpec.TypeScopes}
    (input : Invocation) (outputs : List Value)
    (bodyGlobals : scope.globals = globals)
    (bodyLocals : scope.locals = procedure.inputs ++ procedure.outputs)
    (bodyModifies : scope.modifies = procedure.contract.modifies)
    (globalsTyped : valuesMatch globals input.globals = true)
    (inputsTyped : valuesMatch procedure.inputs input.arguments = true)
    (outputsTyped : valuesMatch procedure.outputs outputs = true)
    (coreTyped : ScalarStoreTyped scopes (initialState globals procedure input outputs)) :
    ExecutionStateTyped scope scopes (initialState globals procedure input outputs) := by
  obtain ⟨globalSlots, localSlots⟩ := initialState_currentSlots input outputs globalsTyped inputsTyped outputsTyped
  refine ⟨bodyLocals ▸ localSlots, bodyGlobals ▸ globalSlots, ?_, coreTyped⟩
  rw [bodyGlobals, bodyModifies]
  exact sourceSlots_filter globalSlots procedure.contract.modifies.contains

end Strata.Boole
