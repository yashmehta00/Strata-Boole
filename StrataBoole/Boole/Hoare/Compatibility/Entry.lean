/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Hoare.Certificate
public import StrataBoole.Boole.Semantics.CoreReference
public import StrataBoole.Boole.Semantics.Adequacy.ExecutionInvariant
import all StrataBoole.Boole.Semantics.Adequacy.ExecutionInvariant
import all StrataBoole.Boole.Semantics.Adequacy.Entry
import StrataBoole.Boole.Semantics.Adequacy.Statements
public import Strata.Languages.Core.Logic.ContractToHoareTripleProps
import Strata.DL.Lambda.LExprDenoteEvalProps
import all Strata.DL.Lambda.Denote.LExprDenote
import all StrataBoole.Boole.Runtime
import all StrataBoole.Boole.Hoare.Certificate
import all StrataBoole.Boole.Hoare.Compile
import all StrataBoole.Boole.Hoare.Rules

public section

namespace Strata.Boole.Hoare

open Core.Logic Imperative

/-- Source-visible bindings represented in the Core store. Output-only slots
can be ignored until their first assignment. Extra Core registers are allowed. -/
structure StoreAgrees (factory : Lambda.Factory Core.CoreLParams) (unwritten : List Core.CoreIdent)
    (source : State) (env : Env Core.Expression) : Prop where
  factory_eq : env.factory.factory = factory
  globals : ∀ name value, source.globals.lookup name = some value →
    ∃ v, coreValueIn? env.factory.model.tcInterp value = some v ∧ env.store ⟨name, ()⟩ = some v
  locals : ∀ name value, (⟨name, ()⟩ : Core.CoreIdent) ∉ unwritten →
    source.locals.lookup name = some value →
    ∃ v, coreValueIn? env.factory.model.tcInterp value = some v ∧ env.store ⟨name, ()⟩ = some v
  snapshots : ∀ name value, source.snapshots.lookup name = some value →
    ∃ v, coreValueIn? env.factory.model.tcInterp value = some v ∧
      env.store (Core.CoreIdent.mkOld name) = some v

/-- Runtime bindings realize the compiler's lexical scope. Scope typing and
Core payload agreement are kept separate so the same source invariant works
in every modeled factory. -/
structure StateFits (scope : Scope) (state : State) : Prop where
  globals : SourceSlotsTyped scope.globals state.globals
  locals : SourceSlotsTyped scope.locals state.locals
  snapshots : SourceSlotsTyped
    (scope.globals.filter fun binding => scope.modifies.contains binding.name) state.snapshots

abbrev ScopedStoresAgree (scope : Scope) (factory : Lambda.Factory Core.CoreLParams)
    (unwritten : List Core.CoreIdent) (state : State) (env : Env Core.Expression) : Prop :=
  StoreAgrees factory unwritten state env ∧ StateFits scope state

/-- Only procedure-visible slots remain at entry and after the body returns. -/
@[expose] def Prepared.interfaceScope (prepared : Prepared) : Scope :=
  { globals := prepared.globals
    locals := prepared.procedure.inputs ++ prepared.procedure.outputs
    modifies := prepared.procedure.contract.modifies }

theorem Prepared.entry_fits {prepared : Prepared} {globals arguments outputs : List Value}
    (hg : valuesMatch prepared.globals globals = true)
    (ha : valuesMatch prepared.procedure.inputs arguments = true)
    (ho : valuesMatch prepared.procedure.outputs outputs = true) :
    StateFits prepared.interfaceScope (prepared.entryState globals arguments outputs) := by
  have globalSlots := sourceSlots_bindValues hg
  refine ⟨globalSlots, ?_, sourceSlots_filter globalSlots prepared.procedure.contract.modifies.contains⟩
  have argLength := (valuesMatch_iff _ _).mp ha |>.1
  change SourceSlotsTyped (prepared.procedure.inputs ++ prepared.procedure.outputs)
    (bindValues prepared.procedure.inputs arguments ++ bindValues prepared.procedure.outputs outputs)
  rw [← bindValues_append argLength]
  exact sourceSlots_bindValues (valuesMatch_append ha ho)

theorem StateFits.lookup_local {scope state} (fits : StateFits scope state)
    {name : String} {binding : Binding}
    (declared : scope.locals.find? (fun b => b.name == name) = some binding) :
    ∃ value, state.locals.lookup name = some value ∧ value.sort = binding.sort := by
  have shape := fits.locals name
  rw [declared] at shape
  cases found : state.locals.lookup name with
  | none => simp [found] at shape
  | some value =>
    exact ⟨value, rfl, by simpa [found] using shape⟩

theorem StateFits.lookup_global {scope state} (fits : StateFits scope state)
    {name : String} {binding : Binding}
    (declared : scope.globals.find? (fun b => b.name == name) = some binding) :
    ∃ value, state.globals.lookup name = some value ∧ value.sort = binding.sort := by
  have shape := fits.globals name
  rw [declared] at shape
  cases found : state.globals.lookup name with
  | none => simp [found] at shape
  | some value =>
    exact ⟨value, rfl, by simpa [found] using shape⟩

theorem StateFits.assign {scope state next} (fits : StateFits scope state)
    {slot : Variable} {expression : Expression}
    (updated : Transformer.assignState slot expression state = .ok next) :
    StateFits scope next := by
  unfold Transformer.assignState Expression.read at updated
  cases lookup : state.lookup slot with
  | none => simp [lookup, bind, Except.bind] at updated
  | some previous =>
    cases evaluated : expression state with
    | error reason => simp [lookup, evaluated, bind, Except.bind] at updated
    | ok value =>
      simp only [lookup, evaluated, bind, Except.bind] at updated
      split at updated
      · rename_i sameSort
        obtain rfl := Except.ok.inj updated
        cases slot with
        | global name =>
          exact ⟨sourceSlots_update fits.globals lookup sameSort.symm, fits.locals, fits.snapshots⟩
        | «local» name =>
          exact ⟨fits.globals, sourceSlots_update fits.locals lookup sameSort.symm, fits.snapshots⟩
      · contradiction

theorem StateFits.init {scope state next} (fits : StateFits scope state)
    {binding : Binding} {expression : Expression}
    (initialized : Transformer.initState binding expression state = .ok next) :
    StateFits {scope with locals := scope.locals ++ [binding]} next := by
  unfold Transformer.initState at initialized
  cases present : state.locals.lookup binding.name with
  | some _ => simp [present, bind, Except.bind, throw] at initialized
  | none =>
    cases evaluated : expression state with
    | error reason => simp [present, evaluated, bind, Except.bind] at initialized
    | ok value =>
      simp only [present, Option.isSome_none, Bool.false_eq_true, ite_false,
        evaluated, bind, Except.bind] at initialized
      split at initialized
      · rename_i sameSort
        obtain rfl := Except.ok.inj initialized
        exact ⟨fits.globals, sourceSlots_append fits.locals present sameSort, fits.snapshots⟩
      · contradiction

theorem StateFits.restrictLocals {scope : Scope} {inner : List Binding} {entry state : State}
    (initial : StateFits scope entry) (final : StateFits {scope with locals := inner} state)
    (keeps : ∀ name binding, scope.locals.find? (fun b => b.name == name) = some binding →
      inner.find? (fun b => b.name == name) = some binding) :
    StateFits scope {state with locals := state.locals.restrict entry.locals} :=
  ⟨final.globals, sourceSlots_restrict initial.locals final.locals keeps, final.snapshots⟩

/-- Reify a Core integer under the interpretation that owns its entry store. -/
theorem inputInt_of_contractPre {factory : Lambda.Factory Core.CoreLParams}
    {target : Core.Procedure} {env : Env Core.Expression} {id : Core.CoreIdent}
    (pre : Core.Logic.Hoare.Procedure.contractPre factory target env)
    (wf : WellFormedStore env.store env.factory)
    (member : (id, Lambda.LMonoTy.int) ∈ target.header.inputs.toList) :
    ∃ i : Int, env.store id = some (.ofInt env.factory.model.tcInterp i) := by
  obtain ⟨v, read, sort⟩ := pre.2.2.2 id .int member
  have tc : v.tc = env.factory.model.tcInterp := wf id v read
  obtain ⟨i, represented⟩ := Lambda.SemValue.exists_ofInt sort
  exact ⟨i, read.trans (congrArg some (represented.trans (congrArg (fun t => Lambda.SemValue.ofInt t i) tc)))⟩

/-- A checked clause in a modeled factory is exactly an evaluation to true. -/
theorem checkAsPredicate_iff_eval {factory : Lambda.Factory Core.CoreLParams}
    {env : Env Core.Expression} (ambient : env.factory.factory = factory)
    (label : Core.CoreLabel) (check : Core.Procedure.Check) :
    Core.Logic.Hoare.Procedure.checkAsPredicate factory env label check ↔
      Core.Expression.eval env.factory env.store check.expr = some (HasBool.ttVal env.factory) := by
  let world : Core.Logic.DenoteValuation factory := ⟨fun _ => False⟩
  have inhabited : Nonempty (Core.Logic.DenoteValuation factory) := ⟨world⟩
  simp [Core.Logic.Hoare.Procedure.checkAsPredicate, Core.Logic.DenoteBasedInterp, ambient]

/-- Get Core's freely ordered input registers into Boole's source order. -/
theorem inputsRepresented {factory : Lambda.Factory Core.CoreLParams}
    {target : Core.Procedure} {env : Env Core.Expression}
    (pre : Core.Logic.Hoare.Procedure.contractPre factory target env)
    (wf : WellFormedStore env.store env.factory)
    (bindings : List Binding)
    (inputs : ∀ binding ∈ bindings,
      binding.sort = .int ∧ ((⟨binding.name, ()⟩ : Core.CoreIdent), Lambda.LMonoTy.int)
        ∈ target.header.inputs.toList) :
    ∃ values, valuesMatch bindings values = true ∧
      ∀ name value, Store.lookup (bindValues bindings values) name = some value →
        ∃ v, coreValueIn? env.factory.model.tcInterp value = some v ∧
          env.store ⟨name, ()⟩ = some v := by
  induction bindings with
  | nil =>
    refine ⟨[], rfl, ?_⟩
    intro _ _ impossible
    cases impossible
  | cons head rest ih =>
    obtain ⟨int, member⟩ := inputs head (by simp)
    obtain ⟨i, represented⟩ := inputInt_of_contractPre pre wf member
    obtain ⟨values, typed, agrees⟩ := ih (fun binding member => inputs binding (by simp [member]))
    refine ⟨.int i :: values, ?_, ?_⟩
    · simp [valuesMatch, int, Value.int] at typed ⊢
      exact typed
    · intro name value read
      by_cases same : head.name = name
      · subst name
        simp [bindValues, Store.lookup] at read
        subst value
        exact ⟨_, rfl, represented⟩
      · change Store.lookup ((head.name, Value.int i) :: bindValues rest values) name =
          some value at read
        have different : (head.name == name) = false := beq_eq_false_iff_ne.mpr same
        simp only [Store.lookup, List.findSome?_cons, different, Bool.false_eq_true, ite_false] at read
        exact agrees name value read

/-- Instantiate the source output quantifier before the Core body runs. Its
output-only slots need no initial payload in the matching relation. -/
theorem typedInitialOutputs (bindings : List Binding)
    (integer : ∀ binding ∈ bindings, binding.sort = .int) :
    ∃ values : List Value, valuesMatch bindings values = true := by
  induction bindings with
  | nil => exact ⟨[], rfl⟩
  | cons head rest ih =>
    obtain ⟨values, typed⟩ := ih (fun binding member => integer binding (by simp [member]))
    refine ⟨.int 0 :: values, ?_⟩
    have int := integer head (by simp)
    simp [valuesMatch, int, Value.int] at typed ⊢
    exact typed

/-- Every value in a filtered source store comes from the original store
when the filter depends only on the key. -/
private theorem lookup_filter_keys {keep : String → Bool} {store : Store} {name : String} {value : Value}
    (read : Store.lookup (store.filter (fun slot => keep slot.1)) name = some value) :
    keep name = true ∧ store.lookup name = some value := by
  induction store with
  | nil => cases read
  | cons head rest ih =>
    obtain ⟨key, current⟩ := head
    by_cases same : key = name
    · subst key
      cases kept : keep name with
      | true =>
        simp [List.filter, kept, Store.lookup] at read
        exact ⟨rfl, by simpa [Store.lookup] using read⟩
      | false =>
        have smaller : Store.lookup (List.filter (fun slot : String × Value => keep slot.1) rest)
              name = some value := by
          simpa only [List.filter_cons, kept, Bool.false_eq_true, ite_false] using read
        exact False.elim (by simpa [kept] using (ih smaller).1)
    · have smaller : Store.lookup (List.filter (fun slot : String × Value => keep slot.1) rest)
          name = some value := by
        cases kept : keep key <;>
          simpa only [List.filter_cons, kept, Bool.false_eq_true, ite_false, ite_true,
            Store.lookup, List.findSome?_cons, beq_iff_eq, same] using read
      obtain ⟨kept, binding⟩ := ih smaller
      exact ⟨kept, by simpa [Store.lookup, same] using binding⟩

private theorem lookup_mem {store : Store} {name : String} {value : Value}
    (read : Store.lookup store name = some value) : (name, value) ∈ store := by
  induction store with
  | nil => cases read
  | cons slot rest ih =>
    obtain ⟨key, current⟩ := slot
    by_cases same : key = name
    · subst key
      have eq : current = value := by simpa [Store.lookup] using read
      subst current
      exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      apply ih
      have different : (key == name) = false := beq_eq_false_iff_ne.mpr same
      simpa only [Store.lookup, List.findSome?_cons, different, Bool.false_eq_true, ite_false] using read

/-- Relate an admitted Core store to the canonical Boole entry, independently
of the contract expression evaluation. Only output-only slots are ignored. -/
theorem entryState_agrees {factory : Lambda.Factory Core.CoreLParams}
    {target : Core.Procedure} {env : Env Core.Expression} (prepared : Prepared)
    (pre : Core.Logic.Hoare.Procedure.contractPre factory target env)
    (wf : WellFormedStore env.store env.factory)
    (inputs : ∀ binding ∈ prepared.globals ++ prepared.procedure.inputs,
      binding.sort = .int ∧ ((⟨binding.name, ()⟩ : Core.CoreIdent), Lambda.LMonoTy.int)
        ∈ target.header.inputs.toList)
    (outputs : ∀ binding ∈ prepared.procedure.outputs, binding.sort = .int ∧
      (⟨binding.name, ()⟩ : Core.CoreIdent) ∈ target.header.getOutputOnlyParams.keys)
    (modified : ∀ name ∈ prepared.procedure.contract.modifies,
      (⟨name, ()⟩ : Core.CoreIdent) ∈ target.header.getInoutParams.keys) :
    ∃ globals arguments initialOutputs,
      valuesMatch prepared.globals globals = true ∧
      valuesMatch prepared.procedure.inputs arguments = true ∧
      valuesMatch prepared.procedure.outputs initialOutputs = true ∧
      StoreAgrees factory target.header.getOutputOnlyParams.keys
        (prepared.entryState globals arguments initialOutputs) env := by
  obtain ⟨globals, hg, readGlobal⟩ := inputsRepresented pre wf prepared.globals
    (fun binding member => inputs binding (List.mem_append_left _ member))
  obtain ⟨arguments, ha, readInput⟩ := inputsRepresented pre wf prepared.procedure.inputs
    (fun binding member => inputs binding (List.mem_append_right _ member))
  obtain ⟨initialOutputs, ho⟩ := typedInitialOutputs prepared.procedure.outputs
    (fun binding member => (outputs binding member).1)
  refine ⟨globals, arguments, initialOutputs, hg, ha, ho, ⟨pre.2.1, readGlobal, ?_, ?_⟩⟩
  · intro name value written read
    change Store.lookup (bindValues prepared.procedure.inputs arguments ++
      bindValues prepared.procedure.outputs initialOutputs) name = some value at read
    have appendLookup :
        Store.lookup (bindValues prepared.procedure.inputs arguments ++
          bindValues prepared.procedure.outputs initialOutputs) name =
        (Store.lookup (bindValues prepared.procedure.inputs arguments) name).or
          (Store.lookup (bindValues prepared.procedure.outputs initialOutputs) name) := by
      simp only [Store.lookup, List.findSome?_append]
    rw [appendLookup] at read
    cases first : Store.lookup (bindValues prepared.procedure.inputs arguments) name with
    | none =>
      have found : Store.lookup (bindValues prepared.procedure.outputs initialOutputs) name =
          some value := by simpa only [first, Option.none_or] using read
      obtain ⟨pair, paired, eqSlot⟩ := List.mem_map.mp (lookup_mem found)
      have isOutput := (outputs pair.1 ((List.of_mem_zip paired).1)).2
      have equal : pair.1.name = name := congrArg Prod.fst eqSlot
      exact False.elim (written (equal ▸ isOutput))
    | some firstValue =>
      have eq : firstValue = value := Option.some.inj (by simpa only [first, Option.some_or] using read)
      subst value
      exact readInput name firstValue first
  · intro name value read
    change Store.lookup ((bindValues prepared.globals globals).filter
      (fun slot => prepared.procedure.contract.modifies.contains slot.1)) name = some value at read
    obtain ⟨mentioned, hread⟩ := lookup_filter_keys read
    obtain ⟨v, representation, payload⟩ := readGlobal name value hread
    exact ⟨v, representation,
      (pre.2.2.1 ⟨name, ()⟩ (modified name (List.contains_iff_mem.mp mentioned))).trans payload⟩


/-- Name used by the corresponding Core register. Both namespaces are
disjoint in a successfully compiled program. -/
@[expose] def coreIdent : Variable → Core.CoreIdent
  | .global name | .local name => ⟨name, ()⟩

/-- Global and local names have a single representation in the Core store. -/
def SlotUnshadowed (source : State) : Variable → Prop
  | .global name => source.locals.lookup name = none
  | .local name => source.globals.lookup name = none

/-- The source has no shadows, so a write to a visible slot must leave the
other source namespace unchanged even though Core stores both at the top level. -/
theorem StoreAgrees.update {factory unwritten source env}
    (agrees : StoreAgrees factory unwritten source env) (slot : Variable)
    {value : Value} {v : Core.Expression.Val} {store : Core.CoreStore}
    (payload : coreValueIn? env.factory.model.tcInterp value = some v)
    (write : store (coreIdent slot) = some v)
    (frame : ∀ id, coreIdent slot ≠ id → store id = env.store id)
    (noShadow : SlotUnshadowed source slot)
    (freshOld : ∀ name value, source.snapshots.lookup name = some value →
      coreIdent slot ≠ Core.CoreIdent.mkOld name) :
    StoreAgrees factory (unwritten.filter (· != coreIdent slot)) (source.update slot value)
      { env with store } := by
  have other {σ : Store} {name key : String} {old : Value} (different : name ≠ key)
      (read : (σ.update key value).lookup name = some old) : σ.lookup name = some old := by
    simpa only [Store.lookup_update_other _ _ _ _ different] using read
  have same {σ : Store} {name : String} {old : Value}
      (read : (σ.update name value).lookup name = some old) : old = value := by
    rw [Store.lookup_update] at read
    cases σ.lookup name <;> simp_all
  have identical {a b : String} (eq : (⟨a, ()⟩ : Core.CoreIdent) = ⟨b, ()⟩) :
      a = b := congrArg (·.name) eq
  have wasWritten (name : String) (different : coreIdent slot ≠ ⟨name, ()⟩)
      (current : (⟨name, ()⟩ : Core.CoreIdent) ∉ unwritten.filter (· != coreIdent slot)) :
      (⟨name, ()⟩ : Core.CoreIdent) ∉ unwritten := by
    intro before
    apply current
    simp [before, Ne.symm different]
  refine ⟨agrees.factory_eq, ?_, ?_, ?_⟩
  · intro name old read
    cases slot with
    | global key =>
      by_cases eq : name = key
      · subst key
        obtain rfl := same read
        exact ⟨v, payload, write⟩
      · have different : (⟨key, ()⟩ : Core.CoreIdent) ≠ ⟨name, ()⟩ :=
          fun eqId => eq (identical eqId).symm
        obtain ⟨current, hyp, binding⟩ := agrees.globals name old (other eq read)
        exact ⟨current, hyp, (frame _ different).trans binding⟩
    | «local» key =>
      have different : (⟨key, ()⟩ : Core.CoreIdent) ≠ ⟨name, ()⟩ := by
        intro eq
        obtain rfl := identical eq
        have impossible : (none : Option Value) = some old :=
          (show _ = none from noShadow).symm.trans (by simpa [State.update] using read)
        cases impossible
      obtain ⟨current, hyp, binding⟩ := agrees.globals name old read
      exact ⟨current, hyp, (frame _ different).trans binding⟩
  · intro name old written read
    cases slot with
    | global key =>
      have different : (⟨key, ()⟩ : Core.CoreIdent) ≠ ⟨name, ()⟩ := by
        intro eq
        obtain rfl := identical eq
        have impossible : (none : Option Value) = some old :=
          (show _ = none from noShadow).symm.trans (by simpa [State.update] using read)
        cases impossible
      obtain ⟨current, hyp, binding⟩ := agrees.locals name old (wasWritten name different written) read
      exact ⟨current, hyp, (frame _ different).trans binding⟩
    | «local» key =>
      by_cases eq : name = key
      · subst key
        obtain rfl := same read
        exact ⟨v, payload, write⟩
      · have different : (⟨key, ()⟩ : Core.CoreIdent) ≠ ⟨name, ()⟩ :=
          fun eqId => eq (identical eqId).symm
        obtain ⟨current, hyp, binding⟩ := agrees.locals name old (wasWritten name different written)
          (other eq read)
        exact ⟨current, hyp, (frame _ different).trans binding⟩
  · intro name old read
    have previous : source.snapshots.lookup name = some old := by cases slot <;> exact read
    obtain ⟨current, hyp, binding⟩ := agrees.snapshots name old previous
    exact ⟨current, hyp, (frame _ (freshOld name old previous)).trans binding⟩

private theorem clausesHold_iff {clauses : List (Clause Expression)} {state : State} :
    clausesHold clauses state ↔ ∀ clause ∈ clauses, Holds clause.condition state := by
  induction clauses with
  | nil => simp [clausesHold]
  | cons head tail ih =>
    simp only [clausesHold, Obligation, List.forall_mem_cons, ih]

/-- Satisfy the source requires from the corresponding Core contract checks. -/
theorem requires_of_core {factory : Lambda.Factory Core.CoreLParams} {unwritten}
    {source : State} {env : Env Core.Expression} {target : Core.Procedure}
    {clauses : List (Clause Expression)}
    (store : StoreAgrees factory unwritten source env)
    (pre : Core.Logic.Hoare.Procedure.contractPre factory target env)
    (paired : ∀ clause ∈ clauses, ∃ label check,
      (label, check) ∈ target.spec.preconditions.toList ∧
      (Core.Expression.eval env.factory env.store check.expr = some (HasBool.ttVal env.factory) →
        Holds clause.condition source)) :
    clausesHold clauses source := by
  apply clausesHold_iff.mpr
  intro clause member
  obtain ⟨label, check, present, agree⟩ := paired clause member
  exact agree ((checkAsPredicate_iff_eval store.factory_eq label check).mp (pre.1 label check present))

/-- Use the source certificate only for ordinary ensures. Each ordinary Core
clause must have a paired ordinary source clause. -/
theorem ensures_to_core {factory : Lambda.Factory Core.CoreLParams} {unwritten}
    {source : State} {env : Env Core.Expression} {target : Core.Procedure}
    {prepared : Prepared}
    (store : StoreAgrees factory unwritten source env)
    (post : prepared.postcondition none source)
    (paired : ∀ label check, (label, check) ∈ target.spec.postconditions.toList →
      check.attr = Core.Procedure.CheckAttr.Default →
      ∃ clause ∈ prepared.procedure.contract.ensures, clause.free = false ∧
        (Holds clause.condition source →
          Core.Expression.eval env.factory env.store check.expr = some (HasBool.ttVal env.factory))) :
    Core.Logic.Hoare.Procedure.contractPost factory target env := by
  intro label check member ordinary
  obtain ⟨clause, present, checked, agree⟩ := paired label check member ordinary
  apply (checkAsPredicate_iff_eval store.factory_eq label check).mpr
  apply agree
  exact clausesHold_iff.mp post clause (List.mem_filter.mpr ⟨present, by simp [checked]⟩)

/-- A join may conservatively mark more local slots as unwritten. -/
theorem StoreAgrees.weaken {factory unwritten more source env}
    (agrees : StoreAgrees factory unwritten source env)
    (subset : ∀ id ∈ unwritten, id ∈ more) : StoreAgrees factory more source env :=
  ⟨agrees.factory_eq, agrees.globals,
    fun name value written => agrees.locals name value (fun old => written (subset _ old)),
    agrees.snapshots⟩

/-- Scope exit preserves correspondence on every source-visible slot that
survives the two lexical projections. -/
theorem StoreAgrees.restrictLocals_dropVars {factory unwritten source env}
    (agrees : StoreAgrees factory unwritten source env)
    (entry : Store) (drop : List Core.CoreIdent)
    (keepGlobal : ∀ name value, source.globals.lookup name = some value →
      (⟨name, ()⟩ : Core.CoreIdent) ∉ drop)
    (keepLocal : ∀ name, (entry.lookup name).isSome →
      (⟨name, ()⟩ : Core.CoreIdent) ∉ drop)
    (keepOld : ∀ name value, source.snapshots.lookup name = some value →
      Core.CoreIdent.mkOld name ∉ drop) :
    StoreAgrees factory unwritten { source with locals := source.locals.restrict entry }
      { env with store := dropVars drop env.store } := by
  refine ⟨agrees.factory_eq, ?_, ?_, ?_⟩
  · intro name value found
    obtain ⟨v, encoded, binding⟩ := agrees.globals name value found
    exact ⟨v, encoded, by simpa [dropVars, keepGlobal name value found] using binding⟩
  · intro name value written found
    have read : Store.lookup (source.locals.filter (fun slot => (entry.lookup slot.1).isSome)) name =
        some value := found
    obtain ⟨visible, binding⟩ := lookup_filter_keys (keep := fun n => (entry.lookup n).isSome) read
    obtain ⟨v, encoded, represented⟩ := agrees.locals name value written binding
    exact ⟨v, encoded, by simpa [dropVars, keepLocal name visible] using represented⟩
  · intro name value found
    obtain ⟨v, encoded, binding⟩ := agrees.snapshots name value found
    exact ⟨v, encoded, by simpa [dropVars, keepOld name value found] using binding⟩

/-- A matching initialization extends the source locals. The Core freshness
premise also excludes collisions with represented globals and snapshots. -/
theorem StoreAgrees.init {factory unwritten source env}
    (agrees : StoreAgrees factory unwritten source env)
    (name : String) (value : Value) {v : Core.Expression.Val} {store : Core.CoreStore}
    (encoded : coreValueIn? env.factory.model.tcInterp value = some v)
    (fresh : source.locals.lookup name = none)
    (unused : env.store ⟨name, ()⟩ = none)
    (stored : store ⟨name, ()⟩ = some v)
    (frame : ∀ y, (⟨name, ()⟩ : Core.CoreIdent) ≠ y → store y = env.store y) :
    StoreAgrees factory (unwritten.filter (· != ⟨name, ()⟩))
      { source with locals := source.locals ++ [(name, value)] } { env with store } := by
  refine ⟨agrees.factory_eq, ?_, ?_, ?_⟩
  · intro key read found
    obtain ⟨result, encoded, binding⟩ := agrees.globals key read found
    have different : (⟨name, ()⟩ : Core.CoreIdent) ≠ ⟨key, ()⟩ := by
      intro same
      rw [same, binding] at unused
      contradiction
    exact ⟨result, encoded, (frame _ different).trans binding⟩
  · intro key read retained found
    change Store.lookup (source.locals ++ [(name, value)]) key = some read at found
    simp only [Store.lookup, List.findSome?_append] at found
    change (source.locals.lookup key).or (Store.lookup [(name, value)] key) = some read at found
    cases first : source.locals.lookup key with
    | none =>
      rw [first, Option.none_or] at found
      by_cases eq : name = key
      · subst key
        have same : value = read := by simpa [first, Store.lookup] using found
        subst read
        exact ⟨v, encoded, stored⟩
      · simp [Store.lookup, eq] at found
    | some prior =>
      by_cases eq : name = key
      · subst key
        rw [fresh] at first
        contradiction
      · have different : (⟨name, ()⟩ : Core.CoreIdent) ≠ ⟨key, ()⟩ :=
          fun same => eq (congrArg (·.name) same)
        have oldRetained : (⟨key, ()⟩ : Core.CoreIdent) ∉ unwritten := by
          intro member
          exact retained (by simp [member, Ne.symm different])
        have eqRead : prior = read := by simpa [first] using found
        subst prior
        obtain ⟨result, encoded, binding⟩ := agrees.locals key read oldRetained first
        exact ⟨result, encoded, (frame _ different).trans binding⟩
  · intro key read found
    obtain ⟨result, encoded, binding⟩ := agrees.snapshots key read found
    have different : (⟨name, ()⟩ : Core.CoreIdent) ≠ Core.CoreIdent.mkOld key := by
      intro same
      rw [same, binding] at unused
      contradiction
    exact ⟨result, encoded, (frame _ different).trans binding⟩

/-- Boole's no-space rule keeps writable names separate from saved Core names. -/
theorem coreIdent_ne_old_of_no_space {slot : Variable}
    (fresh : (coreIdent slot).name.contains ' ' = false) (old : String) :
    coreIdent slot ≠ Core.CoreIdent.mkOld old := by
  intro same
  rw [same] at fresh
  have spaced : ' ' ∈ (Core.CoreIdent.mkOld old).name.toList := by
    simp [Core.CoreIdent.mkOld, Core.CoreIdent.oldStr, String.toList_append]
  rw [String.contains_char_eq, decide_eq_true spaced] at fresh
  contradiction

/-- Successful evaluation of the source expression gives the same payload
in the target expression's model. -/
@[expose] def ExprAgrees (rel : State → Env Core.Expression → Prop)
    (source : Expression) (target : Core.Expression.Expr) : Prop :=
  ∀ state env value, rel state env → source state = .ok value →
    ∃ v, coreValueIn? env.factory.model.tcInterp value = some v ∧
      Core.Expression.eval env.factory env.store target = some v

theorem ExprAgrees.intLiteral (rel : State → Env Core.Expression → Prop) (n : Int) :
    ExprAgrees rel (fun _ => .ok (.int n)) (.intConst () n) := by
  intro state env value _ result
  obtain rfl := Except.ok.inj result
  exact ⟨_, rfl, Lambda.LExpr.denoteEval_intConst⟩

theorem ExprAgrees.boolLiteral (rel : State → Env Core.Expression → Prop) (b : Bool) :
    ExprAgrees rel (fun _ => .ok (.bool b)) (.boolConst () b) := by
  intro state env value _ result
  obtain rfl := Except.ok.inj result
  exact ⟨_, rfl, Lambda.LExpr.denoteEval_boolConst⟩

private theorem coreValueIn_tc {tc : Lambda.TyConstrInterp} {value : Value}
    {v : Core.Expression.Val} (payload : coreValueIn? tc value = some v) :
    v.tc = tc := by
  obtain ⟨sort, data⟩ := value
  unfold coreValueIn? at payload
  split at payload
  all_goals
    first
    | exact (congrArg Lambda.SemValue.tc (Option.some.inj payload)).symm
    | contradiction

theorem ExprAgrees.bool {rel : State → Env Core.Expression → Prop}
    {source : Expression} {target : Core.Expression.Expr}
    (agrees : ExprAgrees rel source target) {state : State} {env : Env Core.Expression}
    (related : rel state env) {b : Bool} (evaluated : source state = .ok (.bool b)) :
    Core.Expression.eval env.factory env.store target = some (.ofBool env.factory.model.tcInterp b) := by
  obtain ⟨v, payload, evaluatedCore⟩ := agrees state env _ related evaluated
  obtain rfl := Option.some.inj payload
  exact evaluatedCore

/-- Apply a Core operator law to the two evaluated operands and the
successful result of the compiler's binary operator. -/
theorem ExprAgrees.binary {rel : State → Env Core.Expression → Prop}
    {left right : Expression} {leftCore rightCore target : Core.Expression.Expr}
    (op : BinaryOp)
    (leftAgrees : ExprAgrees rel left leftCore) (rightAgrees : ExprAgrees rel right rightCore)
    (coreRule : ∀ {state env} {a b result : Value} {v w : Core.Expression.Val},
      rel state env →
      coreValueIn? env.factory.model.tcInterp a = some v →
      coreValueIn? env.factory.model.tcInterp b = some w →
      Core.Expression.eval env.factory env.store leftCore = some v →
      Core.Expression.eval env.factory env.store rightCore = some w →
      binaryValue op a b = .ok result →
      ∃ resultValue, coreValueIn? env.factory.model.tcInterp result = some resultValue ∧
        Core.Expression.eval env.factory env.store target = some resultValue) :
    ExprAgrees rel (binary op left right) target := by
  intro state env result related evaluated
  cases ranLeft : left state with
  | error reason => simp [Hoare.binary, ranLeft, Except.bind] at evaluated
  | ok a =>
    cases ranRight : right state with
    | error reason => simp [Hoare.binary, ranLeft, ranRight, Except.bind] at evaluated
    | ok b =>
      obtain ⟨v, encodedLeft, evalLeft⟩ := leftAgrees state env a related ranLeft
      obtain ⟨w, encodedRight, evalRight⟩ := rightAgrees state env b related ranRight
      exact coreRule related encodedLeft encodedRight evalLeft evalRight
        (by simpa [Hoare.binary, ranLeft, ranRight, Except.bind] using evaluated)

theorem ExprAgrees.read {factory unwritten}
    (slot : Variable) (written : coreIdent slot ∉ unwritten) (ty : Option Lambda.LMonoTy) :
    ExprAgrees (StoreAgrees factory unwritten) (Expression.read slot)
      (.fvar () (coreIdent slot) ty) := by
  intro state env value related evaluates
  have present : state.lookup slot = some value := by
    unfold Expression.read at evaluates
    cases slotValue : state.lookup slot <;> simp_all
  obtain ⟨v, payload, binding⟩ : ∃ v, coreValueIn? env.factory.model.tcInterp value = some v ∧
      env.store (coreIdent slot) = some v := by
    cases slot with
    | global name => exact related.globals name value present
    | «local» name => exact related.locals name value written present
  exact ⟨v, payload, Lambda.LExpr.denoteEval_fvar binding (coreValueIn_tc payload)⟩

/-- A saved modified global is the value read by the lowered `old` expression. -/
theorem ExprAgrees.readSnapshot {factory unwritten} {rel : State → Env Core.Expression → Prop}
    (name : String) (ty : Option Lambda.LMonoTy)
    (store : ∀ state env, rel state env → StoreAgrees factory unwritten state env)
    (hasSnapshot : ∀ state env, rel state env → (state.snapshots.lookup name).isSome = true) :
    ExprAgrees rel (Expression.old (Expression.read (.global name)))
      (.fvar () (Core.CoreIdent.mkOld name) ty) := by
  intro state env value related evaluates
  obtain ⟨saved, present⟩ := Option.isSome_iff_exists.mp (hasSnapshot state env related)
  have joined : Store.lookup (state.snapshots ++ state.globals) name = some saved := by
    simp only [Store.lookup, List.findSome?_append]
    rw [show state.snapshots.findSome? (fun slot =>
      if slot.1 == name then some slot.2 else none) = some saved from present]
    rfl
  have same : saved = value := by
    simpa [Expression.old, Expression.read, State.lookup, joined] using evaluates
  subst saved
  obtain ⟨v, payload, binding⟩ := (store _ _ related).snapshots name value present
  exact ⟨v, payload, Lambda.LExpr.denoteEval_fvar binding (coreValueIn_tc payload)⟩

private theorem updateState_facts {P : PureExpr} {before after : SemanticStore P}
    {id : P.Ident} {value : P.Val}
    (write : UpdateState P before id value after) :
    after id = some value ∧ ∀ other, id ≠ other → after other = before other := by
  cases write with
  | update _ stored preserved => exact ⟨stored, preserved⟩

/-- Apply the expression agreement to the value of a successful assignment.
The output slot becomes represented at the first write. -/
theorem StoreAgrees.assign {factory unwritten source env}
    (related : StoreAgrees factory unwritten source env) (slot : Variable)
    {expr : Expression} {target : Core.Expression.Expr} {after : State}
    {store : Core.CoreStore} {value : Core.Expression.Val}
    (exprAgrees : ∀ value, expr source = .ok value →
      ∃ v, coreValueIn? env.factory.model.tcInterp value = some v ∧
        Core.Expression.eval env.factory env.store target = some v)
    (coreValue : Core.Expression.eval env.factory env.store target = some value)
    (coreWrite : UpdateState Core.Expression env.store (coreIdent slot) value store)
    (booleWrite : Transformer.assignState slot expr source = .ok after)
    (noShadow : SlotUnshadowed source slot)
    (freshOld : ∀ name v, source.snapshots.lookup name = some v →
      coreIdent slot ≠ Core.CoreIdent.mkOld name) :
    StoreAgrees factory (unwritten.filter (· != coreIdent slot)) after { env with store } := by
  unfold Transformer.assignState at booleWrite
  cases read : Expression.read slot source with
  | error reason => simp [read, bind, Except.bind] at booleWrite
  | ok prev =>
    cases eval : expr source with
    | error reason => simp [read, eval, bind, Except.bind] at booleWrite
    | ok result =>
      simp only [read, eval, bind, Except.bind] at booleWrite
      split at booleWrite
      · obtain rfl := Except.ok.inj booleWrite
        obtain ⟨v, payload, verified⟩ := exprAgrees result eval
        obtain rfl := Option.some.inj (verified.symm.trans coreValue)
        have facts := updateState_facts coreWrite
        exact related.update slot payload facts.1 facts.2 noShadow freshOld
      · contradiction

private theorem initState_facts {P : PureExpr} {before after : SemanticStore P}
    {id : P.Ident} {value : P.Val}
    (write : InitState P before id value after) :
    before id = none ∧ after id = some value ∧ ∀ other, id ≠ other → after other = before other := by
  cases write with
  | init unused stored preserved => exact ⟨unused, stored, preserved⟩

theorem StoreAgrees.declare {factory unwritten source env}
    (related : StoreAgrees factory unwritten source env) (binding : Binding)
    {expr : Expression} {target : Core.Expression.Expr} {after : State}
    {store : Core.CoreStore} {value : Core.Expression.Val}
    (exprAgrees : ∀ value, expr source = .ok value →
      ∃ v, coreValueIn? env.factory.model.tcInterp value = some v ∧
        Core.Expression.eval env.factory env.store target = some v)
    (coreValue : Core.Expression.eval env.factory env.store target = some value)
    (coreWrite : InitState Core.Expression env.store ⟨binding.name, ()⟩ value store)
    (booleWrite : Transformer.initState binding expr source = .ok after) :
    StoreAgrees factory (unwritten.filter (· != ⟨binding.name, ()⟩)) after {env with store} := by
  unfold Transformer.initState at booleWrite
  cases present : source.locals.lookup binding.name with
  | some _ => simp [present, bind, Except.bind, throw] at booleWrite
  | none =>
    cases evaluated : expr source with
    | error reason => simp [present, evaluated, bind, Except.bind] at booleWrite
    | ok result =>
      simp only [present, Option.isSome_none, Bool.false_eq_true, ite_false,
        evaluated, bind, Except.bind] at booleWrite
      split at booleWrite
      · obtain rfl := Except.ok.inj booleWrite
        obtain ⟨v, payload, verified⟩ := exprAgrees result evaluated
        obtain rfl := Option.some.inj (verified.symm.trans coreValue)
        obtain ⟨unused, stored, preserved⟩ := initState_facts coreWrite
        exact related.init binding.name result payload present unused stored preserved
      · contradiction

end Strata.Boole.Hoare
