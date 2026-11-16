/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.CoreReference
import all StrataBoole.Boole.Semantics.CoreReference
public import StrataBoole.Boole.Semantics.Adequacy.Lowering
import all StrataBoole.Boole.Semantics.Adequacy.Lowering
import all StrataBoole.Verify
import all StrataBoole.Boole.Interp
import StrataBoole.Boole.Semantics.Adequacy.SourceState
import StrataBoole.Boole.Semantics.Adequacy.SourceInterface
import all StrataBoole.Boole.Runtime
import all StrataBoole.Boole.Types
import all Strata.DL.Lambda.LExprTypeEnv
import all Strata.DL.Lambda.LExprAliasFree
import Strata.DL.Lambda.LTyUnify
import all Strata.Languages.Core.ProcedureType
import all Strata.Languages.Core.StatementType
import all Strata.Util.ListMap
import Strata.Util.ListMapProps
import Strata.Util.ListUtilsProps
import all Strata.Languages.Core.StatementSemantics
import Strata.Languages.Core.StatementSemanticsProps

/-! # Entry frames -/

public section
namespace Strata.Boole

private theorem lookup_none_of_name_not_mem (slots : List (Core.CoreIdent × Core.Expression.Val))
    (id : Core.CoreIdent) (absent : id ∉ slots.map Prod.fst) : slots.lookup id = none := by
  apply List.lookup_eq_none_iff.mpr
  intro pair member
  have different : id ≠ pair.1 := fun same => absent (same.symm ▸ List.mem_map_of_mem member)
  simp [bne, different]

private theorem initStates_lookup (slots : List (Core.CoreIdent × Core.Expression.Val))
    (base : Core.CoreStore) (distinct : (slots.map Prod.fst).Nodup)
    (fresh : ∀ id ∈ slots.map Prod.fst, base id = none) :
    Imperative.InitStates (P := Core.Expression) base (slots.map Prod.fst) (slots.map Prod.snd)
      (fun id => (slots.lookup id).or (base id)) := by
  induction slots generalizing base with
  | nil => exact .init_none
  | cons head tail ih =>
      obtain ⟨name, value⟩ := head
      let next := Core.updatedState (P := Core.Expression) base name value
      have step : Imperative.InitState Core.Expression base name value next :=
        Core.updatedStateInit (fresh name (by simp))
      simp only [List.map_cons, List.nodup_cons] at distinct
      have nextFresh : ∀ id ∈ tail.map Prod.fst, next id = none := by
        intro id present
        have different : id ≠ name := fun eq => distinct.1 (eq ▸ present)
        have absent := fresh id (List.mem_cons_of_mem _ present)
        simp [next, Core.updatedState, different, absent]
      have initialized := ih next distinct.2 nextFresh
      have storeEq :
          (fun id => (tail.lookup id).or (next id)) =
            fun id => ((name, value) :: tail).lookup id |>.or (base id) := by
        funext id
        by_cases eq : id = name
        · subst id
          have missing : tail.lookup name = none :=
            lookup_none_of_name_not_mem tail name distinct.1
          simp [List.lookup, missing, next, Core.updatedState]
        · have unequal : (id == name) = false := beq_eq_false_iff_ne.mpr eq
          simp [List.lookup, next, Core.updatedState, eq, unequal]
      rw [storeEq] at initialized
      exact .init_some step initialized

/-- With distinct input and output-only names, Core's call frame stores the
supplied semantic values at those names, then installs Core's own old snapshots. -/
theorem initCallFrame_iff_lookup (procedure : Core.Procedure)
    (arguments initialOutputs : List Core.Expression.Val) (store : Core.CoreStore)
    (inputLength : procedure.header.inputs.keys.length = arguments.length)
    (outputLength : (Imperative.Calls.outputOnlyParams (P := Core.Expression)
      procedure.header).length = initialOutputs.length)
    (inputDistinct : procedure.header.inputs.keys.Nodup)
    (outputDistinct : (Imperative.Calls.outputOnlyParams (P := Core.Expression)
      procedure.header).Nodup) :
    let inputs := procedure.header.inputs.keys.zip arguments
    let outputNames := Imperative.Calls.outputOnlyParams (P := Core.Expression) procedure.header
    let outputs := outputNames.zip initialOutputs
    let installed : Core.CoreStore := fun id => (outputs.lookup id).or (inputs.lookup id)
    Core.InitCallFrame procedure arguments initialOutputs store ↔
      store = Core.withOldSnapshots (Imperative.Calls.inoutParams (P := Core.Expression)
        procedure.header) installed := by
  dsimp only
  let inputNames := procedure.header.inputs.keys
  let outputNames := Imperative.Calls.outputOnlyParams (P := Core.Expression) procedure.header
  let inputs := inputNames.zip arguments
  let outputs := outputNames.zip initialOutputs
  have inputKeys : inputs.map Prod.fst = inputNames := List.map_fst_zip (Nat.le_of_eq inputLength)
  have inputValues : inputs.map Prod.snd = arguments := List.map_snd_zip (Nat.le_of_eq inputLength.symm)
  have outputKeys : outputs.map Prod.fst = outputNames := List.map_fst_zip (Nat.le_of_eq outputLength)
  have outputValues : outputs.map Prod.snd = initialOutputs := List.map_snd_zip (Nat.le_of_eq outputLength.symm)
  have inputFresh : ∀ id ∈ inputs.map Prod.fst, (Imperative.emptyStore : Core.CoreStore) id = none :=
    fun _ _ => rfl
  have inputDistinct' : (inputs.map Prod.fst).Nodup := inputKeys ▸ inputDistinct
  have inputFrame := initStates_lookup inputs Imperative.emptyStore inputDistinct' inputFresh
  rw [inputKeys, inputValues] at inputFrame
  have outputFresh : ∀ id ∈ outputs.map Prod.fst, inputs.lookup id = none := by
    rw [outputKeys]
    intro id present
    apply lookup_none_of_name_not_mem
    rw [inputKeys]
    change id ∈ procedure.header.outputs.keys.filter (fun id => !procedure.header.inputs.keys.contains id) at present
    simpa using (List.mem_filter.mp present).2
  have outputDistinct' : (outputs.map Prod.fst).Nodup := outputKeys ▸ outputDistinct
  have outputFrame := initStates_lookup outputs (fun id => inputs.lookup id) outputDistinct' outputFresh
  rw [outputKeys, outputValues] at outputFrame
  have inputFrame' : Imperative.InitStates (P := Core.Expression) Imperative.emptyStore
      inputNames arguments (fun id => inputs.lookup id) := by
    simpa [Imperative.emptyStore, Option.or_none] using inputFrame
  have canonical : Core.InitCallFrame procedure arguments initialOutputs
      (Core.withOldSnapshots (Imperative.Calls.inoutParams (P := Core.Expression) procedure.header)
        (fun id => (outputs.lookup id).or (inputs.lookup id))) :=
    ⟨_, _, inputFrame', outputFrame, rfl⟩
  exact ⟨fun frame => Core.InitCallFrameUniqueResult frame canonical, fun same => same.symm ▸ canonical⟩

private theorem instantiateCheckedTypes_length (context : Core.Expression.TyContext)
    (environment final : Core.Expression.TyEnv) (types : List Lambda.LTy)
    (result : List Lambda.LMonoTy)
    (success : Lambda.LMonoTySignature.instantiate.go context environment types = .ok (result, final)) :
    result.length = types.length := by
  induction types generalizing environment result final with
  | nil =>
    have same : [] = result := congrArg Prod.fst (Except.ok.inj success)
    simp [← same]
  | cons ty rest ih =>
    simp only [Lambda.LMonoTySignature.instantiate.go, bind, Except.bind] at success
    split at success
    · contradiction
    · split at success
      · contradiction
      · rename_i pair step
        obtain ⟨tail, last⟩ := pair
        have size := ih _ _ _ step
        have same := congrArg Prod.fst (Except.ok.inj success)
        dsimp only at same
        rw [← same]
        simp [size]

private theorem instantiateSignature_keys (context : Core.Expression.TyContext)
    (environment final : Core.Expression.TyEnv) (typeArgs : List String)
    (signature result : ListMap Core.CoreIdent Lambda.LMonoTy)
    (success : Lambda.LMonoTySignature.instantiate context environment typeArgs signature =
      .ok (result, final)) :
    result.keys = signature.keys := by
  simp only [Lambda.LMonoTySignature.instantiate, bind, Except.bind] at success
  split at success
  · contradiction
  · rename_i first
    split at success
    · contradiction
    · rename_i second
      have firstSize := Lambda.LMonoTys.instantiateEnv_length _ _ _ _ _ first
      have secondSize := instantiateCheckedTypes_length _ _ _ _ _ second
      have same := congrArg Prod.fst (Except.ok.inj success)
      dsimp only at same
      rw [← same]
      simp only [List.length_map, firstSize] at secondSize
      exact (listMap_keys_zip_values signature _ secondSize.symm).1

private theorem instantiateHeader_keys (context : Core.Expression.TyContext)
    (environment final : Core.Expression.TyEnv) (header : Core.Procedure.Header)
    (inputs outputs : ListMap Core.CoreIdent Lambda.LMonoTy)
    (success : Core.Procedure.Header.instantiate context environment header =
      .ok (inputs, outputs, final)) :
    inputs.keys = header.inputs.keys ∧ outputs.keys = header.outputs.keys := by
  simp only [Core.Procedure.Header.instantiate, bind, Except.bind] at success
  split at success
  · contradiction
  · rename_i signature checked
    have keys := instantiateSignature_keys _ _ _ _ _ _ checked
    have same := Except.ok.inj success
    have inputEq := congrArg Prod.fst same
    have outputEq := congrArg (fun pair => pair.2.1) same
    dsimp only at inputEq outputEq
    rw [← inputEq, ← outputEq]
    let typed := signature.1.toList
    let rawInputs := header.inputs.toList
    let rawOutputs := header.outputs.toList
    have names : typed.map Prod.fst = (rawInputs ++ rawOutputs).map Prod.fst := by
      rw [ListMap.keys_eq_map_fst signature.1,
        ListMap.keys_eq_map_fst (header.inputs ++ header.outputs)] at keys
      exact keys
    have first : (typed.take rawInputs.length).map Prod.fst = rawInputs.map Prod.fst := by
      rw [List.map_take, names, List.map_append]
      exact List.take_left' (List.length_map _)
    have second : (typed.drop rawInputs.length).map Prod.fst = rawOutputs.map Prod.fst := by
      rw [List.map_drop, names, List.map_append]
      exact List.drop_left' (List.length_map _)
    have split : signature.1.splitAt header.inputs.length =
        (typed.take rawInputs.length, typed.drop rawInputs.length) := List.splitAt_eq
    rw [split]
    exact ⟨(ListMap.keys_eq_map_fst _).trans (first.trans (ListMap.keys_eq_map_fst _).symm),
      (ListMap.keys_eq_map_fst _).trans (second.trans (ListMap.keys_eq_map_fst _).symm)⟩

private theorem instantiateHeader_mapped_keys (context : Core.Expression.TyContext)
    (environment final : Core.Expression.TyEnv) (header : Core.Procedure.Header)
    (inputs outputs : ListMap Core.CoreIdent Lambda.LMonoTy)
    (wrap : Std.Format → Message)
    (success : (Core.Procedure.Header.instantiate context environment header).mapError wrap =
      .ok (inputs, outputs, final)) :
    inputs.keys = header.inputs.keys ∧ outputs.keys = header.outputs.keys := by
  cases run : Core.Procedure.Header.instantiate context environment header with
  | error error => simp [run, Except.mapError] at success
  | ok result =>
    have same : result = (inputs, outputs, final) := by
      simpa [run, Except.mapError] using success
    rw [same] at run
    exact instantiateHeader_keys _ _ _ _ _ _ run

private theorem noDuplicateFormals (procedure : Core.Procedure) (location : FileRange)
    (result : Unit) (passed : procedure.checkParamNames location = .ok result) :
    procedure.header.inputs.keys.Nodup ∧ procedure.header.outputs.keys.Nodup := by
  by_cases inputs : procedure.header.inputs.keys.Nodup <;>
    by_cases outputs : procedure.header.outputs.keys.Nodup <;>
    simp_all [Core.Procedure.checkParamNames, bind, Except.bind]

/-- Core checking leaves the ordered input and output names in the raw
header intact and checks that each list has distinct names. -/
theorem checkedProcedure_formals {program : Core.Program} {raw checked : Core.Procedure}
    (checkedByCore : ProcedureWasChecked program raw checked) :
    checked.header.inputs.keys = raw.header.inputs.keys ∧
    checked.header.outputs.keys = raw.header.outputs.keys ∧
    checked.header.inputs.keys.Nodup ∧ checked.header.outputs.keys.Nodup := by
  obtain ⟨context, environment, final, metadata, success⟩ := checkedByCore
  unfold Core.Procedure.typeCheck at success
  simp only [bind, Except.bind] at success
  split at success
  · contradiction
  · rename_i passed
    have distinct := noDuplicateFormals _ _ _ passed
    have keys : checked.header.inputs.keys = raw.header.inputs.keys ∧
        checked.header.outputs.keys = raw.header.outputs.keys := by
      repeat' first
        | contradiction
        | (have same := Except.ok.inj success
           obtain rfl := congrArg Prod.fst same
           apply instantiateHeader_mapped_keys
           assumption)
        | split at success
    exact ⟨keys.1, keys.2, keys.1.symm ▸ distinct.1, keys.2.symm ▸ distinct.2⟩


private theorem instantiateEmptySignature (env : Core.Expression.TyEnv) (types : List Lambda.LMonoTy)
    (closed : ∀ ty ∈ types, ty.freeVars = []) :
    Lambda.LMonoTys.instantiateEnv [] types env = .ok (types, env) := by
  have unchanged : ∀ ty ∈ types,
      Lambda.LMonoTy.subst (Strata.Util.HMaps.ofScopes [[]]) ty = ty := by
    intro ty member
    exact Lambda.LMonoTy.subst_no_relevant_keys _ _ (by simp [closed ty member])
  have allUnchanged : Lambda.LMonoTys.subst (Strata.Util.HMaps.ofScopes [[]]) types = types := by
    rw [Lambda.LMonoTys.subst_eq_map]
    calc
      _ = types.map id := List.map_congr_left unchanged
      _ = types := List.map_id _
  cases env
  simp [Lambda.LMonoTys.instantiateEnv, Lambda.LMonoTys.instantiate, Lambda.TGenEnv.genTyVars,
    bind, Except.bind, allUnchanged]

private theorem instantiateMonoType {context : Core.Expression.TyContext}
    {env final : Core.Expression.TyEnv} {ty checked : Lambda.LMonoTy}
    (aliasFree : ty.aliasFree env.context.aliases)
    (success : (Lambda.LTy.forAll [] ty).instantiateWithCheck context env = .ok (checked, final)) :
    checked = ty ∧ final = env := by
  have resolve : (Lambda.LTy.forAll [] ty).resolveAliases env = .ok (ty, env) := by
    have aliasEq := Lambda.resolveAliases_aliasFree (T := Core.CoreLParams) ty env aliasFree
    cases env
    simpa only [Lambda.LTy.resolveAliases, Lambda.LTy.instantiate, bind, Except.bind] using aliasEq
  simp only [Lambda.LTy.instantiateWithCheck, resolve, bind, Except.bind] at success
  split at success
  · contradiction
  · split at success
    · exact (Prod.mk.injEq _ _ _ _).mp (Except.ok.inj success).symm
    · contradiction

private theorem checkedMonoTypes_eq (context : Core.Expression.TyContext)
    (types : List Lambda.LMonoTy) (env final : Core.Expression.TyEnv) (checked : List Lambda.LMonoTy)
    (aliasFree : ∀ ty ∈ types, ty.aliasFree env.context.aliases)
    (success : Lambda.LMonoTySignature.instantiate.go context env (types.map (Lambda.LTy.forAll [])) =
      .ok (checked, final)) :
    checked = types := by
  induction types generalizing env checked final with
  | nil =>
    exact (congrArg Prod.fst (Except.ok.inj success)).symm
  | cons ty types ih =>
    simp only [List.map_cons, Lambda.LMonoTySignature.instantiate.go, bind, Except.bind] at success
    split at success
    · contradiction
    · rename_i first firstRan
      obtain ⟨checkedType, afterFirst⟩ := first
      obtain ⟨typeEq, envEq⟩ := instantiateMonoType (aliasFree ty (by simp)) firstRan
      subst checkedType
      subst afterFirst
      split at success
      · contradiction
      · rename_i tail checkedTail
        obtain ⟨checkedTypes, afterTail⟩ := tail
        have tailEq := ih _ _ _ (fun t present => aliasFree t (List.mem_cons_of_mem _ present)) checkedTail
        have same : ty :: checkedTypes = checked := congrArg Prod.fst (Except.ok.inj success)
        rw [← same, tailEq]

private theorem instantiateClosedSignature_eq (context : Core.Expression.TyContext)
    (env final : Core.Expression.TyEnv) (signature checked : ListMap Core.CoreIdent Lambda.LMonoTy)
    (closed : ∀ ty ∈ signature.values, ty.freeVars = [])
    (aliasFree : ∀ ty ∈ signature.values, ty.aliasFree env.context.aliases)
    (success : Lambda.LMonoTySignature.instantiate context env [] signature = .ok (checked, final)) :
    checked = signature := by
  simp only [Lambda.LMonoTySignature.instantiate, instantiateEmptySignature _ _ closed,
    bind, Except.bind] at success
  split at success
  · contradiction
  · rename_i result ran
    obtain ⟨types, last⟩ := result
    have typesEq := checkedMonoTypes_eq _ _ _ _ _ aliasFree ran
    have same : signature.keys.zip types = checked := congrArg Prod.fst (Except.ok.inj success)
    have zipped (formals : ListMap Core.CoreIdent Lambda.LMonoTy) :
        formals.keys.zip formals.values = formals := by
      induction formals with
      | nil => rfl
      | cons first rest ih =>
        cases first
        exact congrArg (List.cons _) ih
    rw [← same, typesEq, zipped]

private theorem instantiateClosedHeader_eq (context : Core.Expression.TyContext)
    (env final : Core.Expression.TyEnv) (header : Core.Procedure.Header)
    (inputs outputs : ListMap Core.CoreIdent Lambda.LMonoTy)
    (monomorphic : header.typeArgs = [])
    (closed : ∀ ty ∈ (header.inputs ++ header.outputs).values, ty.freeVars = [])
    (aliasFree : ∀ ty ∈ (header.inputs ++ header.outputs).values, ty.aliasFree env.context.aliases)
    (success : Core.Procedure.Header.instantiate context env header = .ok (inputs, outputs, final)) :
    inputs = header.inputs ∧ outputs = header.outputs := by
  simp only [Core.Procedure.Header.instantiate, monomorphic, bind, Except.bind] at success
  split at success
  · contradiction
  · rename_i result ran
    obtain ⟨signature, next⟩ := result
    have equal := instantiateClosedSignature_eq context env next _ signature closed aliasFree ran
    subst signature
    have parts : (header.inputs ++ header.outputs).splitAt header.inputs.length =
        (header.inputs, header.outputs) := by
      change (header.inputs.toList ++ header.outputs.toList).splitAt header.inputs.toList.length = _
      rw [List.splitAt_eq, List.take_left, List.drop_left]
      rfl
    dsimp only at success
    rw [parts] at success
    have equal := congrArg Prod.fst (Except.ok.inj success)
    have equalOutputs := congrArg (fun p => p.2.1) (Except.ok.inj success)
    exact ⟨equal.symm, equalOutputs.symm⟩

/-- Every value of an admitted scalar sort has a Core literal representation. -/
theorem coreValue?_isSome_iff (value : Value) :
    (coreValue? value).isSome = value.sort.hasCoreLiteral := by
  obtain ⟨sort, data⟩ := value
  cases sort with
  | bitvec => rfl
  | «variable» => rfl
  | con name arguments =>
      cases arguments with
      | cons => simp [coreValue?, coreValueIn?, ValueType.hasCoreLiteral]
      | nil =>
        by_cases bool : name = "bool"
        · subst name; rfl
        by_cases int : name = "int"
        · subst name; rfl
        by_cases real : name = "real"
        · subst name; rfl
        by_cases string : name = "string"
        · subst name; rfl
        simp [coreValue?, coreValueIn?, ValueType.hasCoreLiteral, bool, int, real, string]

/-- Type-correct values for scalar bindings can all be supplied to Core as
literals, with the same number of values and in the same order. -/
theorem reifyValues_of_valuesMatch (bindings : List Binding) (values : List Value)
    (scalar : ∀ binding ∈ bindings, binding.sort.hasCoreLiteral = true)
    (typed : valuesMatch bindings values = true) :
    ∃ represented, values.mapM coreValue? = some represented ∧
      represented.length = bindings.length := by
  induction bindings generalizing values with
  | nil =>
    cases values <;> simp_all [valuesMatch]
  | cons binding rest ih =>
    cases values with
    | nil => simp [valuesMatch] at typed
    | cons value values =>
      simp only [valuesMatch, List.length_cons, List.zip_cons_cons, List.all_cons,
        Bool.and_eq_true, beq_iff_eq, Nat.succ.injEq] at typed
      obtain ⟨size, sort, typedRest⟩ := typed
      have literal : (coreValue? value).isSome = true := by
        rw [coreValue?_isSome_iff, ← sort]
        exact scalar binding (by simp)
      obtain ⟨expression, reified⟩ := Option.isSome_iff_exists.mp literal
      have restMatches : valuesMatch rest values = true := by
        simp only [valuesMatch, Bool.and_eq_true, beq_iff_eq, size, typedRest, and_self]
      obtain ⟨expressions, reifiedRest, length⟩ := ih values
        (fun b h => scalar b (List.mem_cons_of_mem _ h)) restMatches
      refine ⟨expression :: expressions, ?_, by simp [length]⟩
      simp [List.mapM_cons, reified, reifiedRest, bind, Option.bind, pure]

/-! ## The generated procedure interface -/

/-- Encode the name and scalar type of a source binding as a Core formal. -/
def scalarFormal? (binding : Binding) : Option (Core.CoreIdent × Lambda.LMonoTy) :=
  let id : Core.CoreIdent := ⟨binding.name, ()⟩
  match binding.sort with
  | .bool => some (id, .bool)
  | .int => some (id, .int)
  | .string => some (id, .string)
  | .real => some (id, .real)
  | .bitvec width => some (id, .bitvec width)
  | _ => none

/-- The checked header passes all globals as inputs, passes modified globals
back as outputs, and preserves the order of explicit procedure parameters.
Names are distinct across the three source lists, and current slots cannot
collide with the reserved names used for snapshots. -/
structure ProcedureLayout {E S : Type} (globals : List Binding) (source : InterpProcedure E S)
    (target : Core.Procedure) : Prop where
  inputs : ∃ orderedGlobals, orderedGlobals.Perm globals ∧
    (orderedGlobals ++ source.inputs).mapM scalarFormal? = some target.header.inputs.toList
  outputs : ∃ modifiedGlobals, (∀ b ∈ modifiedGlobals, b ∈ globals) ∧
    (modifiedGlobals.map (·.name)).Perm source.contract.modifies ∧
    (modifiedGlobals ++ source.outputs).mapM scalarFormal? = some target.header.outputs.toList
  distinct : ((globals ++ source.inputs ++ source.outputs).map (·.name)).Nodup
  snapshotNamesFresh : ∀ name ∈ source.contract.modifies,
    (Core.CoreIdent.mkOld name).name ∉ (globals ++ source.inputs ++ source.outputs).map (·.name)


private theorem addLocal_name (range : SourceRange) (name : String) (ty : Boole.Type)
    (initial final : Scope) (binding : Binding)
    (added : addLocal range name ty initial = .ok (binding, final)) :
    binding.name = name := by
  unfold addLocal at added
  simp only [bind, StateT.bind, Except.bind] at added
  cases sorted : sourceSort ty initial with
  | error error => simp [sorted] at added
  | ok result =>
    obtain ⟨sort, afterSort⟩ := result
    simp only [sorted, bind, StateT.bind, Except.bind] at added
    cases freshResult : fresh range ⟨name, sort⟩ afterSort with
    | error error => simp [freshResult] at added
    | ok result =>
      obtain ⟨_, afterFresh⟩ := result
      simp only [freshResult, bind, StateT.bind, Except.bind] at added
      simp only [modify, modifyGet, MonadStateOf.modifyGet,
        StateT.modifyGet, pure, StateT.pure, Except.pure] at added
      have bindingEq : (⟨name, sort⟩ : Binding) = binding :=
        congrArg Prod.fst (Except.ok.inj added)
      simpa using congrArg Binding.name bindingEq.symm

private def inputParameter (parameter : BooleDDM.Binding SourceRange) : InterpM Binding :=
  match parameter with
  | .mkBinding range name (.expr ty) => addLocal range name.val ty
  | parameter => reject default s!"Unsupported parameter: {repr parameter}"

private theorem inputParameter_name (parameter : BooleDDM.Binding SourceRange)
    (initial final : Scope) (binding : Binding)
    (added : inputParameter parameter initial = .ok (binding, final)) :
    binding.name = bindingName parameter := by
  cases parameter with
  | mkBinding range name type =>
    cases type with
    | expr ty => exact addLocal_name range name.val ty initial final binding added
    | type range => simp [inputParameter, reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.map, Functor.map] at added
  | outBinding range name type => simp [inputParameter, reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.map, Functor.map] at added
  | inoutBinding range name type => simp [inputParameter, reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.map, Functor.map] at added
  | casesBinding range name type => simp [inputParameter, reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.map, Functor.map] at added

private theorem mapM_preserves_names {α : Type} (items : List α)
    (run : α → InterpM Binding) (name : α → String)
    (one : ∀ item initial final binding, run item initial = .ok (binding, final) →
      binding.name = name item)
    (initial final : Scope) (bindings : List Binding)
    (mapped : items.mapM run initial = .ok (bindings, final)) :
    bindings.map Binding.name = items.map name := by
  induction items generalizing initial bindings with
  | nil =>
    simp only [List.mapM_nil, pure, StateT.pure, Except.pure] at mapped
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj mapped)
    rfl
  | cons item rest ih =>
    simp only [List.mapM_cons, bind, StateT.bind, Except.bind] at mapped
    cases first : run item initial with
    | error error => simp [first] at mapped
    | ok pair =>
      obtain ⟨head, next⟩ := pair
      cases tail : rest.mapM run next with
      | error error => simp [first, tail] at mapped
      | ok result =>
        obtain ⟨tailBindings, last⟩ := result
        simp only [first, tail, pure, StateT.pure, Except.pure] at mapped
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj mapped)
        simp [one item _ _ _ first, ih _ _ tail]

private theorem inputBindings_names (parameters : BooleDDM.Bindings SourceRange)
    (initial final : Scope) (bindings : List Binding)
    (interpreted : inputBindings parameters initial = .ok (bindings, final)) :
    bindings.map Binding.name = (bindingsToList parameters).map bindingName := by
  cases parameters with
  | mkBindings range annotated =>
    cases annotated with
    | mk annotation values =>
      change values.toList.mapM inputParameter initial = .ok (bindings, final) at interpreted
      have mapped : values.toList.mapM inputParameter initial = .ok (bindings, final) := interpreted
      simpa [bindingsToList] using
        mapM_preserves_names values.toList inputParameter bindingName
          inputParameter_name initial final bindings mapped

/-- Lowering a term binding preserves its source name in the Core formal. -/
private theorem toCoreBinding_name (binding : BooleDDM.Binding SourceRange)
    (state : TranslateState) (formal : Core.Expression.Ident × Lambda.LMonoTy)
    (final : TranslateState)
    (lowered : toCoreBinding binding state = .ok (formal, final)) :
    formal.1.name = bindingName binding := by
  cases binding with
  | mkBinding range name type
  | outBinding range name type
  | inoutBinding range name type
  | casesBinding range name type =>
    cases type with
    | type range =>
      simp [toCoreBinding, bind, StateT.bind, Except.bind, get, getThe,
        MonadStateOf.get, StateT.get, throwAt, throw, throwThe,
        MonadExceptOf.throw, StateT.lift, pure, StateT.pure, Except.pure] at lowered
    | expr ty =>
      simp only [toCoreBinding, bind, StateT.bind, Except.bind] at lowered
      cases converted : toCoreMonoType ty state with
      | error error => simp [converted] at lowered
      | ok pair =>
        obtain ⟨coreType, next⟩ := pair
        simp only [converted, pure, StateT.pure, Except.pure] at lowered
        obtain ⟨formalEq, stateEq⟩ := Prod.mk.inj (Except.ok.inj lowered)
        change formal.1.name = name.val
        exact congrArg (fun ident : Core.Expression.Ident => ident.name)
          (congrArg Prod.fst formalEq).symm

/-- The lowerer's binding traversal preserves declaration order and names. -/
private theorem toCoreBindings_names (bindings : List (BooleDDM.Binding SourceRange))
    (state final : TranslateState) (formals : List (Core.Expression.Ident × Lambda.LMonoTy))
    (lowered : bindings.mapM toCoreBinding state = .ok (formals, final)) :
    formals.map (fun formal => formal.1.name) = bindings.map bindingName := by
  induction bindings generalizing state formals with
  | nil =>
    simp only [List.mapM_nil, pure, StateT.pure, Except.pure] at lowered
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj lowered)
    rfl
  | cons binding rest ih =>
    simp only [List.mapM_cons, bind, StateT.bind, Except.bind, pure, StateT.pure,
      Except.pure] at lowered
    cases first : toCoreBinding binding state with
    | error error => simp [first] at lowered
    | ok pair =>
      obtain ⟨formal, next⟩ := pair
      cases tail : rest.mapM toCoreBinding next with
      | error error => simp [first, tail] at lowered
      | ok result =>
        obtain ⟨tailFormals, last⟩ := result
        simp only [first, tail, pure, StateT.pure, Except.pure] at lowered
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj lowered)
        simp [toCoreBinding_name _ _ _ _ first, ih _ _ tail]

private theorem scalarFormal_name (binding : Binding) (formal : Core.CoreIdent × Lambda.LMonoTy)
    (encoded : scalarFormal? binding = some formal) : formal.1.name = binding.name := by
  unfold scalarFormal? at encoded
  split at encoded <;> first
    | contradiction
    | exact congrArg (fun pair : Core.CoreIdent × Lambda.LMonoTy => pair.1.name)
        (Option.some.inj encoded).symm

private theorem scalarFormals_names (bindings : List Binding)
    (formals : List (Core.CoreIdent × Lambda.LMonoTy))
    (encoded : bindings.mapM scalarFormal? = some formals) :
    formals.map (fun pair => pair.1.name) = bindings.map (·.name) := by
  induction bindings generalizing formals with
  | nil =>
    obtain rfl := Option.some.inj encoded
    rfl
  | cons binding rest ih =>
    simp only [List.mapM_cons, bind, Option.bind, pure] at encoded
    cases first : scalarFormal? binding with
    | none => simp [first] at encoded
    | some formal =>
      cases tail : rest.mapM scalarFormal? with
      | none => simp [first, tail] at encoded
      | some more =>
        have same : formal :: more = formals := by simpa [first, tail] using encoded
        subst formals
        simp [scalarFormal_name _ _ first, ih more tail]

private theorem scalarFormal_type_matches (binding : Binding) (value : Value)
    (formal : Core.CoreIdent × Lambda.LMonoTy) (encoded : scalarFormal? binding = some formal) :
    matchesCoreType value formal.2 = (value.sort == binding.sort) := by
  unfold scalarFormal? at encoded
  split at encoded
  all_goals try contradiction
  all_goals
    obtain rfl := Option.some.inj encoded
    unfold matchesCoreType
    split <;> simp_all [Lambda.LMonoTy.bool, Lambda.LMonoTy.int,
      Lambda.LMonoTy.string, Lambda.LMonoTy.real]
  all_goals
    first
    | (apply Bool.eq_iff_iff.mpr
       simp only [beq_iff_eq, ValueType.bitvec.injEq]
       done)
    | apply beq_eq_false_iff_ne.mpr
      intro same
      simp_all

private theorem scalarFormals_valuesMatch (bindings : List Binding)
    (formals : List (Core.CoreIdent × Lambda.LMonoTy)) (values : List Value)
    (encoded : bindings.mapM scalarFormal? = some formals) :
    valuesMatch bindings values = true ↔
      formals.length = values.length ∧
        (formals.zip values).all (fun ((_, ty), value) => matchesCoreType value ty) = true := by
  induction bindings generalizing formals values with
  | nil =>
    obtain rfl := Option.some.inj encoded
    cases values <;> simp [valuesMatch]
  | cons binding rest ih =>
    simp only [List.mapM_cons, bind, Option.bind, pure] at encoded
    cases first : scalarFormal? binding with
    | none => simp [first] at encoded
    | some formal =>
      cases tail : rest.mapM scalarFormal? with
      | none => simp [first, tail] at encoded
      | some more =>
        have same : formal :: more = formals := by simpa [first, tail] using encoded
        subst formals
        cases values with
        | nil => simp [valuesMatch]
        | cons value values =>
          have related := ih more values tail
          unfold valuesMatch at related ⊢
          simp only [List.length_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq,
            Nat.succ.injEq, scalarFormal_type_matches _ _ _ first] at related ⊢
          constructor
          · rintro ⟨length, sort, typed⟩
            obtain ⟨size, restTyped⟩ := related.mp ⟨length, typed⟩
            exact ⟨size, sort.symm, restTyped⟩
          · rintro ⟨length, sort, typed⟩
            obtain ⟨size, restTyped⟩ := related.mpr ⟨length, typed⟩
            exact ⟨size, sort.symm, restTyped⟩

private theorem scalarFormals_filter (keep : String → Bool) (bindings : List Binding)
    (formals : List (Core.CoreIdent × Lambda.LMonoTy))
    (encoded : bindings.mapM scalarFormal? = some formals) :
    (bindings.filter (keep ∘ Binding.name)).mapM scalarFormal? =
      some (formals.filter (fun formal => keep formal.1.name)) := by
  induction bindings generalizing formals with
  | nil =>
    obtain rfl := Option.some.inj encoded
    rfl
  | cons binding rest ih =>
    simp only [List.mapM_cons, bind, Option.bind, pure] at encoded
    cases first : scalarFormal? binding with
    | none => simp [first] at encoded
    | some formal =>
      cases tail : rest.mapM scalarFormal? with
      | none => simp [first, tail] at encoded
      | some more =>
        have same : formal :: more = formals := by simpa [first, tail] using encoded
        subst formals
        have restFilter := ih more tail
        simp only [Function.comp_def] at restFilter ⊢
        cases kept : keep binding.name <;>
          simp [scalarFormal_name _ _ first, kept, restFilter, List.mapM_cons, first, bind, Option.bind, pure]

private def coreOutputOnly (target : Core.Procedure) : List (Core.CoreIdent × Lambda.LMonoTy) :=
  target.header.outputs.toList.filter fun (id, _) =>
    !target.header.inputs.toList.any (fun (other, _) => other.name == id.name)

/-- Output-only formals are the encodings of the explicit Boole outputs. -/
private theorem ProcedureLayout.outputOnly {E S : Type} {globals : List Binding}
    {source : InterpProcedure E S}
    {target : Core.Procedure} (layout : ProcedureLayout globals source target) :
    source.outputs.mapM scalarFormal? = some (coreOutputOnly target) := by
  let isOutputOnly : String → Bool :=
    fun name => !target.header.inputs.toList.any (fun (id, _) => id.name == name)
  obtain ⟨orderedGlobals, permutation, inputEncoding⟩ := layout.inputs
  obtain ⟨modifiedGlobals, inGlobals, _, outputEncoding⟩ := layout.outputs
  have names := scalarFormals_names _ _ inputEncoding
  have inInputs (name : String) :
      (target.header.inputs.toList.any (fun (id, _) => id.name == name) = true) ↔
        name ∈ (globals ++ source.inputs).map (·.name) := by
    have order : (target.header.inputs.toList.map (fun pair => pair.1.name)).Perm
        ((globals ++ source.inputs).map (·.name)) := by
      rw [names]
      exact (permutation.append_right _).map _
    rw [← order.mem_iff]
    simp [List.any_eq_true, List.mem_map]
  have noModified : modifiedGlobals.filter (isOutputOnly ∘ Binding.name) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro binding present
    have included : binding.name ∈ (globals ++ source.inputs).map (·.name) :=
      List.mem_map.mpr ⟨binding, List.mem_append_left _ (inGlobals _ present), rfl⟩
    simp [isOutputOnly, (inInputs _).mpr included]
  have allOutputs : source.outputs.filter (isOutputOnly ∘ Binding.name) = source.outputs := by
    apply List.filter_eq_self.mpr
    intro binding present
    have distinct := layout.distinct
    rw [List.map_append] at distinct
    have disjoint := (List.nodup_append.mp distinct).2.2
    have excluded : ¬ target.header.inputs.toList.any (fun (id, _) => id.name == binding.name) = true := by
      intro hit
      exact disjoint binding.name ((inInputs _).mp hit) binding.name (List.mem_map_of_mem present) rfl
    simp [isOutputOnly, excluded]
  have filtered := scalarFormals_filter isOutputOnly _ _ outputEncoding
  simpa [List.filter_append, noModified, allOutputs, isOutputOnly, coreOutputOnly] using filtered

/-- The observable Core output order is exactly the explicit Boole output order. -/
theorem ProcedureLayout.outputNames {globals : List Binding} {source : ProcedureMeaning}
    {target : Core.Procedure} (layout : ProcedureLayout globals source target) :
    (target.header.outputs.toList.filterMap fun (id, _) =>
      if globals.any (fun g => g.name == id.name) then none else some id.name) =
      source.outputs.map (·.name) := by
  let user : String → Bool := fun name => !globals.any (fun g => g.name == name)
  have filterNames (formals : List (Core.CoreIdent × Lambda.LMonoTy)) :
      (formals.filterMap fun (id, _) =>
        if globals.any (fun g => g.name == id.name) then none else some id.name) =
        (formals.map (fun pair => pair.1.name)).filter user := by
    induction formals with
    | nil => rfl
    | cons pair rest ih =>
      obtain ⟨id, ty⟩ := pair
      cases global : globals.any (fun g => g.name == id.name) <;>
        simp only [List.filterMap_cons, List.map_cons, List.filter_cons, user, global,
          Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false, ih]
  obtain ⟨modified, inGlobals, _, encoded⟩ := layout.outputs
  rw [filterNames, scalarFormals_names _ _ encoded, List.map_append, List.filter_append]
  have skipGlobals : (modified.map (·.name)).filter user = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro name member
    obtain ⟨b, inModified, rfl⟩ := List.mem_map.mp member
    have present : globals.any (fun g => g.name == b.name) = true :=
      List.any_eq_true.mpr ⟨b, inGlobals b inModified, by simp⟩
    simp [user, present]
  have keepOutputs : (source.outputs.map (·.name)).filter user = source.outputs.map (·.name) := by
    apply List.filter_eq_self.mpr
    intro name member
    have distinct := layout.distinct
    simp only [List.map_append, List.append_assoc] at distinct
    have disjoint := (List.nodup_append.mp distinct).2.2
    have absent : ¬ globals.any (fun g => g.name == name) = true := by
      intro present
      obtain ⟨binding, included, same⟩ := List.any_eq_true.mp present
      have nameEq : binding.name = name := beq_iff_eq.mp same
      have globalName : name ∈ globals.map (·.name) := List.mem_map.mpr ⟨binding, included, nameEq⟩
      exact disjoint name globalName name (List.mem_append_right _ member) rfl
    simp [user, absent]
  simp [skipGlobals, keepOutputs]

private def coreExplicitInputs (globals : List Binding) (target : Core.Procedure) :
    List (Core.CoreIdent × Lambda.LMonoTy) :=
  target.header.inputs.toList.filter fun (id, _) => !globals.any (fun g => g.name == id.name)

private theorem ProcedureLayout.explicitInputs {globals : List Binding} {source : ProcedureMeaning}
    {target : Core.Procedure} (layout : ProcedureLayout globals source target) :
    source.inputs.mapM scalarFormal? = some (coreExplicitInputs globals target) := by
  let explicit : String → Bool := fun name => !globals.any (fun g => g.name == name)
  obtain ⟨orderedGlobals, permutation, encoded⟩ := layout.inputs
  have skip : orderedGlobals.filter (explicit ∘ Binding.name) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro binding present
    have global : globals.any (fun g => g.name == binding.name) = true :=
      List.any_eq_true.mpr ⟨binding, permutation.mem_iff.mp present, by simp⟩
    simp [explicit, global]
  have keep : source.inputs.filter (explicit ∘ Binding.name) = source.inputs := by
    apply List.filter_eq_self.mpr
    intro binding present
    have distinct := layout.distinct
    simp only [List.map_append, List.append_assoc] at distinct
    have disjoint := (List.nodup_append.mp distinct).2.2
    have absent : ¬ globals.any (fun g => g.name == binding.name) = true := by
      intro global
      obtain ⟨g, included, eq⟩ := List.any_eq_true.mp global
      have gName : binding.name ∈ globals.map (·.name) :=
        List.mem_map.mpr ⟨g, included, beq_iff_eq.mp eq⟩
      have iName : binding.name ∈ source.inputs.map (·.name) := List.mem_map_of_mem present
      exact disjoint binding.name gName binding.name (List.mem_append_left _ iName) rfl
    simp [explicit, absent]
  simpa [List.filter_append, skip, keep, explicit, coreExplicitInputs] using
    scalarFormals_filter explicit _ _ encoded

private theorem valuesMatch_append {left right : List Binding} {xs ys : List Value}
    (first : valuesMatch left xs = true) (second : valuesMatch right ys = true) :
    valuesMatch (left ++ right) (xs ++ ys) = true := by
  obtain ⟨firstLength, firstTypes⟩ := Bool.and_eq_true_iff.mp first
  obtain ⟨secondLength, secondTypes⟩ := Bool.and_eq_true_iff.mp second
  have leftLength : left.length = xs.length := beq_iff_eq.mp firstLength
  have rightLength : right.length = ys.length := beq_iff_eq.mp secondLength
  simp [valuesMatch, List.zip_append leftLength, leftLength, rightLength, firstTypes, secondTypes]

private theorem bindValues_append {left right : List Binding} {xs ys : List Value}
    (first : left.length = xs.length) :
    bindValues (left ++ right) (xs ++ ys) = bindValues left xs ++ bindValues right ys := by
  simp only [bindValues, List.zip_append first, List.map_append]

private theorem lookup_bindValues_of_member {bindings : List Binding} {values : List Value}
    (binding : Binding) (present : binding ∈ bindings)
    (distinct : (bindings.map (·.name)).Nodup) (typed : valuesMatch bindings values = true) :
    ∃ value, (bindValues bindings values).lookup binding.name = some value ∧
      value.sort = binding.sort := by
  induction bindings generalizing values with
  | nil => simp at present
  | cons first rest ih =>
    cases values with
    | nil => simp [valuesMatch] at typed
    | cons value tail =>
      simp only [valuesMatch, List.length_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true,
        beq_iff_eq, Nat.succ.injEq] at typed
      obtain ⟨length, firstType, tailTypes⟩ := typed
      rcases List.mem_cons.mp present with rfl | later
      · exact ⟨value, by simp [bindValues, Store.lookup], firstType.symm⟩
      · simp only [List.map_cons, List.nodup_cons] at distinct
        have different : first.name ≠ binding.name := by
          intro equal
          exact distinct.1 (equal.symm ▸ List.mem_map_of_mem later)
        obtain ⟨found, lookup, sort⟩ := ih (values := tail) later distinct.2
          (by simp [valuesMatch, length, tailTypes])
        exact ⟨found, by simpa [bindValues, Store.lookup, different] using lookup, sort⟩

private theorem readValues_of_typed_lookup (bindings : List Binding) (store : Store)
    (available : ∀ binding ∈ bindings, ∃ value, store.lookup binding.name = some value ∧
      value.sort = binding.sort) :
    ∃ values, readValues bindings store = some values ∧ valuesMatch bindings values = true := by
  induction bindings with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons binding rest ih =>
    obtain ⟨value, lookup, sort⟩ := available binding (by simp)
    obtain ⟨values, readRest, typedRest⟩ :=
      ih (fun b present => available b (List.mem_cons_of_mem _ present))
    have typedHead : binding.sort = value.sort := sort.symm
    refine ⟨value :: values, ?_, ?_⟩
    · have restEq : rest.mapM (fun b => store.lookup b.name) = some values := readRest
      simp [readValues, List.mapM_cons, lookup, restEq, bind, Option.bind, pure]
    · simp only [valuesMatch, List.length_cons, List.zip_cons_cons, List.all_cons,
        Bool.and_eq_true, beq_iff_eq, Nat.succ.injEq] at typedRest ⊢
      exact ⟨typedRest.1, typedHead, typedRest.2⟩

private theorem lookup_eq_listLookup (store : Store) (name : String) :
    store.lookup name = List.lookup name store := by
  rw [List.lookup_eq_findSome?]
  unfold Store.lookup
  congr 1
  funext binding
  simp only [beq_iff_eq]
  by_cases same : name = binding.1
  · simp [same]
  · simp [same, Ne.symm same]

private theorem scalarFormals_are_scalar (bindings : List Binding)
    (formals : List (Core.CoreIdent × Lambda.LMonoTy))
    (encoded : bindings.mapM scalarFormal? = some formals) :
    ∀ binding ∈ bindings, binding.sort.hasCoreLiteral = true := by
  induction bindings generalizing formals with
  | nil => simp
  | cons binding rest ih =>
    simp only [List.mapM_cons, bind, Option.bind, pure] at encoded
    cases first : scalarFormal? binding with
    | none => simp [first] at encoded
    | some formal =>
      cases tail : rest.mapM scalarFormal? with
      | none => simp [first, tail] at encoded
      | some more =>
        intro b present
        rcases List.mem_cons.mp present with rfl | later
        · unfold scalarFormal? at first
          split at first <;> simp_all [ValueType.hasCoreLiteral]
        · exact ih more tail b later

private def coreSuppliedArguments (globals : List Binding) (target : Core.Procedure) (input : Invocation) :
    Option (List Value) :=
  let supplied := bindValues globals input.globals ++
    ((coreExplicitInputs globals target).zip input.arguments).map (fun ((id, _), value) => (id.name, value))
  target.header.inputs.toList.mapM (fun (id, _) => supplied.lookup id.name)

private theorem coreSuppliedArguments_by_name {globals : List Binding} {source : ProcedureMeaning}
    {target : Core.Procedure} (layout : ProcedureLayout globals source target)
    (input : Invocation) (typed : valuesMatch globals input.globals = true) :
    coreSuppliedArguments globals target input =
      (target.header.inputs.keys.map (·.name)).mapM
        (fun name => (bindValues (globals ++ source.inputs) (input.globals ++ input.arguments)).lookup name) := by
  have explicitNames := scalarFormals_names _ _ layout.explicitInputs
  have explicitValues :
      ((coreExplicitInputs globals target).zip input.arguments).map
        (fun ((id, _), value) => (id.name, value)) = bindValues source.inputs input.arguments := by
    have coreZip := List.zip_map_left (f := fun pair : Core.CoreIdent × Lambda.LMonoTy => pair.1.name)
      (l₁ := coreExplicitInputs globals target) (l₂ := input.arguments)
    have sourceZip := List.zip_map_left (f := Binding.name)
      (l₁ := source.inputs) (l₂ := input.arguments)
    exact coreZip.symm.trans ((congrArg (fun names => names.zip input.arguments) explicitNames).trans sourceZip)
  have suppliedEq : bindValues globals input.globals ++ bindValues source.inputs input.arguments =
      bindValues (globals ++ source.inputs) (input.globals ++ input.arguments) :=
    (bindValues_append (beq_iff_eq.mp (Bool.and_eq_true_iff.mp typed).1)).symm
  have inputKeys : target.header.inputs.keys = target.header.inputs.toList.map Prod.fst :=
    ListMap.keys_eq_map_fst _
  unfold coreSuppliedArguments
  rw [explicitValues, suppliedEq, inputKeys]
  simp only [List.mapM_map, Function.comp_def, lookup_eq_listLookup]

private theorem coreIdent_name_iff (left right : Core.CoreIdent) :
    left.name = right.name ↔ left = right := by
  obtain ⟨left, ⟨⟩⟩ := left
  obtain ⟨right, ⟨⟩⟩ := right
  simp

private theorem lookup_reified_zip (keys : List Core.CoreIdent) (values : List Value)
    (literals : List Core.Expression.Val) (encoded : values.mapM coreValue? = some literals)
    (id : Core.CoreIdent) :
    (keys.zip literals).lookup id =
      (((keys.map (·.name)).zip values).lookup id.name).bind coreValue? := by
  induction keys generalizing values literals with
  | nil => rfl
  | cons key keys ih =>
    cases values with
    | nil =>
      obtain rfl := Option.some.inj encoded
      rfl
    | cons value values =>
      simp only [List.mapM_cons, bind, Option.bind, pure] at encoded
      cases first : coreValue? value with
      | none => simp [first] at encoded
      | some literal =>
        cases tail : values.mapM coreValue? with
        | none => simp [first, tail] at encoded
        | some rest =>
          have same : literal :: rest = literals := by simpa [first, tail] using encoded
          subst literals
          by_cases equal : id = key
          · subst id
            simp [first]
          · have different : id.name ≠ key.name := fun same => equal ((coreIdent_name_iff _ _).mp same)
            have unequal : (id == key) = false := beq_eq_false_iff_ne.mpr equal
            have nameTest : (id.name == key.name) = false := beq_eq_false_iff_ne.mpr different
            simp [List.lookup, unequal, nameTest, ih values rest tail]

private theorem lookup_zip_mapM {names : List String} {values : List Value}
    {lookup : String → Option Value} (read : names.mapM lookup = some values) (name : String) :
    (names.zip values).lookup name = if name ∈ names then lookup name else none := by
  induction names generalizing values with
  | nil => simp
  | cons key keys ih =>
    simp only [List.mapM_cons, bind, Option.bind, pure] at read
    cases first : lookup key with
    | none => simp [first] at read
    | some value =>
      cases tail : keys.mapM lookup with
      | none => simp [first, tail] at read
      | some more =>
        have same : value :: more = values := by simpa [first, tail] using read
        subst values
        by_cases equal : name = key
        · subst key
          simp [first]
        · have test : (name == key) = false := beq_eq_false_iff_ne.mpr equal
          simp [List.lookup, equal, test, ih tail]

private theorem lookup_bindValues_none (bindings : List Binding) (values : List Value)
    (name : String) (absent : name ∉ bindings.map (·.name)) :
    (bindValues bindings values).lookup name = none := by
  rw [lookup_eq_listLookup, List.lookup_eq_none_iff]
  intro pair present
  obtain ⟨⟨binding, value⟩, zipped, rfl⟩ := List.mem_map.mp present
  have different : name ≠ binding.name :=
    fun same => absent (same.symm ▸ List.mem_map_of_mem (List.of_mem_zip zipped).1)
  simp [bne, different]

private theorem installedInputs_lookup {globals : List Binding} {source : ProcedureMeaning}
    {target : Core.Procedure} (layout : ProcedureLayout globals source target)
    (input : Invocation) (typed : valuesMatch globals input.globals = true)
    (arguments : List Value) (literals : List Core.Expression.Val)
    (supplied : coreSuppliedArguments globals target input = some arguments)
    (encoded : arguments.mapM coreValue? = some literals) (id : Core.CoreIdent) :
    (target.header.inputs.keys.zip literals).lookup id =
      ((bindValues (globals ++ source.inputs) (input.globals ++ input.arguments)).lookup id.name).bind
        coreValue? := by
  rw [lookup_reified_zip _ _ _ encoded, lookup_zip_mapM ((coreSuppliedArguments_by_name layout input typed).symm.trans supplied)]
  split
  · rfl
  · rename_i absent
    obtain ⟨orderedGlobals, perm, inputEncoding⟩ := layout.inputs
    have names : target.header.inputs.keys.map (·.name) = (orderedGlobals ++ source.inputs).map (·.name) := by
      have inputKeys : target.header.inputs.keys = target.header.inputs.toList.map Prod.fst :=
        ListMap.keys_eq_map_fst _
      rw [inputKeys, List.map_map]
      exact scalarFormals_names _ _ inputEncoding
    rw [names] at absent
    have noBinding : id.name ∉ (globals ++ source.inputs).map (·.name) :=
      fun hit => absent (((perm.append_right _).map Binding.name).mem_iff.mpr hit)
    rw [lookup_bindValues_none _ _ _ noBinding]

private theorem optionMapM_length {f : α → Option β} {source : List α} {target : List β}
    (run : source.mapM f = some target) : source.length = target.length := by
  induction source generalizing target with
  | nil =>
    obtain rfl := Option.some.inj run
    rfl
  | cons value rest ih =>
    simp only [List.mapM_cons, bind, Option.bind, pure] at run
    cases first : f value with
    | none => simp [first] at run
    | some x =>
      cases tail : rest.mapM f with
      | none => simp [first, tail] at run
      | some xs =>
        have same : x :: xs = target := by simpa [first, tail] using run
        subst target
        simp [ih tail]

private theorem coreOutputOnly_keys (target : Core.Procedure) :
    Imperative.Calls.outputOnlyParams (P := Core.Expression) target.header =
      (coreOutputOnly target).map Prod.fst := by
  have inputContains (id : Core.CoreIdent) :
      target.header.inputs.keys.contains id =
        target.header.inputs.toList.any (fun (other, _) => other.name == id.name) := by
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro key
      have member := List.contains_iff_mem.mp key
      rw [ListMap.keys_eq_map_fst] at member
      obtain ⟨binding, present, same⟩ := List.mem_map.mp member
      exact List.any_eq_true.mpr ⟨binding, present, beq_iff_eq.mpr ((coreIdent_name_iff _ _).mpr same)⟩
    · intro present
      obtain ⟨binding, included, same⟩ := List.any_eq_true.mp present
      apply List.contains_iff_mem.mpr
      rw [ListMap.keys_eq_map_fst]
      exact List.mem_map.mpr ⟨binding, included, (coreIdent_name_iff _ _).mp (beq_iff_eq.mp same)⟩
  change target.header.outputs.keys.filter (fun id => !target.header.inputs.keys.contains id) = _
  have outputKeys : target.header.outputs.keys = target.header.outputs.toList.map Prod.fst :=
    ListMap.keys_eq_map_fst _
  rw [outputKeys, List.filter_map]
  simp only [coreOutputOnly, inputContains, Function.comp_def]

private theorem installedOutputs_lookup {globals : List Binding} {source : ProcedureMeaning}
    {target : Core.Procedure} (layout : ProcedureLayout globals source target)
    (outputs : List Value) (literals : List Core.Expression.Val)
    (encoded : outputs.mapM coreValue? = some literals) (id : Core.CoreIdent) :
    (((Imperative.Calls.outputOnlyParams (P := Core.Expression) target.header).zip literals).lookup id) =
      ((bindValues source.outputs outputs).lookup id.name).bind coreValue? := by
  rw [lookup_reified_zip _ _ _ encoded, coreOutputOnly_keys, List.map_map]
  change ((((coreOutputOnly target).map (fun pair => pair.1.name)).zip outputs).lookup id.name).bind
    coreValue? = _
  rw [scalarFormals_names _ _ layout.outputOnly, List.zip_map_left, lookup_eq_listLookup]
  rfl

private theorem lookup_bindValues_isSome_mem {bindings : List Binding} {values : List Value}
    {name : String} {value : Value} (found : (bindValues bindings values).lookup name = some value) :
    name ∈ bindings.map (·.name) := by
  by_cases member : name ∈ bindings.map (·.name)
  · exact member
  · rw [lookup_bindValues_none _ _ _ member] at found
    contradiction

/-- The zipped Core input and output slots agree with the current source
slots. Formal-name disjointness allows the two stores to use different
lookup orders. -/
private theorem installedCurrentSlots_eq_source {globals : List Binding} {source : ProcedureMeaning}
    {target : Core.Procedure} (layout : ProcedureLayout globals source target)
    (input : Invocation) (outputs arguments : List Value)
    (globalsMatch : valuesMatch globals input.globals = true)
    (coreArguments coreOutputs : List Core.Expression.Val)
    (supplied : coreSuppliedArguments globals target input = some arguments)
    (argumentLiterals : arguments.mapM coreValue? = some coreArguments)
    (outputLiterals : outputs.mapM coreValue? = some coreOutputs) :
    (fun id => (((Imperative.Calls.outputOnlyParams (P := Core.Expression)
          target.header).zip coreOutputs).lookup id).or
        ((target.header.inputs.keys.zip coreArguments).lookup id)) =
      coreStore { initialState globals source input outputs with snapshots := [] } := by
  funext id
  rw [installedOutputs_lookup layout _ _ outputLiterals,
    installedInputs_lookup layout input globalsMatch _ _ supplied argumentLiterals,
    bindValues_append (beq_iff_eq.mp (Bool.and_eq_true_iff.mp globalsMatch).1), Store.lookup_append]
  have distinct := layout.distinct
  simp only [List.map_append, List.append_assoc] at distinct
  have splitGlobals := (List.nodup_append.mp distinct).2.2
  have splitLocals := (List.nodup_append.mp (List.nodup_append.mp distinct).2.1).2.2
  let globalValue : Option Value := (bindValues globals input.globals).lookup id.name
  let param := (bindValues source.inputs input.arguments).lookup id.name
  let output := (bindValues source.outputs outputs).lookup id.name
  change (output.bind coreValue?).or ((globalValue.or param).bind coreValue?) =
    coreStore { initialState globals source input outputs with snapshots := [] } id
  unfold coreStore
  simp only [initialState, Store.lookup_append, List.findSome?_nil]
  change (output.bind coreValue?).or ((globalValue.or param).bind coreValue?) =
    (match param.or output with
      | some value => coreValue? value
      | none => match globalValue with | some value => coreValue? value | none => none)
  have noShadowedGlobal : ∀ value, globalValue = some value →
      id.name ∉ source.inputs.map (·.name) ++ source.outputs.map (·.name) := by
    intro value found localName
    exact splitGlobals id.name (lookup_bindValues_isSome_mem found) id.name localName rfl
  have noShadowedOutput : ∀ value, output = some value →
      id.name ∉ source.inputs.map (·.name) := by
    intro value found localName
    exact splitLocals id.name localName id.name (lookup_bindValues_isSome_mem found) rfl
  cases globalEq : globalValue with
  | some value =>
    have absent := noShadowedGlobal value globalEq
    have paramEq : param = none := lookup_bindValues_none _ _ _ (fun h => absent (List.mem_append_left _ h))
    have outEq : output = none := lookup_bindValues_none _ _ _ (fun h => absent (List.mem_append_right _ h))
    simp [paramEq, outEq]
  | none =>
    cases outEq : output with
    | some value =>
      have paramEq : param = none := lookup_bindValues_none _ _ _ (noShadowedOutput value outEq)
      simp [paramEq]
    | none =>
      cases param <;> rfl

private theorem mem_keys_iff_name (formals : ListMap Core.CoreIdent Lambda.LMonoTy)
    (id : Core.CoreIdent) :
    id ∈ formals.keys ↔ id.name ∈ formals.toList.map (fun pair => pair.1.name) := by
  have keys : formals.keys = formals.toList.map Prod.fst := ListMap.keys_eq_map_fst _
  rw [keys, List.mem_map, List.mem_map]
  exact exists_congr (fun pair => and_congr_right (fun _ => (coreIdent_name_iff _ _).symm))

private theorem ProcedureLayout.inoutNames {E S : Type} {globals : List Binding}
    {source : InterpProcedure E S}
    {target : Core.Procedure} (layout : ProcedureLayout globals source target) (id : Core.CoreIdent) :
    id ∈ Imperative.Calls.inoutParams (P := Core.Expression) target.header ↔
      id.name ∈ source.contract.modifies := by
  obtain ⟨ordered, permuted, encodedInputs⟩ := layout.inputs
  obtain ⟨modified, allGlobals, modifies, encodedOutputs⟩ := layout.outputs
  have distinct := layout.distinct
  simp only [List.map_append, List.append_assoc] at distinct
  have globalLocal := (List.nodup_append.mp distinct).2.2
  have inputOutput := (List.nodup_append.mp (List.nodup_append.mp distinct).2.1).2.2
  change id ∈ target.header.inputs.keys.filter (fun g => target.header.outputs.keys.contains g) ↔ _
  rw [List.mem_filter, List.contains_iff_mem, mem_keys_iff_name, mem_keys_iff_name,
    scalarFormals_names _ _ encodedInputs, scalarFormals_names _ _ encodedOutputs,
    List.map_append, List.map_append, List.mem_append, List.mem_append,
    (permuted.map Binding.name).mem_iff, modifies.mem_iff]
  constructor
  · rintro ⟨inInput, mod | out⟩
    · exact mod
    · rcases inInput with global | arg
      · exact (globalLocal id.name global id.name (List.mem_append_right _ out) rfl).elim
      · exact (inputOutput id.name arg id.name out rfl).elim
  · intro mod
    obtain ⟨binding, present, name⟩ := List.mem_map.mp (modifies.mem_iff.mpr mod)
    exact ⟨Or.inl (List.mem_map.mpr ⟨binding, allGlobals _ present, name⟩), Or.inl mod⟩

private theorem lookup_filter_of_kept (store : Store) (names : List String) (name : String)
    (kept : name ∈ names) :
    Store.lookup (store.filter (fun pair => names.contains pair.1)) name = store.lookup name := by
  induction store with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨key, value⟩ := pair
    by_cases same : key = name
    · subst key
      have keep : names.contains name = true := List.contains_iff_mem.mpr kept
      rw [List.filter_cons_of_pos (p := fun pair : String × Value => names.contains pair.1) keep]
      simp [Store.lookup_cons]
    · by_cases keep : names.contains key = true
      · rw [List.filter_cons_of_pos (p := fun pair : String × Value => names.contains pair.1) keep]
        simpa [Store.lookup_cons, same] using ih
      · rw [List.filter_cons_of_neg (p := fun pair : String × Value => names.contains pair.1) keep]
        simpa [Store.lookup_cons, same] using ih

/-- Core copies its inout slots to reserved old identifiers. Those are the same
values already recorded by Boole's source-level modifies snapshots. -/
private theorem installedSnapshots_eq_source {globals : List Binding} {source : ProcedureMeaning}
    {target : Core.Procedure} (layout : ProcedureLayout globals source target)
    (input : Invocation) (outputs : List Value)
    (globalsMatch : valuesMatch globals input.globals = true) :
    coreStore (initialState globals source input outputs) =
      Core.withOldSnapshots (Imperative.Calls.inoutParams (P := Core.Expression) target.header)
        (coreStore { initialState globals source input outputs with snapshots := [] }) := by
  let state := initialState globals source input outputs
  let inoutSlots := Imperative.Calls.inoutParams (P := Core.Expression) target.header
  funext id
  unfold Core.withOldSnapshots Imperative.Calls.withOldSnapshots
  split
  · rename_i g found
    have modified := (layout.inoutNames g).mp (List.mem_of_find?_eq_some found)
    have oldMatch := List.find?_some found
    have sameId : Core.CoreIdent.mkOld g.name = id := by
      change decide (Core.CoreIdent.mkOld g.name = id) = true at oldMatch
      exact of_decide_eq_true oldMatch
    subst id
    obtain ⟨modifiedGlobals, allGlobals, modifies, _⟩ := layout.outputs
    obtain ⟨binding, present, bindingName⟩ := List.mem_map.mp (modifies.mem_iff.mpr modified)
    have globalMember := allGlobals binding present
    have distinct := layout.distinct
    simp only [List.map_append, List.append_assoc] at distinct
    have globalDistinct := (List.nodup_append.mp distinct).1
    obtain ⟨value, stored, sort⟩ := lookup_bindValues_of_member binding globalMember globalDistinct globalsMatch
    rw [bindingName] at stored
    have localAbsent : state.locals.lookup g.name = none := by
      have disjoint := (List.nodup_append.mp distinct).2.2
      have globalName : g.name ∈ globals.map (·.name) := List.mem_map.mpr ⟨binding, globalMember, bindingName⟩
      simp only [state, initialState, Store.lookup_append]
      rw [lookup_bindValues_none _ _ _ (fun h => disjoint _ globalName _ (List.mem_append_left _ h) rfl),
        lookup_bindValues_none _ _ _ (fun h => disjoint _ globalName _ (List.mem_append_right _ h) rfl)]
      rfl
    have fresh := layout.snapshotNamesFresh g.name modified
    simp only [List.map_append, List.append_assoc] at fresh
    have noLocal : state.locals.lookup (Core.CoreIdent.mkOld g.name).name = none := by
      simp only [state, initialState, Store.lookup_append]
      rw [lookup_bindValues_none _ _ _ (fun h => fresh (by simp [h])),
        lookup_bindValues_none _ _ _ (fun h => fresh (by simp [h]))]
      rfl
    have noGlobal : state.globals.lookup (Core.CoreIdent.mkOld g.name).name = none :=
      lookup_bindValues_none _ _ _ (fun h => fresh (List.mem_append_left _ h))
    have saved : state.snapshots.lookup g.name = some value :=
      (lookup_filter_of_kept _ _ _ modified).trans stored
    obtain ⟨ordered, permuted, encoding⟩ := layout.inputs
    have scalar := scalarFormals_are_scalar _ _ encoding binding
      (List.mem_append_left _ (permuted.mem_iff.mpr globalMember))
    rw [← sort, ← coreValue?_isSome_iff] at scalar
    obtain ⟨expression, represented⟩ := Option.isSome_iff_exists.mp scalar
    rw [coreStore_old state g.name value noLocal noGlobal saved represented]
    have globalStored : state.globals.lookup g.name = some value := stored
    dsimp only [state] at localAbsent globalStored
    simpa [coreStore, localAbsent, globalStored] using represented.symm
  · rename_i found
    have noSnapshot : state.snapshots.findSome? (fun pair =>
        if id.name == (Core.CoreIdent.mkOld pair.1).name then coreValue? pair.2 else none) = none := by
      apply List.findSome?_eq_none_iff.mpr
      rintro ⟨name, value⟩ saved
      have modified : name ∈ source.contract.modifies :=
        List.contains_iff_mem.mp (List.mem_filter.mp saved).2
      let g : Core.CoreIdent := ⟨name, ()⟩
      have included : g ∈ inoutSlots := (layout.inoutNames g).mpr modified
      have different : id.name ≠ (Core.CoreIdent.mkOld name).name := by
        intro equal
        have sameId : id = Core.CoreIdent.mkOld name := (coreIdent_name_iff _ _).mp equal
        exact List.find?_eq_none.mp found g included (by rw [sameId]; exact beq_self_eq_true _)
      simp [different]
    dsimp only [state] at noSnapshot
    simp only [coreStore, noSnapshot, List.findSome?_nil]

private theorem initCallFrame_agrees_of_layout {globals : List Binding} {source : ProcedureMeaning}
    {target : Core.Procedure} (layout : ProcedureLayout globals source target)
    (input : Invocation) (outputs arguments : List Value)
    (globalsMatch : valuesMatch globals input.globals = true)
    (outputsMatch : valuesMatch source.outputs outputs = true)
    (coreArguments coreOutputs : List Core.Expression.Val)
    (supplied : coreSuppliedArguments globals target input = some arguments)
    (argumentLiterals : arguments.mapM coreValue? = some coreArguments)
    (outputLiterals : outputs.mapM coreValue? = some coreOutputs) :
    Core.InitCallFrame target coreArguments coreOutputs
      (coreStore (initialState globals source input outputs)) := by
  have inputLength : target.header.inputs.keys.length = coreArguments.length := by
    have suppliedLength : target.header.inputs.toList.length = arguments.length := optionMapM_length supplied
    rw [ListMap.keys.length]
    exact suppliedLength.trans (optionMapM_length argumentLiterals)
  have outputLength : (Imperative.Calls.outputOnlyParams (P := Core.Expression)
      target.header).length = coreOutputs.length := by
    rw [coreOutputOnly_keys, List.length_map]
    have size := ((scalarFormals_valuesMatch _ _ _ layout.outputOnly).mp outputsMatch).1
    exact size.trans (optionMapM_length outputLiterals)
  obtain ⟨orderedGlobals, permutation, encodedInputs⟩ := layout.inputs
  have allDistinct := layout.distinct
  rw [List.map_append] at allDistinct
  have inputDistinct : target.header.inputs.keys.Nodup := by
    apply List.nodup_of_nodup_map (fun id : Core.CoreIdent => id.name)
    have inputKeys : target.header.inputs.keys = target.header.inputs.toList.map Prod.fst :=
      ListMap.keys_eq_map_fst _
    rw [inputKeys, List.map_map]
    simp only [Function.comp_def]
    rw [scalarFormals_names _ _ encodedInputs]
    exact (((permutation.append_right _).map Binding.name).nodup_iff).mpr
      (List.nodup_append.mp allDistinct).1
  have outputDistinct : (Imperative.Calls.outputOnlyParams (P := Core.Expression)
      target.header).Nodup := by
    apply List.nodup_of_nodup_map (fun id : Core.CoreIdent => id.name)
    rw [coreOutputOnly_keys, List.map_map]
    simp only [Function.comp_def]
    rw [scalarFormals_names _ _ layout.outputOnly]
    exact (List.nodup_append.mp allDistinct).2.1
  apply (initCallFrame_iff_lookup target coreArguments coreOutputs _
    inputLength outputLength inputDistinct outputDistinct).mpr
  dsimp only
  rw [installedCurrentSlots_eq_source layout input outputs arguments globalsMatch
    coreArguments coreOutputs supplied argumentLiterals outputLiterals]
  exact installedSnapshots_eq_source layout input outputs globalsMatch

/-- Build the canonical Core frame from the supplied source values. Argument
lookup uses the checked input order, and the installed store agrees by name
with the source invocation, including its old snapshots. -/
private theorem reified_call_frame {globals : List Binding} {source : ProcedureMeaning}
    {target : Core.Procedure} (layout : ProcedureLayout globals source target)
    (input : Invocation) (outputs : List Value)
    (globalsMatch : valuesMatch globals input.globals = true)
    (inputsMatch : valuesMatch source.inputs input.arguments = true)
    (outputsMatch : valuesMatch source.outputs outputs = true) :
    ∃ arguments coreArguments coreOutputs,
      (coreExplicitInputs globals target).length = input.arguments.length ∧
      coreSuppliedArguments globals target input = some arguments ∧
      (target.header.inputs.toList.zip arguments).all
        (fun ((_, ty), value) => matchesCoreType value ty) = true ∧
      arguments.mapM coreValue? = some coreArguments ∧
      outputs.mapM coreValue? = some coreOutputs ∧
      Core.InitCallFrame target coreArguments coreOutputs
        (coreStore (initialState globals source input outputs)) := by
  obtain ⟨orderedGlobals, permutation, inputEncoding⟩ := layout.inputs
  let supplied := bindValues (globals ++ source.inputs) (input.globals ++ input.arguments)
  have distinct : ((globals ++ source.inputs).map (·.name)).Nodup := by
    have allDistinct := layout.distinct
    rw [List.map_append] at allDistinct
    exact (List.nodup_append.mp allDistinct).1
  have available : ∀ binding ∈ orderedGlobals ++ source.inputs,
      ∃ value, supplied.lookup binding.name = some value ∧ value.sort = binding.sort := by
    intro binding member
    exact lookup_bindValues_of_member binding ((permutation.append_right _).mem_iff.mp member)
      distinct (valuesMatch_append globalsMatch inputsMatch)
  obtain ⟨arguments, read, typed⟩ :=
    readValues_of_typed_lookup (orderedGlobals ++ source.inputs) supplied available
  have explicitNames := scalarFormals_names _ _ layout.explicitInputs
  have explicitLength : (coreExplicitInputs globals target).length = input.arguments.length := by
    have count := congrArg List.length explicitNames
    simp only [List.length_map] at count
    exact count.trans (beq_iff_eq.mp (Bool.and_eq_true_iff.mp inputsMatch).1)
  have orderedArguments : coreSuppliedArguments globals target input = some arguments := by
    rw [coreSuppliedArguments_by_name layout input globalsMatch]
    have order := scalarFormals_names _ _ inputEncoding
    have inputKeys : target.header.inputs.keys = target.header.inputs.toList.map Prod.fst :=
      ListMap.keys_eq_map_fst _
    rw [inputKeys, List.map_map]
    change (target.header.inputs.toList.map (fun pair => pair.1.name)).mapM
      (fun name => supplied.lookup name) = _
    rw [order, List.mapM_map]
    exact read
  obtain ⟨coreArguments, reifiedArgs, _⟩ := reifyValues_of_valuesMatch _ _
    (scalarFormals_are_scalar _ _ inputEncoding) typed
  obtain ⟨coreOutputs, reifiedOuts, _⟩ := reifyValues_of_valuesMatch _ _
    (scalarFormals_are_scalar _ _ layout.outputOnly) outputsMatch
  have coreTyped := (scalarFormals_valuesMatch _ _ _ inputEncoding).mp typed
  exact ⟨arguments, coreArguments, coreOutputs, explicitLength, orderedArguments, coreTyped.2,
    reifiedArgs, reifiedOuts, initCallFrame_agrees_of_layout layout input outputs arguments
      globalsMatch outputsMatch coreArguments coreOutputs orderedArguments reifiedArgs reifiedOuts⟩

/-- Source output choices and Core entry frames describe the same set of
initial stores. The reverse direction uses the uniqueness of Core's frame
for the same inputs and output choices. -/
theorem entry_agrees_of_layout {globals : List Binding} {source : ProcedureMeaning}
    {target : Core.Procedure} (layout : ProcedureLayout globals source target)
    (input : Invocation) (globalsMatch : valuesMatch globals input.globals = true)
    (inputsMatch : valuesMatch source.inputs input.arguments = true) (store : Core.CoreStore) :
    coreEntry globals target input store ↔
      ∃ outputs, valuesMatch source.outputs outputs = true ∧
        store = coreStore (initialState globals source input outputs) := by
  have outputsTyped := fun values =>
    scalarFormals_valuesMatch source.outputs (coreOutputOnly target) values layout.outputOnly
  constructor
  · rintro ⟨arguments, outputs, coreArguments, coreOutputs, _, _, supplied, _,
      outputLength, outputTypes, reifiedArguments, reifiedOutputs, frame⟩
    have outputsMatch := (outputsTyped outputs).mpr ⟨outputLength, outputTypes⟩
    obtain ⟨expected, expectedArguments, expectedOutputs, _, expectedSupply, _,
      expectedArgumentLiterals, expectedOutputLiterals, canonical⟩ :=
      reified_call_frame layout input outputs globalsMatch inputsMatch outputsMatch
    have argumentsEq : arguments = expected := Option.some.inj (supplied.symm.trans expectedSupply)
    subst arguments
    obtain rfl := Option.some.inj (reifiedArguments.symm.trans expectedArgumentLiterals)
    obtain rfl := Option.some.inj (reifiedOutputs.symm.trans expectedOutputLiterals)
    exact ⟨outputs, outputsMatch, Core.InitCallFrameUniqueResult frame canonical⟩
  · rintro ⟨outputs, outputsMatch, rfl⟩
    obtain ⟨arguments, coreArguments, coreOutputs, parameterLength, supplied, argumentTypes,
      reifiedArguments, reifiedOutputs, frame⟩ :=
      reified_call_frame layout input outputs globalsMatch inputsMatch outputsMatch
    obtain ⟨outputLength, outputTypes⟩ := (outputsTyped outputs).mp outputsMatch
    exact ⟨arguments, outputs, coreArguments, coreOutputs, globalsMatch, parameterLength,
      supplied, argumentTypes, outputLength, outputTypes, reifiedArguments, reifiedOutputs, frame⟩

/-- A call with typed arguments, globals, and output choices satisfies the
source interface typing invariant, including its initialized old snapshots. -/
theorem initialState_wellTyped_of_layout {globals : List Binding} {source : ProcedureMeaning}
    {target : Core.Procedure} (layout : ProcedureLayout globals source target)
    (input : Invocation) (outputs : List Value)
    (globalsMatch : valuesMatch globals input.globals = true)
    (inputsMatch : valuesMatch source.inputs input.arguments = true)
    (outputsMatch : valuesMatch source.outputs outputs = true) :
    procedureStateWellTyped globals source (initialState globals source input outputs) := by
  have globalTyped := Bool.and_eq_true_iff.mp globalsMatch
  have inputTyped := Bool.and_eq_true_iff.mp inputsMatch
  have globalLength : globals.length = input.globals.length := beq_iff_eq.mp globalTyped.1
  have inputLength : source.inputs.length = input.arguments.length := beq_iff_eq.mp inputTyped.1
  let globalStore := bindValues globals input.globals
  let snapshots := globalStore.filter (fun (name, _) => source.contract.modifies.contains name)
  change (∃ values, valuesMatch globals values = true ∧ globalStore = bindValues globals values) ∧
    (∃ values, valuesMatch (source.inputs ++ source.outputs) values = true ∧
      bindValues source.inputs input.arguments ++ bindValues source.outputs outputs =
        bindValues (source.inputs ++ source.outputs) values) ∧
    (∀ name value, (name, value) ∈ snapshots →
      name ∈ source.contract.modifies ∧
      ∃ binding ∈ globals, binding.name = name ∧ binding.sort = value.sort) ∧
    (∀ name ∈ source.contract.modifies, (Store.lookup snapshots name).isSome)
  refine ⟨⟨_, globalsMatch, rfl⟩, ⟨input.arguments ++ outputs, ?_, ?_⟩, ?_, ?_⟩
  · exact valuesMatch_append inputsMatch outputsMatch
  · exact (bindValues_append inputLength).symm
  · intro name value member
    obtain ⟨stored, modified⟩ := List.mem_filter.mp member
    refine ⟨List.contains_iff_mem.mp modified, ?_⟩
    obtain ⟨⟨binding, supplied⟩, zipped, equal⟩ := List.mem_map.mp stored
    have sameSort := beq_iff_eq.mp (List.all_eq_true.mp globalTyped.2 _ zipped)
    have sameName : binding.name = name := congrArg Prod.fst equal
    have sameValue : supplied = value := congrArg Prod.snd equal
    exact ⟨binding, (List.of_mem_zip zipped).1, sameName, sameSort.trans (congrArg Value.sort sameValue)⟩
  · intro name modified
    obtain ⟨modifiedGlobals, inGlobals, order, _⟩ := layout.outputs
    obtain ⟨binding, retained, sameName⟩ := List.mem_map.mp (order.mem_iff.mpr modified)
    have keyOrder : globalStore.map Prod.fst = globals.map (·.name) := by
      calc
        _ = ((globals.zip input.globals).map Prod.fst).map (·.name) := by
          simp [globalStore, bindValues, List.map_map, Function.comp_def]
        _ = _ := by rw [List.map_fst_zip (Nat.le_of_eq globalLength)]
    have key : name ∈ globalStore.map Prod.fst := by
      rw [keyOrder]
      exact List.mem_map.mpr ⟨binding, inGlobals binding retained, sameName⟩
    obtain ⟨⟨key, value⟩, stored, sameKey⟩ := List.mem_map.mp key
    change key = name at sameKey
    subst key
    apply List.findSome?_isSome_iff.mpr
    refine ⟨(name, value), List.mem_filter.mpr ⟨stored, List.contains_iff_mem.mpr modified⟩, ?_⟩
    simp


/-- A value found in a typed procedure frame comes from a declared binding
with that name and type. -/
private theorem lookup_bindValues_binding {bindings : List Binding} {values : List Value}
    {name : String} {value : Value} (typed : valuesMatch bindings values = true)
    (found : (bindValues bindings values).lookup name = some value) :
    ∃ binding ∈ bindings, binding.name = name ∧ binding.sort = value.sort := by
  obtain ⟨⟨slot, stored⟩, present, lookedUp⟩ := List.exists_of_findSome?_eq_some found
  change (if slot == name then some stored else none) = some value at lookedUp
  split at lookedUp
  · rename_i sameName
    obtain rfl := Option.some.inj lookedUp
    obtain ⟨⟨binding, slotValue⟩, zipped, same⟩ := List.mem_map.mp present
    have equal : binding.name = slot ∧ slotValue = stored := Prod.mk.injEq _ _ _ _ |>.mp same
    refine ⟨binding, (List.of_mem_zip zipped).1, equal.1.trans (beq_iff_eq.mp sameName), ?_⟩
    have types := (Bool.and_eq_true_iff.mp typed).2
    have sort := List.all_eq_true.mp types (binding, slotValue) zipped
    exact (beq_iff_eq.mp sort).trans (congrArg Value.sort equal.2)
  · contradiction

private theorem slotType_eq_some {store : Store} {name : String} {sort : ValueType}
    (found : (store.lookup name).map Value.sort = some sort) :
    ∃ value, store.lookup name = some value ∧ value.sort = sort := by
  cases lookup : store.lookup name with
  | none => simp [lookup] at found
  | some value => exact ⟨value, rfl, by simpa [lookup] using found⟩

/-- All visible slots at return are scalar. The body cannot introduce a local
slot that hides a global at the procedure interface. -/
theorem body_return_slots_of_layout {globals : List Binding} {source : ProcedureMeaning}
    {target : Core.Procedure} {command : BooleDDM.Command SourceRange}
    (interpreted : ProcedureWasInterpreted (denotation .builtins) command source)
    (layout : ProcedureLayout globals source target)
    (initial : State)
    (typed : procedureStateWellTyped globals source initial) :
    ∀ final, source.body.run initial (.returned () final) →
      (∀ name value, final.globals.lookup name = some value →
        final.locals.lookup name = none ∧ value.sort.hasCoreLiteral = true) ∧
      (∀ name value, final.locals.lookup name = some value → value.sort.hasCoreLiteral = true) := by
  intro final ran
  obtain ⟨globalSlots, localSlots⟩ :=
    interpretedProcedure_return_slotTypes interpreted initial final ran
  obtain ⟨⟨globalValues, globalsTyped, globalsBound⟩, ⟨locals, localsTyped, localsBound⟩, _⟩ := typed
  obtain ⟨ordered, permuted, encoded⟩ := layout.inputs
  have globalScalar : ∀ binding ∈ globals, binding.sort.hasCoreLiteral = true :=
    fun binding present => scalarFormals_are_scalar _ _ encoded binding
      (List.mem_append_left _ (permuted.mem_iff.mpr present))
  have localScalar : ∀ binding ∈ source.inputs ++ source.outputs,
      binding.sort.hasCoreLiteral = true := by
    intro binding present
    rcases List.mem_append.mp present with input | output
    · exact scalarFormals_are_scalar _ _ layout.explicitInputs binding input
    · exact scalarFormals_are_scalar _ _ layout.outputOnly binding output
  have distinct := layout.distinct
  simp only [List.map_append, List.append_assoc] at distinct
  have disjoint := (List.nodup_append.mp distinct).2.2
  constructor
  · intro name value lookup
    have before := (globalSlots name).symm
    rw [lookup] at before
    obtain ⟨previous, previousLookup, sameType⟩ := slotType_eq_some before
    rw [globalsBound] at previousLookup
    obtain ⟨binding, member, named, sort⟩ := lookup_bindValues_binding globalsTyped previousLookup
    have isGlobal : name ∈ globals.map (·.name) := List.mem_map.mpr ⟨binding, member, named⟩
    have absent : name ∉ (source.inputs ++ source.outputs).map (·.name) := by
      rw [List.map_append]
      exact fun present => disjoint name isGlobal name present rfl
    have beforeAbsent : initial.locals.lookup name = none :=
      localsBound ▸ lookup_bindValues_none _ _ _ absent
    have afterAbsent := localSlots name
    rw [beforeAbsent] at afterAbsent
    refine ⟨?_, (sort.trans sameType) ▸ globalScalar binding member⟩
    cases found : final.locals.lookup name with
    | none => rfl
    | some localValue => simp [found] at afterAbsent
  · intro name value lookup
    have before := (localSlots name).symm
    rw [lookup] at before
    obtain ⟨previous, previousLookup, sameType⟩ := slotType_eq_some before
    rw [localsBound] at previousLookup
    obtain ⟨binding, member, _, sort⟩ := lookup_bindValues_binding localsTyped previousLookup
    exact (sort.trans sameType) ▸ localScalar binding member

end Strata.Boole
