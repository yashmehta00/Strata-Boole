/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.Lowering
import all StrataBoole.Boole.Semantics.Adequacy.Lowering
import all StrataBoole.Boole.Interp
import all StrataBoole.Boole.Semantics.Semantics
import Strata.Languages.Core.Identifiers
import Strata.Util.ListUtilsProps

/-! # Source procedure interfaces -/

public section
namespace Strata.Boole
open StrataDDM

/-- A successful state computation can be inverted at its first bind. -/
private theorem split_run {action : StateT σ (Except ε) α} {next : α → StateT σ (Except ε) β}
    {initial final : σ} {result : β}
    (success : (action >>= next) initial = .ok (result, final)) :
    ∃ value middle, action initial = .ok (value, middle) ∧ next value middle = .ok (result, final) := by
  cases ran : action initial with
  | error error => simp [bind, StateT.bind, Except.bind, ran] at success
  | ok output => exact ⟨output.1, output.2, by cases output; rfl,
      by simpa [bind, StateT.bind, Except.bind, ran] using success⟩

private def ReadOnly (action : InterpM α) : Prop :=
  ∀ initial value final, action initial = .ok (value, final) → final = initial

private theorem readOnly_pure (value : α) : ReadOnly (pure value) :=
  fun _ _ _ success => (congrArg Prod.snd (Except.ok.inj success)).symm

private theorem readOnly_get : ReadOnly (get : InterpM Scope) :=
  fun _ _ _ success => (congrArg Prod.snd (Except.ok.inj success)).symm

private theorem readOnly_reject (range : SourceRange) (message : String) :
    ReadOnly (reject range message : InterpM α) := fun _ _ _ success => by contradiction

private theorem ReadOnly.bind {action : InterpM α} {next : α → InterpM β}
    (first : ReadOnly action) (rest : ∀ value, ReadOnly (next value)) :
    ReadOnly (action >>= next) := by
  intro initial result final success
  obtain ⟨value, middle, a, b⟩ := split_run success
  exact (rest _ _ _ _ b).trans (first _ _ _ a)

private theorem ReadOnly.map {action : InterpM α} (f : α → β) (kept : ReadOnly action) :
    ReadOnly (f <$> action) := by
  rw [← bind_pure_comp]
  exact kept.bind (fun x => readOnly_pure (f x))

private theorem readOnly_mapM (items : List α) (action : α → InterpM β)
    (kept : ∀ item ∈ items, ReadOnly (action item)) : ReadOnly (items.mapM action) := by
  induction items with
  | nil => exact readOnly_pure []
  | cons item items ih =>
    rw [List.mapM_cons]
    exact (kept _ (by simp)).bind (fun value =>
      (ih (fun x present => kept _ (List.mem_cons_of_mem _ present))).map (List.cons value))

/-- Resolving a type reads the lexical scope and leaves it unchanged. -/
private theorem sourceSort_readOnly (ty : Boole.Type) : ReadOnly (sourceSort ty) := by
  have finish (sort : ValueType) : ReadOnly (do
      let scope ← get
      if !scope.supportsType sort then
        reject default s!"Type has no interpretation in this model: {repr sort}"
      pure sort : InterpM ValueType) := by
    apply ReadOnly.bind readOnly_get
    intro scope
    split
    · exact (readOnly_reject _ _).bind (fun _ => readOnly_pure _)
    · exact readOnly_pure _
  cases ty
  case' bv range width => cases width
  all_goals rw [sourceSort.eq_def]
  all_goals try dsimp only
  all_goals try exact (readOnly_pure _).bind finish
  all_goals try exact (readOnly_reject _ _).bind finish
  case fvar range index arguments =>
    apply ReadOnly.bind readOnly_get
    intro scope
    cases scope.names.nameOf? index with
    | none =>
      exact (readOnly_reject _ _).bind finish
    | some name =>
      have argumentsRead : ReadOnly (arguments.toList.reverse.mapM sourceSort) := by
        apply readOnly_mapM
        intro item present
        exact sourceSort_readOnly item
      apply ReadOnly.bind argumentsRead
      intro sorts
      by_cases isSet : (name == "Set") = true
      · simp only [isSet, ite_true]
        cases sorts with
        | nil => exact (readOnly_reject _ _).bind finish
        | cons first rest =>
          cases rest
          · exact (readOnly_pure _).bind finish
          · exact (readOnly_reject _ _).bind finish
      · simp only [isSet]
        exact (readOnly_reject _ _).bind finish
  all_goals first
    | (apply ReadOnly.bind _ finish
       rw [seq_eq_bind_map]
       exact (ReadOnly.map _ (sourceSort_readOnly _)).bind
         (fun f => ReadOnly.map f (sourceSort_readOnly _)))
    | exact (ReadOnly.map _ (sourceSort_readOnly _)).bind finish

termination_by sizeOf ty
decreasing_by
  all_goals first
    | (simp_all; omega)
    | (have smaller := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp (List.mem_reverse.mp present))
       simp_all; omega)

private def ValidNames (bindings : List Binding) : Prop :=
  (bindings.map Binding.name).Nodup ∧ ∀ binding ∈ bindings, binding.name.contains ' ' = false

/-- A successful freshness check excludes both collisions and reserved spaces. -/
private theorem fresh_names {range : SourceRange} {binding : Binding} {initial final : Scope}
    (success : fresh range binding initial = .ok ((), final)) :
    binding.name.contains ' ' = false ∧
      binding.name ∉ (initial.locals ++ initial.globals).map Binding.name ∧ final = initial := by
  have readScope : (get : InterpM Scope) initial = .ok (initial, initial) := rfl
  simp only [fresh, bind, StateT.bind, Except.bind, readScope] at success
  split at success
  · contradiction
  · rename_i valid
    split at success
    · contradiction
    · rename_i unused
      have noSpaces : binding.name.contains ' ' = false := by
        cases spaces : binding.name.contains ' ' <;> simp_all
      refine ⟨noSpaces, ?_, (congrArg Prod.snd (Except.ok.inj success)).symm⟩
      intro present
      obtain ⟨other, available, same⟩ := List.mem_map.mp present
      have any : (initial.locals ++ initial.globals).any (fun b => b.name == binding.name) = true :=
        List.any_eq_true.mpr ⟨other, available, beq_iff_eq.mpr same⟩
      exact unused (by simpa [findBinding, List.isSome_find?] using any)

private theorem ValidNames.appendFresh {bindings : List Binding} {binding : Binding}
    (valid : ValidNames bindings) (unused : binding.name ∉ bindings.map Binding.name)
    (noSpaces : binding.name.contains ' ' = false) : ValidNames (bindings ++ [binding]) := by
  refine ⟨?_, ?_⟩
  · rw [List.map_append, List.map_singleton]
    exact List.nodup_append.mpr ⟨valid.1, by simp, fun name present _ equal eq => by
      have same : _ = binding.name := List.mem_singleton.mp equal
      exact unused ((eq.trans same) ▸ present)⟩
  · intro other present
    rcases List.mem_append.mp present with existing | added
    · exact valid.2 _ existing
    · obtain rfl := List.mem_singleton.mp added
      exact noSpaces

private theorem addLocal_names {range : SourceRange} {name : String} {ty : Boole.Type}
    {initial final : Scope} {binding : Binding}
    (valid : ValidNames (initial.globals ++ initial.locals))
    (success : addLocal range name ty initial = .ok (binding, final)) :
    binding.name = name ∧ final = { initial with locals := initial.locals ++ [binding] } ∧
      ValidNames (final.globals ++ final.locals) := by
  unfold addLocal at success
  obtain ⟨sort, middle, resolved, added⟩ := split_run success
  have same : middle = initial := sourceSort_readOnly ty _ _ _ resolved
  subst middle
  obtain ⟨trivialValue, afterFresh, checked, installed⟩ := split_run added
  cases trivialValue
  obtain ⟨noSpaces, fresh, restored⟩ := fresh_names checked
  subst afterFresh
  have equal := Except.ok.inj installed
  have bindingEq : (⟨name, sort⟩ : Binding) = binding := congrArg Prod.fst equal
  have scopeEq : { initial with locals := initial.locals ++ [⟨name, sort⟩] } = final :=
    congrArg Prod.snd equal
  subst binding
  subst final
  have unused : name ∉ (initial.globals ++ initial.locals).map Binding.name := by
    simpa [List.map_append, List.mem_append, or_comm] using fresh
  refine ⟨rfl, rfl, ?_⟩
  simpa only [List.append_assoc] using valid.appendFresh unused noSpaces

/-- A successful binding list extends the local scope by exactly its returned
bindings and preserves the distinct, space-free names of the interface. -/
private def AddsLocals (action : InterpM (List Binding)) : Prop :=
  ∀ initial bindings final, ValidNames (initial.globals ++ initial.locals) →
    action initial = .ok (bindings, final) →
    final.globals = initial.globals ∧ final.locals = initial.locals ++ bindings ∧
      ValidNames (final.globals ++ final.locals)

private theorem addsLocals_none : AddsLocals (pure []) := by
  intro initial bindings final valid success
  have same : ([], initial) = (bindings, final) := Except.ok.inj success
  cases same
  exact ⟨rfl, by simp, valid⟩

private theorem inputBindings_names (parameters : BooleDDM.Bindings SourceRange) :
    AddsLocals (inputBindings parameters) := by
  cases parameters with
  | mkBindings _ parameters =>
    change AddsLocals (parameters.val.toList.mapM fun
      | .mkBinding range name (.expr ty) => addLocal range name.val ty
      | parameter => reject default s!"Unsupported parameter: {repr parameter}")
    generalize parameters.val.toList = items
    induction items with
    | nil => exact addsLocals_none
    | cons parameter rest ih =>
      intro initial bindings final valid success
      rw [List.mapM_cons] at success
      obtain ⟨binding, middle, checked, tail⟩ := split_run success
      have ⟨preserved, appended, distinct⟩ :
          middle.globals = initial.globals ∧ middle.locals = initial.locals ++ [binding] ∧
            ValidNames (middle.globals ++ middle.locals) := by
        cases parameter
        case' mkBinding range name type => cases type
        all_goals try contradiction
        obtain ⟨_, rfl, names⟩ := addLocal_names valid checked
        exact ⟨rfl, rfl, names⟩
      obtain ⟨remaining, last, ran, ended⟩ := split_run tail
      have same : (binding :: remaining, last) = (bindings, final) := Except.ok.inj ended
      cases same
      obtain ⟨globals, locals, distinct⟩ := ih _ _ _ distinct ran
      exact ⟨globals.trans preserved, by simp [locals, appended, List.append_assoc], distinct⟩

private theorem outputBindings_names (outputs : BooleDDM.MonoDeclList SourceRange) :
    AddsLocals (outputBindings outputs) := by
  induction outputs with
  | monoDeclAtom range binding =>
    cases binding
    intro initial bindings final valid success
    rw [outputBindings] at success
    obtain ⟨binding, middle, checked, ended⟩ := split_run success
    have same : ([binding], middle) = (bindings, final) := Except.ok.inj ended
    cases same
    obtain ⟨_, rfl, names⟩ := addLocal_names valid checked
    exact ⟨rfl, rfl, names⟩
  | monoDeclPush range rest binding ih =>
    cases binding
    intro initial bindings final valid success
    rw [outputBindings] at success
    obtain ⟨previous, middle, prior, added⟩ := split_run success
    obtain ⟨binding, last, checked, ended⟩ := split_run added
    have same : (previous ++ [binding], last) = (bindings, final) := Except.ok.inj ended
    cases same
    obtain ⟨globals, locals, distinct⟩ := ih _ _ _ valid prior
    obtain ⟨_, rfl, names⟩ := addLocal_names distinct checked
    exact ⟨globals, by simp [locals, List.append_assoc], names⟩

private theorem withScope_restores {action : InterpM α} {initial final : Scope} {value : α}
    (success : withScope action initial = .ok (value, final)) : final = initial := by
  simp only [withScope, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
    get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set] at success
  split at success
  · contradiction
  · exact (congrArg Prod.snd (Except.ok.inj success)).symm

private theorem interpProc_names {I : Interpretation} {range : SourceRange} {name : String}
    {types : Option (BooleDDM.TypeArgs SourceRange)} {parameters : BooleDDM.Bindings SourceRange}
    {outputs : Option (BooleDDM.MonoDeclList SourceRange)} {spec : Option (BooleDDM.Spec SourceRange)}
    {body : Option (BooleDDM.Block SourceRange)} {initial final : Scope}
    {procedure : InterpProcedure I.Expression I.Statement}
    (valid : ValidNames (initial.globals ++ initial.locals))
    (success : interpProc I range name types parameters outputs spec body initial =
      .ok (procedure, final)) :
    final = initial ∧ ValidNames (initial.globals ++ initial.locals ++ procedure.inputs ++ procedure.outputs) := by
  unfold interpProc at success
  refine ⟨withScope_restores success, ?_⟩
  obtain ⟨_, ran⟩ := withScope_success success
  cases types with
  | some => contradiction
  | none =>
    simp only [Option.isSome, Bool.false_eq_true, ite_false] at ran
    obtain ⟨ins, afterInputs, readInputs, ran⟩ := split_run ran
    cases outputs
    all_goals
      obtain ⟨outs, afterOutputs, readOutputs, ran⟩ := split_run ran
      obtain ⟨inputGlobals, inputLocals, validInputs⟩ :=
        inputBindings_names parameters _ _ _ valid readInputs
      have outputFacts : afterOutputs.globals = afterInputs.globals ∧
          afterOutputs.locals = afterInputs.locals ++ outs ∧
          ValidNames (afterOutputs.globals ++ afterOutputs.locals) := by
        first
        | exact addsLocals_none _ _ _ validInputs readOutputs
        | exact outputBindings_names _ _ _ _ validInputs readOutputs
      obtain ⟨outputGlobals, outputLocals, validOutputs⟩ := outputFacts
      rw [outputGlobals, inputGlobals, outputLocals, inputLocals] at validOutputs
      cases body
      all_goals
        repeat' first
          | contradiction
          | simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
              modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
              reject, throw, throwThe, MonadExceptOf.throw] at ran
          | (have inputs : ins = procedure.inputs :=
               congrArg (fun pair => pair.1.inputs) (Except.ok.inj ran)
             have outputs : outs = procedure.outputs :=
               congrArg (fun pair => pair.1.outputs) (Except.ok.inj ran)
             simpa only [← inputs, ← outputs, List.append_assoc] using validOutputs)
          | split at ran

private theorem forIn_invariant {σ ε α β : Type} (items : List α)
    (step : α → β → StateT σ (Except ε) (ForInStep β)) (invariant : σ → β → Prop)
    (preserved : ∀ item before initial control final,
      invariant initial before → step item before initial = .ok (control, final) →
      invariant final control.value)
    (before after : β) (initial final : σ)
    (valid : invariant initial before)
    (success : (forIn items before step) initial = .ok (after, final)) :
    invariant final after := by
  induction items generalizing before initial with
  | nil =>
    have same : (before, initial) = (after, final) := Except.ok.inj success
    cases same
    exact valid
  | cons item rest ih =>
    simp only [List.forIn_cons, bind, StateT.bind, Except.bind, pure] at success
    cases ran : step item before initial with
    | error => simp [ran] at success
    | ok result =>
      obtain ⟨control, next⟩ := result
      have validNext := preserved item before initial control next valid ran
      cases control with
      | yield current => exact ih current next validNext (by simpa [ran] using success)
      | done current =>
        have same : (current, next) = (after, final) := by
          exact Except.ok.inj (ε := ε) (by simpa [ran, StateT.pure, pure, Except.pure] using success)
        cases same
        exact validNext

private def ValidInterfaces (I : Interpretation) (scope : Scope)
    (procedures : List (InterpProcedure I.Expression I.Statement)) : Prop :=
  scope.locals = [] ∧ ValidNames scope.globals ∧
    ∀ procedure ∈ procedures, ValidNames (scope.globals ++ procedure.inputs ++ procedure.outputs)

private theorem ValidInterfaces.append {I : Interpretation} {scope : Scope}
    {previous : List (InterpProcedure I.Expression I.Statement)}
    {procedure : InterpProcedure I.Expression I.Statement}
    (kept : ValidInterfaces I scope previous)
    (valid : ValidNames (scope.globals ++ procedure.inputs ++ procedure.outputs)) :
    ValidInterfaces I scope (previous ++ [procedure]) := by
  refine ⟨kept.1, kept.2.1, ?_⟩
  intro candidate present
  rcases List.mem_append.mp present with old | new
  · exact kept.2.2 _ old
  · obtain rfl := List.mem_singleton.mp new
    exact valid

private theorem ValidInterfaces.addGlobal {I : Interpretation} {scope : Scope}
    {previous : List (InterpProcedure I.Expression I.Statement)} {binding : Binding}
    (kept : ValidInterfaces I scope previous) (noProcedures : previous = [])
    (noSpaces : binding.name.contains ' ' = false)
    (unused : binding.name ∉ (scope.locals ++ scope.globals).map Binding.name) :
    ValidInterfaces I { scope with globals := scope.globals ++ [binding] } previous := by
  subst previous
  refine ⟨kept.1, kept.2.1.appendFresh ?_ noSpaces, by simp⟩
  simpa only [kept.1, List.nil_append] using unused

set_option linter.unusedSimpArgs false in
private theorem interpProgram_names (I : Interpretation) (program : Boole.Program)
    (names : GlobalContext) (meaning : InterpProgram I.Expression I.Statement)
    (success : interpProgram I program names = .ok meaning) :
    ∀ procedure ∈ meaning.procedures,
      ValidNames (meaning.globals ++ procedure.inputs ++ procedure.outputs) := by
  cases program with
  | prog range commands =>
    simp only [interpProgram, StateT.run', Functor.map, Except.map, bind, StateT.bind, Except.bind,
      get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure] at success
    split at success
    · contradiction
    · rename_i result executed
      split at executed
      · contradiction
      · rename_i stepResult loopRan
        have same : (⟨stepResult.2.globals, stepResult.1⟩ : InterpProgram I.Expression I.Statement) = meaning :=
          (congrArg Prod.fst (Except.ok.inj executed)).trans (Except.ok.inj success)
        rw [← same]
        rw [← (Array.toArray_toList (xs := commands.val)), List.forIn_toArray] at loopRan
        have initial : ValidInterfaces I { names := names, supportsType := I.supportsType } [] :=
          ⟨rfl, ⟨by simp, by simp⟩, by simp⟩
        have valid := forIn_invariant _ _ (ValidInterfaces I) ?_ _ _ _ _ initial loopRan
        · exact valid.2.2
        · intro command previous scope control next kept step
          cases command
          case' command_var range binding => cases binding
          all_goals
            repeat' first
              | contradiction
              | simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, reject,
                  throw, throwThe, MonadExceptOf.throw, StateT.lift, Functor.map, Except.map,
                  modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at step
              | (have pair := Except.ok.inj step
                 have eq : _ = control.value := congrArg (fun p => p.1.value) pair
                 have stateEq : _ = next := congrArg Prod.snd pair
                 rw [← eq, ← stateEq]
                 exact kept)
              | split at step
          all_goals
            first
            | (rename_i called
               have inputNames : ValidNames (scope.globals ++ scope.locals) := by simpa [kept.1] using kept.2.1
               obtain ⟨restored, names⟩ := interpProc_names inputNames called
               have eq : _ = control.value := congrArg (fun p => p.1.value) (Except.ok.inj step)
               have stateEq : _ = next := congrArg Prod.snd (Except.ok.inj step)
               rw [← eq, ← stateEq, restored]
               exact kept.append (by simpa only [kept.1, List.append_nil] using names))
            | (rename_i retained noPrevious _ typeResult typed _ freshResult checked
               obtain ⟨sort, middle⟩ := typeResult
               obtain ⟨u, afterFresh⟩ := freshResult
               cases u
               have beforeFresh : middle = scope := sourceSort_readOnly _ _ _ _ typed
               subst middle
               obtain ⟨noSpaces, unused, restored⟩ := fresh_names checked
               subst afterFresh
               have eq : _ = control.value := congrArg (fun p => p.1.value) (Except.ok.inj step)
               have stateEq : _ = next := congrArg Prod.snd (Except.ok.inj step)
               rw [← eq, ← stateEq]
               exact kept.addGlobal (by cases previous <;> simp_all) noSpaces unused)

/-- A successful program interpretation gives each procedure distinct
interface names and excludes the reserved old-snapshot namespace. -/
theorem interpreted_procedure_interface_names
    (I : Interpretation) (program : Boole.Program) (names : GlobalContext)
    (meaning : InterpProgram I.Expression I.Statement)
    (success : interpProgram I program names = .ok meaning)
    (procedure : InterpProcedure I.Expression I.Statement)
    (member : procedure ∈ meaning.procedures) :
    ((meaning.globals ++ procedure.inputs ++ procedure.outputs).map Binding.name).Nodup ∧
      ∀ name, (Core.CoreIdent.mkOld name).name ∉
        (meaning.globals ++ procedure.inputs ++ procedure.outputs).map Binding.name := by
  have ⟨distinct, noSpaces⟩ := interpProgram_names I program names meaning success procedure member
  refine ⟨distinct, ?_⟩
  intro name present
  obtain ⟨binding, included, oldName⟩ := List.mem_map.mp present
  have absent := noSpaces binding included
  rw [oldName] at absent
  have contains : (Core.CoreIdent.mkOld name).name.contains ' ' = true := by
    simp [Core.CoreIdent.mkOld, Core.CoreIdent.oldStr, String.contains_char_eq]
  rw [contains] at absent
  contradiction

/-- Source interpretation makes the interface names distinct and reserves the
space-containing identifier namespace used by Core for old snapshots. -/
theorem MatchedProcedure.source_interface_names (matched : MatchedProcedure) :
    let bindings := matched.meaning.globals ++ matched.source.inputs ++ matched.source.outputs
    (bindings.map Binding.name).Nodup ∧
      ∀ name, (Core.CoreIdent.mkOld name).name ∉ bindings.map Binding.name := by
  dsimp only
  exact interpreted_procedure_interface_names _ _ _ _ matched.denoted _ matched.member

end Strata.Boole
