/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.Languages.Core.Typing.Spec.TypingSpec
import all Strata.DL.Imperative.Stmt
import all Strata.DL.Imperative.CmdCallFormals
import all Strata.Languages.Core.Typing.Spec.TypeSpecShared
import Strata.Util.ListMapProps
import all Strata.Util.ListMap
import all Strata.Util.HMaps

namespace Strata.Boole.Hoare

open Lambda Imperative Strata.Util

private theorem typed_cmd_preserves_slot
    {P : Core.Program} {C : LContext Core.CoreLParams} {ts ts' : Core.TypeSpec.TypeScopes}
    {cmd : Core.Command} (typed : Core.TypeSpec.CmdExtWellTyped C P ts cmd ts')
    {name : Core.CoreIdent} {ty : LTy} (lookup : ts.find? name = some ty) :
    ts'.find? name = some ty ∧ name ∉ Imperative.CmdExt.definedVars cmd := by
  cases typed
  case cmd =>
    rename_i primitive
    cases primitive
    case init_det =>
      rename_i declared annotation rhs mono md fresh free type kind checked replaced
      have other : declared ≠ name := by
        rintro rfl
        rw [fresh] at lookup
        contradiction
      refine ⟨(replaced.find? name).trans ?_, by simpa [CmdExt.definedVars, Cmd.definedVars] using other.symm⟩
      rw [HMaps.find?_insert_ne]
      · exact lookup
      · exact other.symm
    case init_nondet =>
      rename_i declared annotation mono md fresh type kind replaced
      have other : declared ≠ name := by
        rintro rfl
        rw [fresh] at lookup
        contradiction
      refine ⟨(replaced.find? name).trans ?_, by simpa [CmdExt.definedVars, Cmd.definedVars] using other.symm⟩
      rw [HMaps.find?_insert_ne]
      · exact lookup
      · exact other.symm
    all_goals
      rename_i equivalent
      exact ⟨(equivalent.find? name).trans lookup, by simp [CmdExt.definedVars, Cmd.definedVars]⟩
  case call =>
    rename_i equivalent
    exact ⟨(equivalent.find? name).trans lookup, by simp [CmdExt.definedVars]⟩

private theorem typed_stmt_preserves_slot
    {P : Core.Program} {C C' : LContext Core.CoreLParams} {ts ts' : Core.TypeSpec.TypeScopes}
    {labels : List String} {stmt : Core.Statement}
    (typed : Core.TypeSpec.StatementWellTyped P C ts labels stmt C' ts')
    {name : Core.CoreIdent} {ty : LTy} (lookup : ts.find? name = some ty) :
    ts'.find? name = some ty ∧ name ∉ Imperative.Stmt.definedVars stmt true := by
  cases typed
  case cmd =>
    rename_i primitive
    exact typed_cmd_preserves_slot primitive lookup
  all_goals
    rename_i equivalent
    exact ⟨(equivalent.find? name).trans lookup, by simp [Imperative.Stmt.definedVars]⟩

private theorem typed_stmts_keep_slot
    {P : Core.Program} {C C' : LContext Core.CoreLParams} {ts ts' : Core.TypeSpec.TypeScopes}
    {labels : List String} {stmts : Core.Statements}
    (typed : Core.TypeSpec.StatementsWellTyped P C ts labels stmts C' ts')
    {name : Core.CoreIdent} {ty : LTy} (lookup : ts.find? name = some ty) :
    name ∉ Imperative.Block.definedVars stmts true := by
  induction stmts generalizing C ts with
  | nil => simp [Imperative.Block.definedVars]
  | cons first rest ih =>
    cases typed
    case cons =>
      rename_i head tail
      obtain ⟨preserved, noDeclaration⟩ := typed_stmt_preserves_slot head lookup
      simpa [Imperative.Block.definedVars] using And.intro noDeclaration (ih tail preserved)

private theorem procBodyScopes_lookup
    (scope : Core.TypeSpec.TypeScopes) (proc : Core.Procedure) (name : Core.CoreIdent)
    (present : name ∈ proc.header.inputs.keys ++ proc.header.outputs.keys ++
      (proc.header.getInoutParams.keys.map fun id => Core.CoreIdent.mkOld id.name)) :
    ∃ ty, (Core.TypeSpec.procBodyScopes scope proc).find? name = some ty := by
  let old := proc.header.getInoutParams.toList.map fun (id, ty) =>
    (Core.CoreIdent.mkOld id.name, ty)
  let formals := old ++ proc.header.outputs.toList ++ proc.header.inputs.toList
  let bindings := formals.map fun (id, ty) => (id, LTy.forAll [] ty)
  have inBindings : name ∈ bindings.map Prod.fst := by
    have keys (formals : ListMap Core.CoreIdent LMonoTy) :
        formals.keys = formals.toList.map Prod.fst := ListMap.keys_eq_map_fst _
    simp only [keys, List.mem_append] at present
    simp only [bindings, formals, old, List.map_map, List.map_append, Function.comp_def,
      List.mem_append]
    rcases present with (input | output) | snapshot
    · exact Or.inr input
    · exact Or.inl (Or.inr output)
    · exact Or.inl (Or.inl (by simpa only [List.map_map, Function.comp_def] using snapshot))
  obtain ⟨ty, lookup⟩ := HMap.find?_ofList_of_mem_keys bindings name inBindings
  refine ⟨ty, ?_⟩
  simp only [Core.TypeSpec.procBodyScopes, HMaps.push]
  change (HMaps.find? (HMap.ofList bindings :: scope) name) = some ty
  simp [HMaps.find?, lookup]

end Strata.Boole.Hoare
