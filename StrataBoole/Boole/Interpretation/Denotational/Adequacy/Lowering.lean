/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Denotational.CoreReference
import all StrataBoole.Boole.Interpretation.Denotational.CoreReference

import all StrataBoole.Boole.Interpretation.Legacy.Semantics
import all Init.Util
import all StrataDDM.AST
import all Strata.Languages.Core.ProcedureType
public import Strata.Languages.Core.StatementType
import all Strata.Languages.Core.StatementType
import all Strata.Languages.Core.ProgramType
import all Strata.Languages.Core.ProgramWF
import all Strata.Languages.Core.Program
import all Strata.Languages.Core.Verifier
import all Strata.Transform.GenOpaqueTypeParams
import all StrataBoole.Boole.Interpretation.Legacy.Interp
import all StrataBoole.Boole.Interpretation.Source
import all StrataBoole.Verify
import Std.Data.HashMap.Lemmas
import all Strata.Util.ListMap
import Strata.Util.ListMapProps

public section

/-! ## Procedure lookup through Core checking -/

namespace Strata.Boole

/-- Type checking a procedure resolves types and expressions; it keeps its name. -/
private theorem checkedProcedure_name (context : Core.Expression.TyContext)
    (environment final : Core.Expression.TyEnv) (program : Core.Program)
    (procedure checked : Core.Procedure) (metadata : Imperative.MetaData Core.Expression)
    (success : Core.Procedure.typeCheck context environment program procedure metadata =
      .ok (checked, final)) : checked.header.name = procedure.header.name := by
  unfold Core.Procedure.typeCheck at success
  simp only [bind, Except.bind] at success
  repeat' first
    | contradiction
    | (injection success with h; cases h; rfl)
    | split at success

private def procName? : Core.Decl → Option String
  | .proc procedure _ => some procedure.header.name.name
  | _ => none

/-- The checked procedure was obtained by running the actual Core procedure
checker on this raw declaration in the enclosing program. -/
def ProcedureWasChecked (program : Core.Program) (raw checked : Core.Procedure) : Prop :=
  ∃ (context : Core.Expression.TyContext) (environment final : Core.Expression.TyEnv)
    (metadata : Imperative.MetaData Core.Expression),
    Core.Procedure.typeCheck context environment program raw metadata = .ok (checked, final)

/-- A successful checker run certifies that the raw output formals have
distinct names, including the prefix generated from modified globals. -/
private theorem checkedProcedure_rawOutputsNodup {program : Core.Program} {raw checked : Core.Procedure}
    (passed : ProcedureWasChecked program raw checked) : raw.header.outputs.keys.Nodup := by
  obtain ⟨context, environment, final, metadata, success⟩ := passed
  unfold Core.Procedure.typeCheck Core.Procedure.checkParamNames at success
  by_cases inputs : raw.header.inputs.keys.Nodup <;>
    by_cases outputs : raw.header.outputs.keys.Nodup <;>
    first
    | exact outputs
    | simp [inputs, outputs, bind, Except.bind] at success

private inductive CheckedProcedures (program : Core.Program) :
    List Core.Procedure → List Core.Procedure → Prop
  | nil : CheckedProcedures program [] []
  | cons : ProcedureWasChecked program raw checked →
      CheckedProcedures program raws checkeds →
      CheckedProcedures program (raw :: raws) (checked :: checkeds)

private def procDecls (decls : List Core.Decl) : List Core.Procedure :=
  decls.filterMap Core.Decl.getProc?

private theorem checkedProcedures_prepend_nonproc {program : Core.Program}
    {before after : Core.Decl} {remaining acc checked : List Core.Decl}
    (related : ∃ rest, checked = (after :: acc).reverse ++ rest ∧
      CheckedProcedures program (procDecls remaining) (procDecls rest))
    (beforeNotProc : before.getProc? = none) (afterNotProc : after.getProc? = none) :
    ∃ rest, checked = acc.reverse ++ rest ∧
      CheckedProcedures program (procDecls (before :: remaining)) (procDecls rest) := by
  obtain ⟨rest, appended, procedures⟩ := related
  refine ⟨after :: rest, ?_, ?_⟩
  · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using appended
  · simpa only [procDecls, List.filterMap_cons, beforeNotProc, afterNotProc] using procedures

private theorem typeCheckDecls_procedures (program : Core.Program)
    (context : Core.Expression.TyContext) (environment final : Core.Expression.TyEnv)
    (remaining acc checked : List Core.Decl)
    (success : Core.Program.typeCheck.go program context environment remaining acc = .ok (checked, final)) :
    ∃ rest, checked = acc.reverse ++ rest ∧
      CheckedProcedures program (procDecls remaining) (procDecls rest) := by
  induction remaining generalizing context environment acc checked final with
  | nil =>
    simp only [Core.Program.typeCheck.go] at success
    obtain rfl := congrArg Prod.fst (Except.ok.inj success)
    exact ⟨[], (List.append_nil _).symm, .nil⟩
  | cons decl remaining ih =>
    cases decl <;>
      simp only [Core.Program.typeCheck.go, bind, Except.bind, tryCatch, tryCatchThe,
        MonadExceptOf.tryCatch, Except.tryCatch] at success
    case proc procedure metadata =>
      split at success
      · contradiction
      · split at success
        · contradiction
        · rename_i result step
          obtain ⟨rest, appended, related⟩ := ih _ _ _ _ _ success
          refine ⟨.proc result.1 metadata :: rest, ?_, ?_⟩
          · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using appended
          · change CheckedProcedures program (procedure :: procDecls remaining)
              (result.1 :: procDecls rest)
            rcases result with ⟨target, lastEnv⟩
            exact .cons ⟨_, _, _, _, step⟩ related
    all_goals
      split at success
      · contradiction
      · split at success
        · contradiction
        · rename_i step
          try simp only [Core.Program.typeCheckFuncDecl, bind, Except.bind, tryCatch, tryCatchThe,
            MonadExceptOf.tryCatch, Except.tryCatch] at step
          split at step
          · rename_i evaluated
            obtain rfl := Except.ok.inj step
            repeat' first
              | contradiction
              | (rw [← Except.ok.inj evaluated] at success
                 exact checkedProcedures_prepend_nonproc (ih _ _ _ _ _ success) rfl rfl)
              | split at evaluated
          · contradiction

private theorem coreProgramTypeCheck_procedures (context : Core.Expression.TyContext)
    (environment final : Core.Expression.TyEnv) (raw checked : Core.Program)
    (success : Core.Program.typeCheck context environment raw = .ok (checked, final)) :
    raw.getNames.Nodup ∧ CheckedProcedures raw (procDecls raw.decls) (procDecls checked.decls) := by
  unfold Core.Program.typeCheck at success
  simp only [bind, Except.bind] at success
  split at success
  · contradiction
  · rename_i result finished
    obtain ⟨decls, lastEnv⟩ := result
    have same := congrArg Prod.fst (Except.ok.inj success)
    change ({ decls := decls } : Core.Program) = checked at same
    subst checked
    obtain ⟨rest, eq, related⟩ := typeCheckDecls_procedures _ _ _ _ _ _ _ finished
    refine ⟨Core.WF.Program.typeCheckFunctionNoDup finished, ?_⟩
    simpa using (show CheckedProcedures raw
      (procDecls raw.decls) (procDecls decls) by simpa using eq.symm ▸ related)

private theorem coreTypeCheck_procedures (options : Core.VerifyOptions) (raw checked : Core.Program)
    (success : Core.typeCheck options raw = .ok checked) :
    raw.getNames.Nodup ∧ CheckedProcedures raw (procDecls raw.decls) (procDecls checked.decls) := by
  unfold Core.typeCheck at success
  simp only [bind, Except.bind] at success
  split at success
  · contradiction
  · split at success
    · contradiction
    · rename_i result finished
      obtain ⟨typed, environment⟩ := result
      have same : Core.GenOpaqueTypeParams.closeLemmaTypeVars typed = checked := by
        split at success <;> simpa [dbgTrace, pure, Except.pure] using success
      have typedProcedures := coreProgramTypeCheck_procedures _ _ _ _ _ finished
      have closeProcedures :
          procDecls (Core.GenOpaqueTypeParams.closeLemmaTypeVars typed).decls = procDecls typed.decls := by
        unfold Core.GenOpaqueTypeParams.closeLemmaTypeVars
        induction typed.decls with
        | nil => simp [procDecls]
        | cons declaration rest ih =>
          cases declaration <;> try
            simp_all [procDecls, List.filterMap_cons, Core.Decl.getProc?,
              Core.GenOpaqueTypeParams.opaqueTypes]
          case lemma l md =>
            split
            · simp_all
            · intro a member
              simp only [List.mem_append, List.mem_singleton, List.mem_map] at member
              rcases member with ⟨_, _, rfl⟩ | rfl <;> simp
      rw [← same, closeProcedures]
      exact typedProcedures

private theorem findProc_eq_find (decls : List Core.Decl) (name : String) :
    ({ decls := decls } : Core.Program).findProcByString? name =
      (procDecls decls).find? (fun p => p.header.name.name == name) := by
  unfold Core.Program.findProcByString? Core.Program.find?
  induction decls with
  | nil => rfl
  | cons decl rest ih =>
      cases decl <;>
        simp [Core.Program.find?.go, Core.Decl.kind, procDecls, Core.Decl.getProc?,
          List.filterMap_cons] at ih ⊢
      all_goals try exact ih
      rename_i procedure metadata
      cases id : procedure.header.name with
      | mk procName md =>
          cases md
          by_cases eq : procName = name
          · simp [Core.Decl.name, Core.Decl.getProc?, id, eq]
          · simp [Core.Decl.name, Core.Decl.getProc?, id, eq, ih]

private theorem preamble_procDecls (names : StrataDDM.GlobalContext) (raw : Core.Program) :
    procDecls (withNatPreamble names raw).decls = procDecls raw.decls := by
  simp only [withNatPreamble]
  split
  · rfl
  · have noProcedures : procDecls natCorePreamble = [] := rfl
    simp [procDecls, List.filterMap_append, show List.filterMap Core.Decl.getProc? natCorePreamble = [] from noProcedures]

private theorem getNames_eq_flatMap (decls : List Core.Decl) :
    Core.Program.getNames.go decls = decls.flatMap Core.Decl.names := by
  induction decls with
  | nil => rfl
  | cons _ _ => simp [Core.Program.getNames.go]

private theorem procNames_sublist (decls : List Core.Decl) :
    ((procDecls decls).map (·.header.name)).Sublist (decls.flatMap Core.Decl.names) := by
  induction decls with
  | nil => exact .slnil
  | cons declaration rest ih =>
    cases declaration <;>
      simp only [procDecls, Core.Decl.getProc?, List.filterMap_cons, List.map_cons,
        List.flatMap_cons] at ih ⊢
    all_goals
      first
      | exact List.Sublist.cons_cons _ ih
      | exact ih.trans (List.sublist_append_right _ _)

private theorem find_unique_procedure (procedures : List Core.Procedure) (procedure : Core.Procedure)
    (present : procedure ∈ procedures)
    (distinct : (procedures.map (·.header.name)).Nodup) :
    procedures.find? (fun p => p.header.name.name == procedure.header.name.name) = some procedure := by
  induction procedures with
  | nil => simp at present
  | cons first rest ih =>
    rcases List.mem_cons.mp present with rfl | later
    · simp
    · simp only [List.map_cons, List.nodup_cons] at distinct
      have different : first.header.name.name ≠ procedure.header.name.name := by
        intro eq
        have sameName : ∀ a b : Core.CoreIdent, a.name = b.name → a = b := by
          rintro ⟨a, ⟨⟩⟩ ⟨b, ⟨⟩⟩ same
          cases same
          rfl
        exact distinct.1 ((sameName _ _ eq).symm ▸ List.mem_map_of_mem later)
      have test : (first.header.name.name == procedure.header.name.name) = false :=
        beq_eq_false_iff_ne.mpr different
      simp [test, ih later distinct.2]

private theorem find_raw_procedure_of_mem (source : Boole.Program) (names : StrataDDM.GlobalContext)
    (raw checked : Core.Program) (lowered : toCoreProgram source names = .ok raw)
    (typeChecked : checkedCoreProgram source names = .ok checked)
    (procedure : Core.Procedure) (metadata : Imperative.MetaData Core.Expression)
    (member : Core.Decl.proc procedure metadata ∈ raw.decls) :
    raw.findProcByString? procedure.header.name.name = some procedure := by
  have success : Core.typeCheck .default (withNatPreamble names raw) = .ok checked := by
    simpa [checkedCoreProgram, lowered, bind, Except.bind] using typeChecked
  have unique := (coreTypeCheck_procedures _ _ _ success).1
  rw [Core.Program.getNames, getNames_eq_flatMap] at unique
  have sublist := procNames_sublist (withNatPreamble names raw).decls
  have distinct := List.Nodup.sublist sublist unique
  rw [preamble_procDecls] at distinct
  have present : procedure ∈ procDecls raw.decls :=
    List.mem_filterMap.mpr ⟨_, member, rfl⟩
  change ({ decls := raw.decls } : Core.Program).findProcByString? _ = _
  rw [findProc_eq_find]
  exact find_unique_procedure _ _ present distinct

private theorem checkedProcedures_find {program : Core.Program} {raw checked : List Core.Procedure}
    (related : CheckedProcedures program raw checked) (name : String) (before : Core.Procedure)
    (found : raw.find? (fun p => p.header.name.name == name) = some before) :
    ∃ after, checked.find? (fun p => p.header.name.name == name) = some after ∧
      ProcedureWasChecked program before after := by
  induction related with
  | nil => simp at found
  | cons relatedHead _ ih =>
      obtain ⟨context, environment, final, metadata, passed⟩ := relatedHead
      have same := checkedProcedure_name _ _ _ _ _ _ _ passed
      simp only [List.find?_cons, same] at found ⊢
      split at found
      · obtain rfl := Option.some.inj found
        exact ⟨_, rfl, ⟨_, _, _, _, passed⟩⟩
      · rename_i notFound
        simpa using ih found

/-- Each raw procedure found by name has a matching checked declaration, with
the successful invocation of Core's procedure checker available for proofs. -/
theorem checkedLowering_matchProcedure (source : Boole.Program) (names : StrataDDM.GlobalContext)
    (raw checked : Core.Program) (lowered : toCoreProgram source names = .ok raw)
    (typeChecked : checkedCoreProgram source names = .ok checked) (name : String)
    (before : Core.Procedure) (found : raw.findProcByString? name = some before) :
    ∃ after, checked.findProcByString? name = some after ∧
      ProcedureWasChecked (withNatPreamble names raw) before after := by
  have success : Core.typeCheck .default (withNatPreamble names raw) = .ok checked := by
    simpa [checkedCoreProgram, lowered, bind, Except.bind] using typeChecked
  have related := (coreTypeCheck_procedures _ _ _ success).2
  rw [preamble_procDecls] at related
  change ({ decls := raw.decls } : Core.Program).findProcByString? name = some before at found
  rw [findProc_eq_find] at found
  have foundChecked : ∀ after, checked.findProcByString? name = some after ↔
      (procDecls checked.decls).find? (fun p => p.header.name.name == name) = some after := by
    intro after
    rw [← findProc_eq_find]
  simp only [foundChecked]
  exact checkedProcedures_find related name before found

end Strata.Boole

/-! ## Procedure lookup through Boole lowering -/

namespace Strata.Boole

open StrataDDM

private def sourceProcedureName? : BooleDDM.Command SourceRange → Option String
  | .boole_procedure _ name _ _ _ _ _ _ => some name.val
  | .command_procedure _ _ name _ _ _ _ => some name.val
  | _ => none

private theorem withScope_success {action : InterpM α} {initial final : Scope}
    {value : α} (success : withScope action initial = .ok (value, final)) :
    ∃ intermediate, action initial = .ok (value, intermediate) := by
  simp only [withScope, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
    get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set] at success
  split at success
  · contradiction
  · rename_i result evaluated
    have same := congrArg Prod.fst (Except.ok.inj success)
    exact ⟨result.2, by cases result; simp_all⟩

private theorem interpProc_name (I : Interpretation) (range : SourceRange) (name : String)
    (types : Option (BooleDDM.TypeArgs SourceRange)) (inputs : BooleDDM.Bindings SourceRange)
    (outputs : Option (BooleDDM.MonoDeclList SourceRange)) (spec : Option (BooleDDM.Spec SourceRange))
    (body : Option (BooleDDM.Block SourceRange)) (initial : Scope)
    (result : InterpProcedure I.Expression I.Statement × Scope)
    (success : interpProc I range name types inputs outputs spec body initial = .ok result) :
    result.1.name = name := by
  obtain ⟨procedure, final⟩ := result
  unfold interpProc at success
  obtain ⟨_, success⟩ := withScope_success success
  cases types <;> cases outputs <;> cases body <;>
    simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
      Option.isSome, Bool.false_eq_true, ite_false, ite_true, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet] at success
  all_goals repeat' first
    | contradiction
    | exact congrArg (fun pair => pair.1.name) (Except.ok.inj success).symm
    | simp only [StateT.bind, StateT.pure, StateT.modifyGet, Except.bind, pure,
        Except.pure, reject, throw, throwThe, MonadExceptOf.throw, StateT.throw, Except.throw] at success
    | split at success

private theorem translateProcedureDecl_names (range : SourceRange) (name : String) (types : List String)
    (inputs outputs : ListMap Core.CoreIdent Lambda.LMonoTy)
    (spec : Option (BooleDDM.Spec SourceRange)) (body : Option (BooleDDM.Block SourceRange))
    (initial final : TranslateState) (decls : List Core.Decl)
    (success : translateProcedureDecl range name types inputs outputs spec body initial = .ok (decls, final)) :
    decls.filterMap procName? = [name] := by
  cases body <;>
    simp only [translateProcedureDecl, bind, StateT.bind, Except.bind, pure, StateT.pure,
      Except.pure, get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet,
      MonadStateOf.modifyGet, StateT.modifyGet] at success
  all_goals repeat' first
    | contradiction
    | exact congrArg (fun pair => pair.1.filterMap procName?) (Except.ok.inj success).symm
    | split at success

private theorem withTypeBVars_success {types : List String} {action : TranslateM α}
    {initial final : TranslateState} {value : α}
    (success : withTypeBVars types action initial = .ok (value, final)) :
    ∃ next, action { initial with tyBVars := initial.tyBVars ++ types.toArray } = .ok (value, next) := by
  simp only [withTypeBVars, bind, StateT.bind, Except.bind, pure, Except.pure,
    get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, tryCatch, tryCatchThe, MonadExceptOf.tryCatch] at success
  cases run : action { initial with tyBVars := initial.tyBVars ++ types.toArray } with
  | error message =>
      simp [run, throw, throwThe, MonadExceptOf.throw, StateT.lift,
        Except.tryCatch, Functor.map, Except.map] at success
  | ok pair =>
      obtain ⟨result, next⟩ := pair
      have same : result = value := by
        simpa [run, EarlyReturnT.return, EarlyReturn.runK, throw, throwThe,
          MonadExceptOf.throw, ExceptT.mk, pure, StateT.pure, Except.pure, Except.tryCatch, Except.map] using
          congrArg (Except.map Prod.fst) success
      exact ⟨next, by simp [same]⟩

private theorem toCoreDecls_contains_proc (command : BooleDDM.Command SourceRange)
    (name : String) (initial final : TranslateState) (decls : List Core.Decl)
    (named : sourceProcedureName? command = some name)
    (success : toCoreDecls command initial = .ok (decls, final)) :
    name ∈ decls.filterMap procName? := by
  cases command <;> simp [sourceProcedureName?] at named
  case boole_procedure range label types inputs outputs decreases spec body =>
    subst name
    cases ht : types.val <;> cases ho : outputs.val <;>
      simp only [toCoreDecls, ht, ho] at success <;>
      obtain ⟨_, success⟩ := withTypeBVars_success success
    all_goals
      simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at success
      repeat' first
        | contradiction
        | (rw [translateProcedureDecl_names _ _ _ _ _ _ _ _ _ _ success]; simp)
        | split at success
  case command_procedure range annotations label types inputs spec body =>
    subst name
    cases ht : types.val <;> cases ha : hasOutOrInoutBinding inputs
    all_goals
      simp only [toCoreDecls, ht, ha] at success
      first
      | obtain ⟨_, success⟩ := withTypeBVars_success success
        simp only [bind, StateT.bind, Except.bind] at success
        split at success
        · contradiction
        · rw [translateProcedureDecl_names _ _ _ _ _ _ _ _ _ _ success]
          simp
      | simp [throwAt, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
          StateT.get, throw, throwThe, MonadExceptOf.throw, StateT.lift, pure, Except.pure] at success

private theorem mapM_success_member {action : α → StateT σ (Except ε) β}
    (xs : List α) (initial final : σ) (results : List β) (x : α) (member : x ∈ xs)
    (success : (xs.mapM action) initial = .ok (results, final)) :
    ∃ value before after, value ∈ results ∧ action x before = .ok (value, after) := by
  induction xs generalizing initial results with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.mapM_cons, bind, StateT.bind, Except.bind, pure, StateT.pure,
        Except.pure] at success
      cases firstRun : action first initial with
      | error message => simp [firstRun] at success
      | ok step =>
          obtain ⟨value, next⟩ := step
          cases restRun : (rest.mapM action) next with
          | error message => simp [firstRun, restRun] at success
          | ok tail =>
              obtain ⟨values, last⟩ := tail
              have same : value :: values = results := by
                simpa [firstRun, restRun, Except.map] using congrArg (Except.map Prod.fst) success
              subst results
              rcases List.mem_cons.mp member with rfl | later
              · exact ⟨value, initial, next, by simp, firstRun⟩
              · have lastEq : last = final := by
                  simpa [firstRun, restRun, Except.map] using congrArg (Except.map Prod.snd) success
                subst last
                obtain ⟨chosen, before, after, present, executed⟩ := ih next values later restRun
                exact ⟨chosen, before, after, List.mem_cons_of_mem _ present, executed⟩

/-- The call to the original declaration lowerer that emitted this procedure. -/
def ProcedureWasLowered (command : BooleDDM.Command SourceRange) (procedure : Core.Procedure) : Prop :=
  ∃ initial final declarations metadata,
    toCoreDecls command initial = .ok (declarations, final) ∧
      Core.Decl.proc procedure metadata ∈ declarations

private theorem toCoreProgram_lowered_procedure (source : Boole.Program) (names : GlobalContext)
    (raw : Core.Program) (command : BooleDDM.Command SourceRange) (name : String)
    (member : match source with | .prog _ cmds => command ∈ cmds.val.toList)
    (named : sourceProcedureName? command = some name)
    (success : toCoreProgram source names = .ok raw) :
    ∃ procedure metadata, Core.Decl.proc procedure metadata ∈ raw.decls ∧
      procedure.header.name.name = name ∧ ProcedureWasLowered command procedure := by
  cases source with
  | prog range commands =>
    simp only [toCoreProgram, bind, Except.bind, StateT.run', Functor.map, Except.map] at success
    split at success
    · contradiction
    · rename_i prepass _
      simp only [StateT.bind, pure, StateT.pure, Except.pure] at success
      rw [Array.mapM_eq_mapM_toList] at success
      simp only [Functor.map, StateT.map, bind, Except.bind, pure, Except.pure] at success
      let initial : TranslateState := {
        gctx := names, modifiesMap := prepass.2, globalVarTypes := prepass.1 }
      cases run : (commands.val.toList.mapM toCoreDecls) initial with
      | error message => simp [show (commands.val.toList.mapM toCoreDecls) { gctx := names, modifiesMap := prepass.2, globalVarTypes := prepass.1 } = _ from run] at success
      | ok result =>
        obtain ⟨parts, final⟩ := result
        have same : { decls := parts.flatten : Core.Program } = raw := by
          simpa [show (commands.val.toList.mapM toCoreDecls) { gctx := names, modifiesMap := prepass.2, globalVarTypes := prepass.1 } = _ from run] using success
        subst raw
        obtain ⟨part, before, after, included, translated⟩ :=
          mapM_success_member commands.val.toList initial final parts command member run
        obtain ⟨decl, inPart, declName⟩ :=
          List.mem_filterMap.mp (toCoreDecls_contains_proc command name before after part named translated)
        cases decl <;> simp only [procName?] at declName <;> try contradiction
        rename_i procedure metadata
        exact ⟨procedure, metadata, List.mem_flatten.mpr ⟨part, included, inPart⟩,
          Option.some.inj declName, before, after, part, metadata, translated, inPart⟩

/-- The source declaration and interpreter call that produced a procedure meaning. -/
def ProcedureWasInterpreted (I : Interpretation) (command : BooleDDM.Command SourceRange)
    (procedure : InterpProcedure I.Expression I.Statement) : Prop :=
  match command with
  | .boole_procedure range name types inputs outputs _ spec body =>
      ∃ initial final,
        interpProc I range name.val types.val inputs outputs.val spec.val body.val initial =
          .ok (procedure, final)
  | .command_procedure range _ name types inputs spec body =>
      ∃ initial final,
        interpProc I range name.val types.val inputs none spec.val body.val initial =
          .ok (procedure, final)
  | _ => False

private theorem interpretedProcedure_name {I : Interpretation}
    {command : BooleDDM.Command SourceRange} {procedure : InterpProcedure I.Expression I.Statement}
    (interpreted : ProcedureWasInterpreted I command procedure) :
    sourceProcedureName? command = some procedure.name := by
  cases command <;> simp only [ProcedureWasInterpreted] at interpreted
  all_goals
    first
    | contradiction
    | obtain ⟨_, _, ran⟩ := interpreted
      have name := interpProc_name _ _ _ _ _ _ _ _ _ _ ran
      simpa [sourceProcedureName?] using name.symm

private theorem forIn_procedure_origin (I : Interpretation)
    (step : BooleDDM.Command SourceRange → List (InterpProcedure I.Expression I.Statement) →
      InterpM (ForInStep (List (InterpProcedure I.Expression I.Statement))))
    (origin : ∀ command previous state outcome next,
      step command previous state = .ok (outcome, next) →
      ∀ procedure ∈ outcome.value,
        procedure ∈ previous ∨ ProcedureWasInterpreted I command procedure)
    (commands : List (BooleDDM.Command SourceRange))
    (previous procedures : List (InterpProcedure I.Expression I.Statement))
    (initial final : Scope) (success : (forIn commands previous step) initial = .ok (procedures, final))
    (procedure : InterpProcedure I.Expression I.Statement) (member : procedure ∈ procedures) :
    procedure ∈ previous ∨ ∃ command ∈ commands, ProcedureWasInterpreted I command procedure := by
  induction commands generalizing previous initial with
  | nil =>
      have same : previous = procedures := congrArg Prod.fst (Except.ok.inj success)
      exact Or.inl (same.symm ▸ member)
  | cons command rest ih =>
      simp only [List.forIn_cons, bind, StateT.bind, Except.bind, pure] at success
      cases run : step command previous initial with
      | error message => simp [run] at success
      | ok result =>
          obtain ⟨outcome, next⟩ := result
          cases outcome with
          | done current =>
              have same : current = procedures := by
                simpa [run, Except.map, StateT.pure, pure, Except.pure] using congrArg (Except.map Prod.fst) success
              subst current
              rcases origin _ _ _ _ _ run _ member with already | named
              · exact Or.inl already
              · exact Or.inr ⟨command, by simp, named⟩
          | yield current =>
              have continued : (forIn rest current step) next = .ok (procedures, final) := by
                simpa [run] using success
              rcases ih current next continued with present | ⟨other, otherMember, named⟩
              · rcases origin _ _ _ _ _ run _ present with already | named
                · exact Or.inl already
                · exact Or.inr ⟨command, by simp, named⟩
              · exact Or.inr ⟨other, List.mem_cons_of_mem _ otherMember, named⟩

set_option linter.unusedSimpArgs false in
private theorem interpProgram_procedure_origin (I : Interpretation) (source : Boole.Program)
    (names : GlobalContext) (meaning : InterpProgram I.Expression I.Statement)
    (success : interpProgram I source names = .ok meaning)
    (procedure : InterpProcedure I.Expression I.Statement) (member : procedure ∈ meaning.procedures) :
    ∃ command, (match source with | .prog _ cmds => command ∈ cmds.val.toList) ∧
      ProcedureWasInterpreted I command procedure := by
  cases source with
  | prog range commands =>
      simp only [interpProgram, StateT.run', Functor.map, Except.map, bind, StateT.bind, Except.bind,
        get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure] at success
      split at success
      · contradiction
      · rename_i result executed
        split at executed
        · contradiction
        · rename_i stepResult loopRan
          have same : result.1 = meaning := Except.ok.inj success
          subst meaning
          have proceduresEq : stepResult.1 = result.1.procedures :=
            congrArg (fun pair => pair.1.procedures) (Except.ok.inj executed)
          rw [← proceduresEq] at member
          rw [← (Array.toArray_toList (xs := commands.val)), List.forIn_toArray] at loopRan
          refine (forIn_procedure_origin I _ ?_ _ _ _ _ _ loopRan _ member).resolve_left (by simp)
          intro command previous state outcome next stepSuccess p present
          cases command
          all_goals
            repeat' first
              | contradiction
              | (have eq := congrArg (fun pair => pair.1.value) (Except.ok.inj stepSuccess)
                 rw [← eq] at present
                 exact Or.inl present)
              | (have eq := congrArg (fun pair => pair.1.value) (Except.ok.inj stepSuccess)
                 rw [← eq] at present
                 change p ∈ previous ++ [_] at present
                 rcases List.mem_append.mp present with old | added
                 · exact Or.inl old
                 · obtain rfl := List.mem_singleton.mp added
                   right
                   rename_i result called
                   simp only [ProcedureWasInterpreted]
                   exact ⟨_, result.2, by cases result; exact called⟩)
              | simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, reject,
                  throw, throwThe, MonadExceptOf.throw, StateT.lift, Functor.map, Except.map,
                  modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at stepSuccess
              | split at stepSuccess

/-- Recover the two interpretation calls for a denoted procedure and the
occurrence of its lowered Core declaration. -/
theorem lowered_procedure_origin (source : Boole.Program) (names : GlobalContext)
    (meaning : ProgramMeaning) (raw : Core.Program)
    (denoted : denoteProgram source names = .ok meaning)
    (lowered : toCoreProgram source names = .ok raw)
    (procedure : ProcedureMeaning) (member : procedure ∈ meaning.procedures) :
    ∃ command target metadata, ProcedureWasInterpreted denotation command procedure ∧
      ProcedureWasLowered command target ∧ Core.Decl.proc target metadata ∈ raw.decls ∧
      target.header.name.name = procedure.name := by
  obtain ⟨command, present, interpreted⟩ :=
    interpProgram_procedure_origin denotation source names meaning denoted procedure member
  obtain ⟨target, metadata, inRaw, sameName, translated⟩ :=
    toCoreProgram_lowered_procedure source names raw command procedure.name present
      (interpretedProcedure_name interpreted) lowered
  exact ⟨command, target, metadata, interpreted, translated, inRaw, sameName⟩

/-- A denoted procedure and the raw Core procedure found by its name come
from the same source declaration. Both construction calls are available. -/
theorem find_lowered_procedure (source : Boole.Program) (names : GlobalContext)
    (meaning : ProgramMeaning) (raw checked : Core.Program)
    (denoted : denoteProgram source names = .ok meaning)
    (lowered : toCoreProgram source names = .ok raw)
    (typeChecked : checkedCoreProgram source names = .ok checked)
    (procedure : ProcedureMeaning) (member : procedure ∈ meaning.procedures) :
    ∃ command target, ProcedureWasInterpreted denotation command procedure ∧
      ProcedureWasLowered command target ∧ raw.findProcByString? procedure.name = some target := by
  obtain ⟨command, target, metadata, interpreted, translated, inRaw, sameName⟩ :=
    lowered_procedure_origin source names meaning raw denoted lowered procedure member
  refine ⟨command, target, interpreted, translated, ?_⟩
  rw [← sameName]
  exact find_raw_procedure_of_mem source names raw checked lowered typeChecked target metadata inRaw

/-- Evidence from the original pipelines for a single matched declaration.
The program-level successes retain the context needed to relate global
collection and lexical scopes in the two declaration calls. -/
structure MatchedProcedure where
  program : Boole.Program
  names : GlobalContext
  meaning : ProgramMeaning
  checked : Core.Program
  raw : Core.Program
  command : BooleDDM.Command SourceRange
  source : ProcedureMeaning
  loweredProcedure : Core.Procedure
  target : Core.Procedure
  fragment : inConcreteCoreFragment program names
  denoted : denoteProgram program names = .ok meaning
  lowered : toCoreProgram program names = .ok raw
  typeChecked : checkedCoreProgram program names = .ok checked
  member : source ∈ meaning.procedures
  interpreted : ProcedureWasInterpreted denotation command source
  translated : ProcedureWasLowered command loweredProcedure
  foundRaw : raw.findProcByString? source.name = some loweredProcedure
  foundTarget : checked.findProcByString? source.name = some target
  checkedProcedure : ProcedureWasChecked (withNatPreamble names raw) loweredProcedure target


private theorem exceptForIn_preserves {α β ε : Type} (items : List α)
    (step : α → β → Except ε (ForInStep β)) (invariant : β → Prop)
    (preserved : ∀ item state control, step item state = .ok control → invariant state →
      invariant (match control with | .done next | .yield next => next))
    {first final : β} (initial : invariant first)
    (ran : forIn items first step = .ok final) : invariant final := by
  induction items generalizing first with
  | nil =>
    obtain rfl := Except.ok.inj ran
    exact initial
  | cons item items ih =>
    simp only [List.forIn_cons, bind, Except.bind] at ran
    cases h : step item first with
    | error e => simp [h] at ran
    | ok control =>
      have next := preserved _ _ _ h initial
      cases control with
      | done state =>
        have same : state = final := by simpa [h, pure, Except.pure] using ran
        exact same ▸ next
      | yield state =>
        exact ih next (by simpa only [h] using ran)

/-- Each modified parameter is looked up in the global table by its source
name and keeps exactly the type recorded there. -/
private theorem collectModifies_registered
    (file procedure : String) (spec : Option (BooleDDM.Spec SourceRange))
    (table : Std.HashMap String Lambda.LMonoTy)
    (modified : List (Core.CoreIdent × Lambda.LMonoTy))
    (ran : collectModifiesFromSpec file procedure spec table = .ok modified) :
    ∀ pair ∈ modified, (pair.1.name, pair.2) ∈ table.toList := by
  cases spec with
  | none =>
    have empty : [] = modified := Except.ok.inj ran
    simp [← empty]
  | some spec =>
    obtain ⟨range, ⟨ann, elements⟩⟩ := spec
    unfold collectModifiesFromSpec at ran
    simp only [bind, Except.bind] at ran
    split at ran
    · contradiction
    · rename_i reversed loop
      let registered (xs : List (Core.CoreIdent × Lambda.LMonoTy)) :=
        ∀ pair ∈ xs, (pair.1.name, pair.2) ∈ table.toList
      have inv : registered reversed := by
        refine exceptForIn_preserves _ _ registered ?_ (by simp [registered]) loop
        intro element state control success previous
        cases element
        all_goals try
          (obtain rfl := Except.ok.inj success
           exact previous)
        rename_i range names
        obtain ⟨ann, names⟩ := names
        dsimp at success
        split at success
        · contradiction
        · rename_i next inner
          obtain rfl := (Except.ok.inj success).symm
          refine exceptForIn_preserves _ _ registered ?_ previous inner
          intro name before control step earlier
          obtain ⟨ann, name⟩ := name
          dsimp at step
          split at step
          · rename_i ty found
            obtain rfl := (Except.ok.inj step).symm
            intro pair member
            rcases List.mem_cons.mp member with rfl | old
            · exact Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr found
            · exact earlier _ old
          · contradiction
      have result : reversed.reverse = modified := Except.ok.inj ran
      intro pair member
      exact inv pair (List.mem_reverse.mp (result.symm ▸ member))

/-- Sorting the modified and read-only parameters changes only their order.
If the modified parameters are distinct entries from the global table, the
two parts of the generated prefix contain all globals exactly once. -/
private theorem globalParamPrefix_perm (state : TranslateState) (name : String)
    (modified readOnly : List (Core.CoreIdent × Lambda.LMonoTy))
    (computed : getGlobalParamPrefix name state = .ok ((modified, readOnly), state))
    (distinct : modified.Nodup)
    (registered : ∀ pair ∈ modified,
      (pair.1.name, pair.2) ∈ state.globalVarTypes.toList) :
    ((modified ++ readOnly).map fun (id, ty) => (id.name, ty)).Perm state.globalVarTypes.toList := by
  let keep : String × Lambda.LMonoTy → Bool :=
    fun (key, _) => (modified.map (·.1.name)).contains key
  have matchModified : (modified.map fun (id, ty) => (id.name, ty)).Perm
      (state.globalVarTypes.toList.filter keep) := by
    have distinctTable : state.globalVarTypes.toList.Pairwise (fun a b => (a.1 == b.1) = false) :=
      Std.HashMap.distinct_keys_toList
    have strip_injective (a b : Core.CoreIdent × Lambda.LMonoTy)
        (same : (a.1.name, a.2) = (b.1.name, b.2)) : a = b := by
      rcases a with ⟨⟨a, ⟨⟩⟩, aty⟩
      rcases b with ⟨⟨b, ⟨⟩⟩, bty⟩
      cases same
      rfl
    have noDuplicates :
        (modified.map fun (id, ty) => (id.name, ty)).Nodup :=
      List.pairwise_map.mpr (distinct.imp fun ne eq => ne (strip_injective _ _ eq))
    have tableNodup : state.globalVarTypes.toList.Nodup :=
      distinctTable.imp fun ne same => by subst_vars; simp at ne
    apply (List.perm_ext_iff_of_nodup noDuplicates (tableNodup.sublist List.filter_sublist)).mpr
    rintro ⟨key, ty⟩
    constructor
    · intro present
      obtain ⟨pair, member, eq⟩ := List.mem_map.mp present
      have sameName : pair.1.name = key := congrArg Prod.fst eq
      have sameType : pair.2 = ty := congrArg Prod.snd eq
      exact List.mem_filter.mpr ⟨by simpa only [sameName, sameType] using registered pair member,
        List.contains_iff_mem.mpr (List.mem_map.mpr ⟨pair, member, sameName⟩)⟩
    · intro present
      obtain ⟨registeredKey, inNames⟩ := List.mem_filter.mp present
      obtain ⟨pair, member, eq⟩ := List.mem_map.mp (List.contains_iff_mem.mp inNames)
      have hasType := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp (registered pair member)
      have hasOtherType := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp registeredKey
      rw [eq, hasOtherType] at hasType
      exact List.mem_map.mpr ⟨pair, member, Prod.ext eq (Option.some.inj hasType.symm)⟩
  have readOnly_eq : readOnly =
      ((state.globalVarTypes.toList.filter fun pair => !keep pair).map
        (fun (key, ty) => (mkIdent key, ty))).mergeSort (·.1.name < ·.1.name) := by
    have filtered (globals : List (String × Lambda.LMonoTy)) :
        (globals.filterMap fun (key, ty) =>
          if (modified.map (·.1.name)).contains key then none else some (mkIdent key, ty)) =
        (globals.filter fun pair => !keep pair).map (fun (key, ty) => (mkIdent key, ty)) := by
      rw [← List.filterMap_eq_map' (f := fun (p : String × Lambda.LMonoTy) =>
        (mkIdent p.1, p.2)), List.filterMap_filter]
      congr 1
      funext pair
      obtain ⟨key, ty⟩ := pair
      change (if keep (key, ty) then none else some (mkIdent key, ty)) =
        if !keep (key, ty) then some (mkIdent key, ty) else none
      cases keep (key, ty) <;> rfl
    unfold getGlobalParamPrefix at computed
    change Except.ok ((_, _), state) = .ok ((modified, readOnly), state) at computed
    have paired := congrArg Prod.fst (Except.ok.inj computed)
    obtain ⟨mods, reads⟩ := Prod.mk.inj paired
    rw [mods, filtered] at reads
    exact reads.symm
  have matchReadOnly : (readOnly.map fun (id, ty) => (id.name, ty)).Perm
      (state.globalVarTypes.toList.filter fun pair => !keep pair) := by
    rw [readOnly_eq]
    exact ((List.mergeSort_perm _ _).map
      (fun (pair : Core.CoreIdent × Lambda.LMonoTy) => (pair.1.name, pair.2))).trans
      (by simp [List.map_map, Function.comp_def, mkIdent])
  rw [List.map_append]
  exact (matchModified.append matchReadOnly).trans (List.filter_append_perm keep _)

/-- Recover the actual global prefix and explicit formals from the call
that emitted a Core procedure header. -/
private theorem translateProcedureDecl_header (range : SourceRange) (name : String)
    (types : List String) (inputs outputs : ListMap Core.CoreIdent Lambda.LMonoTy)
    (spec : Option (BooleDDM.Spec SourceRange)) (body : Option (BooleDDM.Block SourceRange))
    (entry final : TranslateState) (decls : List Core.Decl)
    (ran : translateProcedureDecl range name types inputs outputs spec body entry = .ok (decls, final))
    (procedure : Core.Procedure) (metadata : Imperative.MetaData Core.Expression)
    (present : .proc procedure metadata ∈ decls) :
    ∃ modified readOnly,
      getGlobalParamPrefix name entry = .ok ((modified, readOnly), entry) ∧
      procedure.header.typeArgs = types ∧
      procedure.header.inputs = modified ++ readOnly ++ inputs ∧
      procedure.header.outputs = modified ++ outputs := by
  cases body
  all_goals
    repeat' first
      | contradiction
      | simp only [translateProcedureDecl, getGlobalParamPrefix, bind, StateT.bind, Except.bind, pure, StateT.pure,
          Except.pure, get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet,
          MonadStateOf.modifyGet, StateT.modifyGet] at ran
      | (have equal : _ = decls := congrArg Prod.fst (Except.ok.inj ran)
         rw [← equal] at present
         simp only [List.mem_singleton, Core.Decl.proc.injEq] at present
         rcases present with ⟨rfl, rfl⟩
         exact ⟨_, _, rfl, rfl, rfl, rfl⟩)
      | split at ran

private def commandTypes? : BooleDDM.Command SourceRange → Option (BooleDDM.TypeArgs SourceRange)
  | .boole_procedure _ _ types _ _ _ _ _ => types.val
  | .command_procedure _ _ _ types _ _ _ => types.val
  | _ => none

private theorem interpretedProcedure_noTypeArguments {I : Interpretation}
    {command : BooleDDM.Command SourceRange} {procedure : InterpProcedure I.Expression I.Statement}
    (interpreted : ProcedureWasInterpreted I command procedure) : commandTypes? command = none := by
  cases command <;> simp only [ProcedureWasInterpreted] at interpreted
  all_goals try contradiction
  case' boole_procedure range name types parameters outputs decreases specification body =>
    obtain ⟨_, types⟩ := types
    cases types
  case' command_procedure range annotations name types parameters specification body =>
    obtain ⟨_, types⟩ := types
    cases types
  all_goals first
    | rfl
    | obtain ⟨_, _, called⟩ := interpreted
      unfold interpProc at called
      obtain ⟨_, ran⟩ := withScope_success called
      contradiction

/-- Recover the split between generated globals and explicit parameters in
the raw header, with the global table used by the legacy lowerer. -/
theorem lowered_header_parts_of_nodup
    {command : BooleDDM.Command SourceRange} {source : ProcedureMeaning} {raw : Core.Procedure}
    (interpreted : ProcedureWasInterpreted denotation command source)
    (translated : ProcedureWasLowered command raw)
    (outputsNodup : raw.header.outputs.keys.Nodup) :
    raw.header.typeArgs = [] ∧
    ∃ (globalTable : Std.HashMap String Lambda.LMonoTy)
      (modified readOnly inputs outputs : List (Core.CoreIdent × Lambda.LMonoTy)),
      raw.header.inputs.toList = modified ++ readOnly ++ inputs ∧
      raw.header.outputs.toList = modified ++ outputs ∧
      (modified.map Prod.fst).Nodup ∧
      ((∀ pair ∈ modified, (pair.1.name, pair.2) ∈ globalTable.toList) →
        ((modified ++ readOnly).map fun (id, ty) => (id.name, ty)).Perm globalTable.toList) := by
  have mono := interpretedProcedure_noTypeArguments interpreted
  obtain ⟨entry, final, decls, metadata, ran, present⟩ := translated
  cases shape : command <;> simp only [shape, ProcedureWasInterpreted] at interpreted
  all_goals try contradiction
  all_goals
    simp only [shape, commandTypes?] at mono
    simp only [shape, toCoreDecls, mono] at ran
  case' boole_procedure range name types parameters outputs decreases specification body =>
    obtain ⟨_, outputs⟩ := outputs
    cases outputs
  case' command_procedure range annotations name types inputs specification body =>
    cases modifiers : hasOutOrInoutBinding inputs
    case some bad =>
      obtain ⟨parameter, modifier⟩ := bad
      simp [modifiers, bind, StateT.bind, Except.bind, throwAt, throw, throwThe,
        MonadExceptOf.throw, get, getThe, MonadStateOf.get, StateT.get, StateT.lift,
        pure, Except.pure] at ran
    case' none => simp only [modifiers] at ran
  all_goals
    obtain ⟨_, ran⟩ := withTypeBVars_success ran
    obtain ⟨inputs, outputs, _, _, modified, readOnly, _, rfl, computed, mono, hin, hout⟩ :
        ∃ (inputs outputs : ListMap Core.CoreIdent Lambda.LMonoTy) (state : TranslateState)
          (name : String) (modified readOnly : List (Core.CoreIdent × Lambda.LMonoTy))
          (globalTable : Std.HashMap String Lambda.LMonoTy),
          globalTable = state.globalVarTypes ∧
          getGlobalParamPrefix name state = .ok ((modified, readOnly), state) ∧
          raw.header.typeArgs = [] ∧
          raw.header.inputs.toList = modified ++ readOnly ++ inputs.toList ∧
          raw.header.outputs.toList = modified ++ outputs.toList := by
      repeat' first
        | contradiction
        | simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
        | (obtain ⟨modified, readOnly, computed, mono, hin, hout⟩ :=
            translateProcedureDecl_header _ _ [] _ _ _ _ _ _ _ ran _ _ present
           exact ⟨_, _, _, _, modified.toList, readOnly.toList, _, rfl, computed, mono,
             congrArg ListMap.toList hin, congrArg ListMap.toList hout⟩)
        | split at ran
    have unique := outputsNodup
    rw [ListMap.keys_eq_map_fst] at unique
    change (raw.header.outputs.toList.map Prod.fst).Nodup at unique
    rw [hout, List.map_append] at unique
    have distinct := (List.nodup_append.mp unique).1
    exact ⟨mono, _, modified, readOnly, inputs.toList, outputs.toList, hin, hout, distinct,
      globalParamPrefix_perm _ _ _ _ computed (List.pairwise_map.mp distinct |>.imp (fun ne same => ne (congrArg Prod.fst same)))⟩

/-- Recover the raw header parts for a procedure accepted by the current checker. -/
theorem MatchedProcedure.lowered_header_parts (matched : MatchedProcedure) :
    matched.loweredProcedure.header.typeArgs = [] ∧
    ∃ (globalTable : Std.HashMap String Lambda.LMonoTy)
      (modified readOnly inputs outputs : List (Core.CoreIdent × Lambda.LMonoTy)),
      matched.loweredProcedure.header.inputs.toList = modified ++ readOnly ++ inputs ∧
      matched.loweredProcedure.header.outputs.toList = modified ++ outputs ∧
      (modified.map Prod.fst).Nodup ∧
      ((∀ pair ∈ modified, (pair.1.name, pair.2) ∈ globalTable.toList) →
        ((modified ++ readOnly).map fun (id, ty) => (id.name, ty)).Perm globalTable.toList) :=
  lowered_header_parts_of_nodup matched.interpreted matched.translated
    (checkedProcedure_rawOutputsNodup matched.checkedProcedure)

/-- A source procedure accepted by the interpreter lowers to a monomorphic
Core procedure. This refers to the raw header before Core checks it. -/
theorem MatchedProcedure.lowered_header_monomorphic (matched : MatchedProcedure) :
    matched.loweredProcedure.header.typeArgs = [] :=
  matched.lowered_header_parts.1

private theorem withBVars_success {xs : List String} {action : TranslateM α}
    {initial final : TranslateState} {value : α}
    (success : withBVars xs action initial = .ok (value, final)) :
    ∃ before after, action before = .ok (value, after) := by
  simp only [withBVars, bind, StateT.bind, Except.bind, pure, Except.pure,
    get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, tryCatch, tryCatchThe, MonadExceptOf.tryCatch] at success
  let fresh := xs.toArray.map (fun n => (.fvar () (mkIdent n) none : Core.Expression.Expr))
  let before := { initial with bvars := initial.bvars ++ fresh }
  cases run : action before with
  | error message =>
      have unfolded : action { initial with bvars := initial.bvars ++ fresh } =
          .error message := run
      dsimp only [fresh] at unfolded
      rw [unfolded] at success
      simp [throw, throwThe, MonadExceptOf.throw, StateT.lift,
        Except.tryCatch, Functor.map, Except.map] at success
  | ok pair =>
      obtain ⟨result, after⟩ := pair
      have unfolded : action { initial with bvars := initial.bvars ++ fresh } =
          .ok (result, after) := run
      dsimp only [fresh] at unfolded
      rw [unfolded] at success
      have same : result = value := by
        simpa [EarlyReturnT.return, EarlyReturn.runK, throw, throwThe,
          MonadExceptOf.throw, ExceptT.mk, pure, StateT.pure, Except.pure, Except.tryCatch, Except.map] using
          congrArg (Except.map Prod.fst) success
      exact ⟨before, after, by rw [run, same]⟩

private theorem interpProc_body_origin (I : Interpretation)
    (range : SourceRange) (name : String) (types : Option (BooleDDM.TypeArgs SourceRange))
    (inputs : BooleDDM.Bindings SourceRange) (outputs : Option (BooleDDM.MonoDeclList SourceRange))
    (spec : Option (BooleDDM.Spec SourceRange)) (body : Option (BooleDDM.Block SourceRange))
    (initial final : Scope) (procedure : InterpProcedure I.Expression I.Statement)
    (success : interpProc I range name types inputs outputs spec body initial = .ok (procedure, final)) :
    ∃ block entry last meaning, body = some block ∧
      interpBlock I block entry = .ok (meaning, last) ∧ procedure.body = I.block name meaning := by
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
      | (have same : _ = procedure.body := congrArg (fun p => p.1.body) (Except.ok.inj success)
         change I.block name _ = procedure.body at same
         exact ⟨_, _, _, _, rfl, by assumption, same.symm⟩)
      | split at success

private theorem translateProcedureDecl_body_origin (range : SourceRange) (name : String)
    (types : List String) (inputs outputs : ListMap Core.CoreIdent Lambda.LMonoTy)
    (spec : Option (BooleDDM.Spec SourceRange)) (body : BooleDDM.Block SourceRange)
    (entry final : TranslateState) (decls : List Core.Decl)
    (ran : translateProcedureDecl range name types inputs outputs spec (some body) entry = .ok (decls, final))
    (procedure : Core.Procedure) (metadata : Imperative.MetaData Core.Expression)
    (present : .proc procedure metadata ∈ decls) :
    ∃ scope next statements,
      withBVars (inputs.map (·.1.name) ++ outputs.map (·.1.name))
        (toCoreBlock body) scope = .ok (statements, next) ∧
      procedure.body = .structured (if statements.isEmpty then [] else [.block name statements .empty]) := by
  simp only [translateProcedureDecl, getGlobalParamPrefix, bind, StateT.bind, Except.bind,
    pure, StateT.pure, Except.pure, get, getThe, MonadStateOf.get, StateT.get,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at ran
  split at ran
  · contradiction
  split at ran
  · contradiction
  rename_i result bodyRun
  obtain ⟨statements, next⟩ := result
  have equal : _ = decls := congrArg Prod.fst (Except.ok.inj ran)
  rw [← equal] at present
  simp only [List.mem_singleton, Core.Decl.proc.injEq] at present
  rcases present with ⟨rfl, rfl⟩
  exact ⟨_, next, statements, bodyRun, by cases statements <;> rfl⟩

/-- A source expression lowered to the given Core expression in this lexical
context. -/
def ExpressionWasLowered (expression : Boole.Expr) (entry : TranslateState)
    (target : Core.Expression.Expr) : Prop :=
  ∃ final, toCoreExpr expression entry = .ok (target, final)

/-- The legacy expression lowerer has a unique result at a given entry. -/
theorem ExpressionWasLowered.unique {expression : Boole.Expr} {entry : TranslateState}
    {left right : Core.Expression.Expr} (first : ExpressionWasLowered expression entry left)
    (second : ExpressionWasLowered expression entry right) : left = right := by
  obtain ⟨_, ranLeft⟩ := first
  obtain ⟨_, ranRight⟩ := second
  exact congrArg Prod.fst (Except.ok.inj (ranLeft.symm.trans ranRight))

/-- The interpreter and lowerer select the same local binding by index. The
source uses the reversed list and Core indexes the unreversed array from
the end. -/
theorem lowerLocalRead (I : Interpretation) (scope : Scope) (entry : TranslateState)
    (range : SourceRange) (index : Nat) (binding : Binding)
    (encoded : entry.bvars = scope.locals.toArray.map
      (fun b => (.fvar () ⟨b.name, ()⟩ none : Core.Expression.Expr)))
    (found : scope.locals.reverse[index]? = some binding) :
    interpExpr I (.bvar range index) scope = .ok (I.read (.local binding.name), scope) ∧
    ExpressionWasLowered (.bvar range index) entry (.fvar () ⟨binding.name, ()⟩ none) := by
  have bounded : index < scope.locals.length := by
    simpa using (List.getElem?_eq_some_iff.mp found).1
  have atIndex : entry.bvars[entry.bvars.size - index - 1]? =
      some (.fvar () ⟨binding.name, ()⟩ none) := by
    rw [encoded]
    simp only [Array.size_map, List.size_toArray, Array.getElem?_map, List.getElem?_toArray]
    have position : scope.locals.length - index - 1 = scope.locals.length - 1 - index := by omega
    rw [position, ← List.getElem?_reverse bounded, found]
    rfl
  constructor
  · rw [interpExpr.eq_def]
    simp [found, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
      get, getThe, MonadStateOf.get, StateT.get]
  · refine ⟨entry, ?_⟩
    rw [toCoreExpr.eq_def]
    simp only [toCoreQuantExpr?, getBVarExpr, bind, StateT.bind, Except.bind, pure,
      Except.pure, get, getThe, MonadStateOf.get, StateT.get]
    have below : index < entry.bvars.size := by simpa [encoded] using bounded
    simp [below, atIndex, StateT.pure, pure, Except.pure]

/-- A retained global resolves to the same name in both traversals. The
legacy lowerer recognizes it as a variable because the global table contains
that name. -/
theorem lowerGlobalRead (I : Interpretation) (scope : Scope) (entry : TranslateState)
    (range : SourceRange) (index : Nat) (name : String) (binding : Binding)
    (sameNames : scope.names = entry.gctx)
    (resolved : scope.names.nameOf? index = some name)
    (found : scope.globals.find? (fun b => b.name == name) = some binding)
    (registered : entry.globalVarTypes.contains name = true) :
    interpExpr I (.fvar range index) scope = .ok (I.read (.global name), scope) ∧
    ExpressionWasLowered (.fvar range index) entry (.fvar () ⟨name, ()⟩ none) := by
  have bindingName : binding.name = name := by
    exact beq_iff_eq.mp (List.find?_some (p := fun b : Binding => b.name == name) found)
  have targetName := sameNames ▸ resolved
  have classified : getFVarIsOp range index entry = .ok (false, entry) := by
    cases atIndex : entry.gctx.vars[index]? with
    | none => simp [GlobalContext.nameOf?, atIndex] at targetName
    | some item =>
      obtain ⟨key, kind⟩ := item
      have same : key = name := by simpa [GlobalContext.nameOf?, atIndex] using targetName
      subst key
      cases kind <;> simp [getFVarIsOp, TranslateState.isGlobalVar, atIndex, registered,
        bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
        pure, StateT.pure, Except.pure]
  constructor
  · rw [interpExpr.eq_def]
    simp [resolved, findBinding, found, bindingName, bind, StateT.bind, Except.bind,
      pure, StateT.pure, Except.pure, get, getThe, MonadStateOf.get, StateT.get]
  · refine ⟨entry, ?_⟩
    rw [toCoreExpr.eq_def]
    simp [toCoreQuantExpr?, getFVarName, targetName, classified, mkIdent, bind, StateT.bind,
      Except.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure]

/-- The original block lowerer produced this statement list. -/
def BlockWasLowered (block : BooleDDM.Block SourceRange) (statements : List Core.Statement) : Prop :=
  ∃ entry final, toCoreBlock block entry = .ok (statements, final)

/-- Lowering an empty source block emits no Core statements. -/
theorem BlockWasLowered.empty (range annotation : SourceRange) (statements : List Core.Statement)
    (lowered : BlockWasLowered (.block range ⟨annotation, #[]⟩) statements) : statements = [] := by
  obtain ⟨_, _, success⟩ := lowered
  rw [toCoreBlock] at success
  exact congrArg Prod.fst (Except.ok.inj success).symm

/-- The procedure's Boole meaning and raw Core body both come from the same
source block. The procedure name wraps the body on both sides and catches
early exits. The lowerer omits the wrapper when the statement list is empty. -/
theorem lowered_body_origin
    {command : BooleDDM.Command SourceRange} {source : ProcedureMeaning} {raw : Core.Procedure}
    (interpreted : ProcedureWasInterpreted denotation command source)
    (translated : ProcedureWasLowered command raw) :
    ∃ (block : BooleDDM.Block SourceRange) (name : String)
      (entry final : Scope) (body : denotation.Statement) (statements : List Core.Statement),
      interpBlock denotation block entry = .ok (body, final) ∧
      source.body = denotation.block name body ∧
      BlockWasLowered block statements ∧
      raw.body =
        .structured (if statements.isEmpty then [] else [.block name statements .empty]) := by
  have mono := interpretedProcedure_noTypeArguments interpreted
  obtain ⟨entry, final, decls, metadata, ran, present⟩ := translated
  cases shape : command <;> simp only [shape, ProcedureWasInterpreted] at interpreted
  all_goals try contradiction
  all_goals
    simp only [shape, commandTypes?] at mono
    simp only [shape, toCoreDecls, mono] at ran
  case' boole_procedure range name types parameters outputs decreases specification body =>
    obtain ⟨_, outputs⟩ := outputs
    cases outputs
  case' command_procedure range annotations name types parameters specification body =>
    cases modifiers : hasOutOrInoutBinding parameters
    case some bad =>
      obtain ⟨parameter, modifier⟩ := bad
      simp [modifiers, bind, StateT.bind, Except.bind, throwAt, throw, throwThe,
        MonadExceptOf.throw, get, getThe, MonadStateOf.get, StateT.get, StateT.lift,
        pure, Except.pure] at ran
    case' none => simp only [modifiers] at ran
  all_goals
    obtain ⟨_, _, sourceRun⟩ := interpreted
    obtain ⟨block, sourceEntry, sourceFinal, body, declared, sourceBody, sourceMeaning⟩ :=
      interpProc_body_origin _ _ _ _ _ _ _ _ _ _ _ sourceRun
    obtain ⟨_, ran⟩ := withTypeBVars_success ran
    simp only [declared, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
    repeat' (first | contradiction | split at ran)
    obtain ⟨_, _, statements, lowered, coreBody⟩ :=
      translateProcedureDecl_body_origin _ _ _ _ _ _ _ _ _ _ ran _ _ present
    exact ⟨block, _, sourceEntry, sourceFinal, body, statements, sourceBody, sourceMeaning,
      withBVars_success lowered, coreBody⟩

/-- Recover the shared Boole body for a procedure matched by the checker-based proof. -/
theorem MatchedProcedure.lowered_body_origin (matched : MatchedProcedure) :
    ∃ (block : BooleDDM.Block SourceRange) (name : String)
      (entry final : Scope) (body : denotation.Statement) (statements : List Core.Statement),
      interpBlock denotation block entry = .ok (body, final) ∧
      matched.source.body = denotation.block name body ∧
      BlockWasLowered block statements ∧
      matched.loweredProcedure.body =
        .structured (if statements.isEmpty then [] else [.block name statements .empty]) :=
  Strata.Boole.lowered_body_origin matched.interpreted matched.translated

/-- The actual Core procedure checker checks the raw statement list and
installs the statement checker's result as the checked body. -/
theorem checkedProcedure_bodyCheck {program : Core.Program} {raw checked : Core.Procedure}
    (passed : ProcedureWasChecked program raw checked)
    (rawStructured : ∃ before, raw.body = .structured before) :
    ∃ (before after : List Core.Statement) (context : Core.Expression.TyContext) (initial final : Core.Expression.TyEnv),
      raw.body = .structured before ∧ checked.body = .structured after ∧
      Core.Statement.typeCheck context initial program (some raw) before = .ok (after, final) := by
  obtain ⟨context, environment, final, metadata, success⟩ := passed
  obtain ⟨before, bodyEq⟩ := rawStructured
  unfold Core.Procedure.typeCheck at success
  simp only [bind, Except.bind] at success
  rw [bodyEq] at success
  simp only [pure, Except.pure] at success
  repeat' first
    | contradiction
    | (obtain rfl := congrArg Prod.fst (Except.ok.inj success)
       exact ⟨before, _, _, _, _, bodyEq, rfl, by assumption⟩)
    | split at success

/-- The procedure checker leaves an empty body empty. This holds for any
environment produced by the contract checker. -/
theorem checkedProcedure_empty {program : Core.Program} {raw checked : Core.Procedure}
    (passed : ProcedureWasChecked program raw checked) (empty : raw.body = .structured []) :
    checked.body = .structured [] := by
  obtain ⟨before, after, context, initial, final, rawBody, checkedBody, success⟩ :=
    checkedProcedure_bodyCheck passed ⟨[], empty⟩
  rw [empty] at rawBody
  obtain rfl := Imperative.Body.structured.inj rawBody
  have shape : after = [] := by
    unfold Core.Statement.typeCheck at success
    simp only [Core.Statement.typeCheckAux, Core.Statement.typeCheckAux.go, bind, Except.bind,
      Core.Statement.Statement.subst.go, List.reverse_nil] at success
    exact congrArg Prod.fst (Except.ok.inj success).symm
  simpa [shape] using checkedBody

/-- Checking a procedure whose raw body is a single labeled block preserves
its wrapper and exposes the actual checker run on its inner statements. -/
theorem checkedProcedure_singleBlock {program : Core.Program} {raw checked : Core.Procedure}
    (passed : ProcedureWasChecked program raw checked) (name : String)
    (statements : List Core.Statement)
    (shape : raw.body = .structured [.block name statements .empty]) :
    ∃ body context initial final,
      Core.Statement.typeCheck context initial program (some raw) [.block name statements .empty] =
        .ok ([.block name body .empty], final) ∧
      checked.body = .structured [.block name body .empty] := by
  obtain ⟨before, after, context, initial, final, rawBody, checkedBody, ran⟩ :=
    checkedProcedure_bodyCheck passed ⟨_, shape⟩
  have sameBefore := Imperative.Body.structured.inj (rawBody.symm.trans shape)
  subst before
  have bodyCheck := ran
  unfold Core.Statement.typeCheck Core.Statement.typeCheckAux at ran
  simp only [Core.Statement.typeCheckAux.go, List.contains_nil, Bool.false_eq_true,
    ↓reduceIte, bind, Except.bind] at ran
  split at ran
  · contradiction
  · rename_i result succeeded
    split at succeeded
    · contradiction
    · rename_i inner innerChecked
      obtain rfl := Except.ok.inj succeeded
      have same := congrArg Prod.fst (Except.ok.inj ran)
      dsimp only at same
      simp only [Core.Statement.Statement.subst.go, Core.Statement.Statement.subst,
        List.reverse_cons, List.reverse_nil, List.nil_append] at same
      rw [← same] at bodyCheck checkedBody
      exact ⟨_, context, initial, final, bodyCheck, checkedBody⟩

/-- A successful Core procedure check yields a structured body. -/
theorem checkedProcedure_structured {program : Core.Program} {raw checked : Core.Procedure}
    (passed : ProcedureWasChecked program raw checked)
    (rawStructured : ∃ before, raw.body = .structured before) :
    ∃ statements, checked.body = .structured statements := by
  obtain ⟨_, after, _, _, _, _, shape, _⟩ := checkedProcedure_bodyCheck passed rawStructured
  exact ⟨after, shape⟩

end Strata.Boole
