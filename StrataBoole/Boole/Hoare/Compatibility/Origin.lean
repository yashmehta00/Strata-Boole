/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Hoare.Certificate
import all StrataBoole.Boole.Hoare.Compile
import all StrataBoole.Boole.Hoare.Certificate
import all StrataBoole.Boole.Interp
import all StrataBoole.Boole.Runtime
import all Init.Util
import Strata.Util.Tactics
import all StrataBoole.Boole.Semantics.Adequacy.Lowering
import all StrataBoole.Boole.Semantics.Adequacy.SourceInterface
public import StrataBoole.Boole.Semantics.Adequacy.Typing
import all StrataBoole.Boole.Semantics.Adequacy.Typing

public section

namespace Strata.Boole.Hoare

open StrataDDM

theorem prepare_name {source : Boole.Program} {names : GlobalContext} {name : String}
    {prepared : Prepared} (compiled : prepare source names name = .ok prepared) :
    prepared.procedure.name = name := by
  cases ran : compile source names with
  | error error => simp [prepare, ran, bind, Except.bind] at compiled
  | ok program =>
    cases found : program.findProcedure name with
    | none => simp [prepare, ran, found, bind, Except.bind, throw] at compiled
    | some proc =>
      simp [prepare, ran, found, bind, Except.bind, pure, Except.pure] at compiled
      subst prepared
      have selected : program.procedures.find? (fun p => p.name == name) = some proc := found
      exact beq_iff_eq.mp (List.find?_some (p := fun p : Procedure => p.name == name) selected)

set_option linter.unusedSimpArgs false in
private theorem procedure_name
    {range : SourceRange} {name : String} {types : Option (BooleDDM.TypeArgs SourceRange)}
    {inputs : BooleDDM.Bindings SourceRange} {outputs : Option (BooleDDM.MonoDeclList SourceRange)}
    {spec : Option (BooleDDM.Spec SourceRange)} {body : Option (BooleDDM.Block SourceRange)}
    {before after : Scope} {proc : Procedure}
    (ran : procedure range name types inputs outputs spec body before = .ok (proc, after)) :
    proc.name = name := by
  unfold procedure at ran
  obtain ⟨_, ran⟩ := withScope_success ran
  cases types <;> cases outputs <;> cases body
  all_goals
    repeat' first
    | contradiction
    | simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
        Option.isSome, Bool.false_eq_true, ite_false, get, getThe, MonadStateOf.get,
        StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        set, MonadStateOf.set, StateT.set,
        reject, throw, throwThe, MonadExceptOf.throw] at ran
    | (exact (congrArg (fun result : Procedure × Scope => result.1.name) (Except.ok.inj ran)).symm)
    | split at ran

def declarationBody? : BooleDDM.Command SourceRange → Option (BooleDDM.Block SourceRange)
  | .boole_procedure _ _ _ _ _ _ _ body | .command_procedure _ _ _ _ _ _ body => body.val
  | _ => none

private def procedureSpecification : BooleDDM.Command SourceRange → Option (BooleDDM.Spec SourceRange)
  | .boole_procedure _ _ _ _ _ _ spec _ | .command_procedure _ _ _ _ _ spec _ => spec.val
  | _ => none

private def procedureBodyScope (before : Scope) (proc : Procedure) : Scope :=
  { before with
    locals := before.locals ++ proc.inputs ++ proc.outputs
    modifies := proc.contract.modifies
    labels := [proc.name] }

private def CompiledProcedureBodyAt (source : BooleDDM.Block SourceRange)
    (proc : Procedure) (entry : Scope) : Prop :=
  ∃ after compiled,
    block source (proc.inputs.map Binding.name) entry = .ok (compiled, after) ∧
    proc.body = Transformer.block proc.name compiled.command

private theorem CompiledProcedureBodyAt.exists_scope {source proc entry}
    (ran : CompiledProcedureBodyAt source proc entry) : CompiledProcedureBody source proc := by
  exact ⟨entry, ran⟩

set_option linter.unusedSimpArgs false in
private theorem procedure_parts
    {range : SourceRange} {name : String} {types : Option (BooleDDM.TypeArgs SourceRange)}
    {inputs : BooleDDM.Bindings SourceRange} {outputs : Option (BooleDDM.MonoDeclList SourceRange)}
    {spec : Option (BooleDDM.Spec SourceRange)} {body : Option (BooleDDM.Block SourceRange)}
    {before after : Scope} {proc : Procedure}
    (ran : procedure range name types inputs outputs spec body before = .ok (proc, after)) :
    ∃ sourceBody, body = some sourceBody ∧ CompiledProcedureBodyAt sourceBody proc (procedureBodyScope before proc) ∧
      ∃ specEntry specExit, contract spec proc.outputs specEntry = .ok (proc.contract, specExit) := by
  unfold procedure at ran
  obtain ⟨_, ran⟩ := withScope_success ran
  cases types <;> cases outputs <;> cases body
  all_goals
    repeat' first
    | contradiction
    | simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
        Option.isSome, Bool.false_eq_true, ite_false, get, getThe, MonadStateOf.get,
        StateT.get, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        set, MonadStateOf.set, StateT.set,
        reject, throw, throwThe, MonadExceptOf.throw] at ran
    | split at ran
  all_goals
    have eq := congrArg Prod.fst (Except.ok.inj ran)
    dsimp only at eq
    subst proc
    rename_i result extracted _
    refine ⟨_, rfl, ⟨result.2, result.1, by cases result; exact extracted, rfl⟩, ?_⟩
    exact ⟨_, _, by assumption⟩

/-- Recover the source block from a successful Hoare compilation. -/
theorem ProcedureOrigin.body {command : BooleDDM.Command SourceRange} {proc : Procedure}
    (origin : ProcedureOrigin command proc) :
    ∃ block, declarationBody? command = some block ∧ CompiledProcedureBody block proc := by
  cases command <;> simp only [ProcedureOrigin] at origin
  all_goals
    first
    | contradiction
    | obtain ⟨_, _, ran⟩ := origin
      exact (procedure_parts ran).imp (fun _ h => ⟨h.1, h.2.1.exists_scope⟩)

/-- Recover the actual contract compiler invocation from the source procedure. -/
private theorem ProcedureOrigin.specification {command : BooleDDM.Command SourceRange}
    {proc : Procedure} (origin : ProcedureOrigin command proc) :
    ∃ before after, contract (procedureSpecification command) proc.outputs before =
      .ok (proc.contract, after) := by
  cases command <;> simp only [ProcedureOrigin] at origin
  all_goals
    first
    | contradiction
    | obtain ⟨_, _, ran⟩ := origin
      obtain ⟨_, _, _, compiled⟩ := procedure_parts ran
      exact compiled

/-- Open the compiler’s block wrapper, retaining the input scope. -/
private theorem compiledBlock_inner {range ann : SourceRange}
    {statements : Array (BooleDDM.Statement SourceRange)} {proc : Procedure} {entry : Scope}
    (body : CompiledProcedureBodyAt (.block range ⟨ann, statements⟩) proc entry) :
    ∃ final compiled,
      stmts statements.toList (proc.inputs.map Binding.name) entry = .ok (compiled, final) ∧
      proc.body = Transformer.block proc.name (Transformer.scope compiled.command) := by
  obtain ⟨after, outer, ran, shape⟩ := body
  unfold block at ran
  obtain ⟨_, ran⟩ := withScope_success ran
  simp only [get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, Except.bind,
    pure, StateT.pure, Except.pure] at ran
  cases inner : stmts statements.toList (proc.inputs.map Binding.name) entry with
  | error => simp [inner] at ran
  | ok result =>
    obtain ⟨compiled, final⟩ := result
    simp only [inner, Except.ok.injEq, Prod.mk.injEq] at ran
    exact ⟨final, compiled, rfl, by rw [shape, ← ran.1]⟩

private theorem compiledProcedureBody_inner {range ann : SourceRange}
    {statements : Array (BooleDDM.Statement SourceRange)} {proc : Procedure}
    (body : CompiledProcedureBody (.block range ⟨ann, statements⟩) proc) :
    ∃ entry final compiled,
      stmts statements.toList (proc.inputs.map Binding.name) entry = .ok (compiled, final) ∧
      proc.body = Transformer.block proc.name (Transformer.scope compiled.command) := by
  obtain ⟨entry, ran⟩ := body
  exact ⟨entry, compiledBlock_inner ran⟩

/-- The empty AST block compiles to scope and procedure wrappers around skip. -/
theorem compiledProcedureBody_empty {range ann : SourceRange} {proc : Procedure}
    (body : CompiledProcedureBody (.block range ⟨ann, #[]⟩) proc) :
    proc.body = Transformer.block proc.name (Transformer.scope Transformer.skip) := by
  obtain ⟨_, _, compiled, ran, shape⟩ := compiledProcedureBody_inner body
  simp only [stmts, pure, StateT.pure, Except.pure] at ran
  obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj ran)
  exact shape

private theorem withBVars_run {xs : List String} {action : TranslateM α}
    {initial final : TranslateState} {value : α}
    (success : withBVars xs action initial = .ok (value, final)) :
    ∃ after, action { initial with bvars := initial.bvars ++
      (xs.toArray.map (fun n => (.fvar () (mkIdent n) none : Core.Expression.Expr))) } =
        .ok (value, after) ∧ final.bvars = initial.bvars := by
  simp only [withBVars, bind, StateT.bind, Except.bind, pure, Except.pure,
    get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet,
    StateT.modifyGet, tryCatch, tryCatchThe, MonadExceptOf.tryCatch] at success
  let fresh := xs.toArray.map (fun n => (.fvar () (mkIdent n) none : Core.Expression.Expr))
  cases run : action { initial with bvars := initial.bvars ++ fresh } with
  | error message =>
      rw [run] at success
      simp [throw, throwThe, MonadExceptOf.throw, StateT.lift,
        Except.tryCatch, Functor.map, Except.map] at success
  | ok pair =>
      obtain ⟨result, after⟩ := pair
      rw [run] at success
      simp [EarlyReturnT.return, EarlyReturn.runK, throw, throwThe,
        MonadExceptOf.throw, ExceptT.mk, pure, StateT.pure, Except.pure,
        Except.tryCatch] at success
      obtain ⟨rfl, stateEq⟩ := success
      exact ⟨after, rfl, (congrArg TranslateState.bvars stateEq).symm⟩

private theorem translated_procedure_parts
    (range : SourceRange) (name : String) (types : List String)
    (inputs outputs : ListMap Core.CoreIdent Lambda.LMonoTy)
    (spec : Option (BooleDDM.Spec SourceRange)) (body : BooleDDM.Block SourceRange)
    (entry final : TranslateState) (decls : List Core.Decl)
    (ran : translateProcedureDecl range name types inputs outputs spec (some body) entry = .ok (decls, final))
    (proc : Core.Procedure) (metadata : Imperative.MetaData Core.Expression)
    (present : .proc proc metadata ∈ decls) :
    ∃ (statements : Core.Statements) (bodyEntry bodyFinal : TranslateState)
      (formalNames : List String),
      toCoreBlock body bodyEntry = .ok (statements, bodyFinal) ∧
      bodyEntry.bvars = entry.bvars ++ formalNames.toArray.map
        (fun n => (.fvar () (mkIdent n) none : Core.Expression.Expr)) ∧
      proc.body = .structured (if statements.isEmpty then [] else [.block name statements .empty]) ∧
      ∃ specEntry specExit, toCoreSpec range name spec specEntry = .ok (proc.spec, specExit) := by
  simp only [translateProcedureDecl, getGlobalParamPrefix, bind, StateT.bind, Except.bind,
    pure, StateT.pure, Except.pure, get, getThe, MonadStateOf.get, StateT.get,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at ran
  split at ran
  · contradiction
  rename_i contractResult contractRun
  split at ran
  · contradiction
  rename_i bodyResult bodyRun
  obtain ⟨statements, next⟩ := bodyResult
  have equal : _ = decls := congrArg Prod.fst (Except.ok.inj ran)
  rw [← equal] at present
  simp only [List.mem_singleton, Core.Decl.proc.injEq] at present
  rcases present with ⟨rfl, rfl⟩
  obtain ⟨bodyFinal, bodyRun, _⟩ := withBVars_run bodyRun
  let formalNames : List String := inputs.map (·.fst.name) ++ outputs.map (·.fst.name)
  let entryBody := { contractResult.2 with bvars := contractResult.2.bvars ++
    (formalNames.toArray.map (fun n => (.fvar () (mkIdent n) none : Core.Expression.Expr))) }
  obtain ⟨_, _, bvars⟩ := withBVars_run contractRun
  refine ⟨statements, entryBody, bodyFinal, formalNames, ?_, ?_, ?_, withBVars_success contractRun⟩
  · simpa [entryBody, formalNames, List.map_append] using bodyRun
  · simp [entryBody, formalNames, bvars, List.map_append]
  · cases statements <;> rfl

/-- The raw Core body was produced from the same source block as the
predicate transformer. An empty body has no named wrapper in Core. -/
private theorem raw_procedure_parts {command : BooleDDM.Command SourceRange}
    {raw : Core.Procedure} {block : BooleDDM.Block SourceRange}
    (body : declarationBody? command = some block)
    (lowered : ProcedureWasLowered command raw) :
    ∃ (name : String) (statements : Core.Statements)
      (procedureEntry entry bodyFinal : TranslateState) (formalNames : List String),
      toCoreBlock block entry = .ok (statements, bodyFinal) ∧
      entry.bvars = procedureEntry.bvars ++ formalNames.toArray.map
        (fun n => (.fvar () (mkIdent n) none : Core.Expression.Expr)) ∧
      raw.body = .structured (if statements.isEmpty then [] else [.block name statements .empty]) ∧
      ∃ range specEntry specExit, toCoreSpec range name (procedureSpecification command) specEntry =
        .ok (raw.spec, specExit) := by
  obtain ⟨entry, final, decls, metadata, ran, present⟩ := lowered
  cases shape : command <;> simp only [shape, declarationBody?] at body
  all_goals try contradiction
  all_goals
    simp only [shape, toCoreDecls] at ran
  case' boole_procedure range name types inputs outputs decreases specification sourceBody =>
    obtain ⟨_, outputs⟩ := outputs
    cases outputs
  case' command_procedure range annotations name types inputs specification sourceBody =>
    cases modifiers : hasOutOrInoutBinding inputs
    case some bad =>
      obtain ⟨parameter, modifier⟩ := bad
      simp [modifiers, bind, StateT.bind, Except.bind, throwAt, throw, throwThe,
        MonadExceptOf.throw, get, getThe, MonadStateOf.get, StateT.get, StateT.lift,
        pure, Except.pure] at ran
    case' none => simp only [modifiers] at ran
  all_goals
    obtain ⟨_, ran⟩ := withTypeBVars_success ran
    simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
    repeat' (first | contradiction | split at ran)
  all_goals
    rw [body] at ran
    obtain ⟨statements, blockEntry, blockFinal, formals, blockRun, binders,
      coreBody, specEntry, specExit, contractRun⟩ :=
      translated_procedure_parts _ _ _ _ _ _ _ _ _ _ ran raw _ present
    exact ⟨name.val, statements, _, blockEntry, blockFinal, formals, blockRun, binders,
      coreBody, range, specEntry, specExit,
      by simpa only [shape, procedureSpecification] using contractRun⟩

theorem raw_body_origin {command : BooleDDM.Command SourceRange}
    {raw : Core.Procedure} {block : BooleDDM.Block SourceRange}
    (body : declarationBody? command = some block)
    (lowered : ProcedureWasLowered command raw) :
    ∃ name statements, BlockWasLowered block statements ∧
      raw.body = .structured (if statements.isEmpty then [] else [.block name statements .empty]) := by
  obtain ⟨name, statements, _, entry, final, _, ran, _, shaped, _⟩ :=
    raw_procedure_parts body lowered
  exact ⟨name, statements, ⟨entry, final, ran⟩, shaped⟩

private theorem ProcedureOrigin.name {command : BooleDDM.Command SourceRange} {proc : Procedure}
    (origin : ProcedureOrigin command proc) :
    sourceProcedureName? command = some proc.name := by
  cases command <;> simp only [ProcedureOrigin] at origin
  all_goals first
    | contradiction
    | obtain ⟨_, _, ran⟩ := origin
      exact congrArg some (procedure_name ran).symm


private theorem procedure_preserves_scope
    {range : SourceRange} {name : String} {types : Option (BooleDDM.TypeArgs SourceRange)}
    {inputs : BooleDDM.Bindings SourceRange} {outputs : Option (BooleDDM.MonoDeclList SourceRange)}
    {spec : Option (BooleDDM.Spec SourceRange)} {body : Option (BooleDDM.Block SourceRange)}
    {before after : Scope} {proc : Procedure}
    (ran : procedure range name types inputs outputs spec body before = .ok (proc, after)) :
    after = before := by
  unfold procedure withScope at ran
  simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
    get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set, StateT.set] at ran
  split at ran
  · contradiction
  · exact congrArg Prod.snd (Except.ok.inj ran).symm

private def ProcedureRun (command : BooleDDM.Command SourceRange) (proc : Procedure)
    (entry : Scope) : Prop :=
  match command with
  | .boole_procedure range name types inputs outputs _ specs body =>
    ∃ after, procedure range name.val types.val inputs outputs.val specs.val body.val entry =
      .ok (proc, after)
  | .command_procedure range _ name types inputs specs body =>
    ∃ after, procedure range name.val types.val inputs none specs.val body.val entry =
      .ok (proc, after)
  | _ => False

private theorem ProcedureRun.origin {command proc entry} (ran : ProcedureRun command proc entry) :
    ProcedureOrigin command proc := by
  cases command <;> simp only [ProcedureRun, ProcedureOrigin] at ran ⊢
  all_goals first | contradiction | exact ⟨entry, ran⟩

private theorem ProcedureRun.body {command proc entry} (ran : ProcedureRun command proc entry) :
    ∃ body, declarationBody? command = some body ∧
      CompiledProcedureBodyAt body proc (procedureBodyScope entry proc) := by
  cases command <;> simp only [ProcedureRun] at ran
  all_goals
    first
    | contradiction
    | obtain ⟨_, invoked⟩ := ran
      exact (procedure_parts invoked).imp fun _ parts => ⟨parts.1, parts.2.1⟩

private def TopLevelScope (names : GlobalContext) (scope : Scope) : Prop :=
  scope.names = names ∧ scope.locals = [] ∧
    ∀ binding ∈ scope.globals, binding.name.contains ' ' = false

set_option linter.unusedSimpArgs false in
/-- A top-level step either adds a fresh global before any procedure,
or compiles a procedure and restores the entire top-level scope. -/
private theorem declaration_scope
    {command : BooleDDM.Command SourceRange} {existing results : List Procedure}
    {before after : Scope} {names : GlobalContext}
    (ran : declaration existing command before = .ok (results, after))
    (scope : TopLevelScope names before) :
    TopLevelScope names after ∧
      ((existing = [] ∧ results = []) ∨
        (after = before ∧ existing.Sublist results ∧
          ∀ proc ∈ results, proc ∈ existing ∨ ProcedureRun command proc before)) := by
  cases command
  all_goals
    simp only [declaration, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      reject, throw, throwThe, MonadExceptOf.throw] at ran
    try contradiction
  case command_var range binding =>
    cases binding with
    | bind_mk ann name kind ty =>
      split at ran
      · rename_i noProcedures
        simp only [bind, StateT.bind, Except.bind] at ran
        split at ran
        · contradiction
        · rename_i sorted typeRun
          obtain ⟨sort, typedScope⟩ := sorted
          have same := sourceSort_readOnly _ _ _ _ typeRun
          subst typedScope
          simp only [bind, StateT.bind, Except.bind] at ran
          split at ran
          · contradiction
          · rename_i checked freshRun
            obtain ⟨trivialValue, checkedScope⟩ := checked
            cases trivialValue
            obtain ⟨noSpaces, _, restored⟩ := fresh_names freshRun
            subst checkedScope
            simp only [bind, StateT.bind, Except.bind, StateT.modifyGet, StateT.pure, Except.pure] at ran
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj ran)
            have empty : existing = [] := by cases existing <;> simp_all
            refine ⟨⟨scope.1, scope.2.1, ?_⟩, Or.inl ⟨empty, empty⟩⟩
            · intro binding mem
              rcases List.mem_append.mp mem with old | new
              · exact scope.2.2 binding old
              · obtain rfl := List.mem_singleton.mp new
                exact noSpaces
      · simp [bind, StateT.bind, Except.bind, StateT.lift, Function.comp_def, throw, throwThe,
          MonadExceptOf.throw] at ran
  all_goals
    repeat' first
    | contradiction
    | simp only [StateT.bind, Except.bind, StateT.pure, Except.pure,
        StateT.modifyGet, bind, pure] at ran
    | split at ran
  all_goals
    rename_i pair step
    obtain ⟨proc, final⟩ := pair
    have restored := procedure_preserves_scope step
    subst final
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj ran)
    refine ⟨scope, Or.inr ⟨rfl, List.sublist_append_left _ _, ?_⟩⟩
    intro selected member
    rcases List.mem_append.mp member with old | new
    · exact Or.inl old
    · obtain rfl := List.mem_singleton.mp new
      exact Or.inr ⟨_, step⟩

private theorem declarations_scope
    (commands : List (BooleDDM.Command SourceRange))
    {existing results : List Procedure} {before after : Scope} {names : GlobalContext}
    (ran : declarations commands existing before = .ok (results, after))
    (scope : TopLevelScope names before) :
    TopLevelScope names after ∧
      (existing ≠ [] → after = before) ∧
      ∀ proc ∈ results, proc ∈ existing ∨ ∃ command ∈ commands, ProcedureRun command proc after := by
  induction commands generalizing existing before with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj ran)
    exact ⟨scope, fun _ => rfl, fun _ member => Or.inl member⟩
  | cons command rest ih =>
    simp only [declarations, bind, StateT.bind, Except.bind] at ran
    split at ran
    · contradiction
    · rename_i step succeeded
      obtain ⟨next, middle⟩ := step
      obtain ⟨middleScope, action⟩ := declaration_scope succeeded scope
      obtain ⟨endScope, stable, origins⟩ := ih ran middleScope
      refine ⟨endScope, ?_, ?_⟩
      · intro nonempty
        rcases action with ⟨empty, _⟩ | ⟨rfl, kept, _⟩
        · exact False.elim (nonempty empty)
        · apply stable
          intro empty
          change next = [] at empty
          subst next
          exact nonempty (by simpa using kept)
      · intro proc member
        rcases origins proc member with present | ⟨other, included, called⟩
        · rcases action with ⟨_, empty⟩ | ⟨rfl, _, added⟩
          · simp [empty] at present
          · rcases added proc present with old | new
            · exact Or.inl old
            · exact Or.inr ⟨command, List.mem_cons_self,
                stable (List.ne_nil_of_mem present) ▸ new⟩
        · exact Or.inr ⟨other, List.mem_cons_of_mem _ included, called⟩

private theorem compile_scoped_origin {source : Boole.Program} {names : GlobalContext}
    {program : CompiledProgram} {proc : Procedure}
    (ran : compile source names = .ok program) (member : proc ∈ program.procedures) :
    ∃ (command : BooleDDM.Command SourceRange) (scope : Scope),
      (match source with | .prog _ commands => command ∈ commands.val.toList) ∧
      ProcedureRun command proc scope ∧ TopLevelScope names scope ∧ scope.globals = program.globals := by
  cases source with
  | prog range commands =>
    simp only [compile, StateT.run', Functor.map, Except.map, bind, StateT.bind,
      Except.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure,
      Except.pure] at ran
    cases decl : declarations commands.val.toList [] { names := names, supportsType := scalar } with
    | error error => simp [decl] at ran
    | ok result =>
      obtain ⟨procs, scope⟩ := result
      simp only [decl, Except.ok.injEq] at ran
      subst program
      obtain ⟨fits, _, selected⟩ := declarations_scope _ decl ⟨rfl, rfl, by simp⟩
      obtain ⟨command, included, origin⟩ := (selected proc member).resolve_left (by simp)
      exact ⟨command, scope, included, origin, fits, rfl⟩

private theorem prepare_scoped_origin {source : Boole.Program} {names : GlobalContext} {name : String}
    {prepared : Prepared} (compiled : prepare source names name = .ok prepared) :
    ∃ (command : BooleDDM.Command SourceRange) (scope : Scope),
      (match source with | .prog _ commands => command ∈ commands.val.toList) ∧
      ProcedureRun command prepared.procedure scope ∧
      TopLevelScope names scope ∧ scope.globals = prepared.globals := by
  cases ran : compile source names with
  | error error => simp [prepare, ran, bind, Except.bind] at compiled
  | ok program =>
    cases found : program.findProcedure name with
    | none => simp [prepare, ran, found, bind, Except.bind, throw] at compiled
    | some proc =>
      simp [prepare, ran, found, bind, Except.bind, pure, Except.pure] at compiled
      subst prepared
      exact compile_scoped_origin ran (List.mem_of_find?_eq_some found)

theorem compile_origin {source : Boole.Program} {names : GlobalContext}
    {program : CompiledProgram} {proc : Procedure}
    (ran : compile source names = .ok program) (member : proc ∈ program.procedures) :
    ∃ command, (match source with | .prog _ commands => command ∈ commands.val.toList) ∧
      ProcedureOrigin command proc := by
  obtain ⟨command, _, included, invoked, _, _⟩ := compile_scoped_origin ran member
  exact ⟨command, included, invoked.origin⟩

theorem prepare_origin {source : Boole.Program} {names : GlobalContext} {name : String}
    {prepared : Prepared} (compiled : prepare source names name = .ok prepared) :
    ∃ command, (match source with | .prog _ commands => command ∈ commands.val.toList) ∧
      ProcedureOrigin command prepared.procedure := by
  obtain ⟨command, _, included, invoked, _, _⟩ := prepare_scoped_origin compiled
  exact ⟨command, included, invoked.origin⟩

private theorem annotated_lowering {source : Boole.Program} {names : GlobalContext} {name : String}
    {command : BooleDDM.Command SourceRange} {raw checked : Core.Program} {target : Core.Procedure}
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    (present : match source with | .prog _ commands => command ∈ commands.val.toList)
    (named : sourceProcedureName? command = some name)
    (lowered : toCoreProgram source names = .ok raw)
    (typed : Core.TypeSpec.ProgramWellTyped context scopes checked)
    (preserved : procedureSyntax checked = procedureSyntax raw)
    (lookup : checked.findProcByString? name = some target) :
    ∃ (before : Core.Procedure) (md : Imperative.MetaData Core.Expression),
      Core.Decl.proc before md ∈ raw.decls ∧ ProcedureWasLowered command before ∧
      procedureWithoutAnnotations target = procedureWithoutAnnotations before := by
  obtain ⟨before, md, member, sameName, declared⟩ :=
    toCoreProgram_lowered_procedure source names raw command name present named lowered
  have rawMember : before ∈ raw.decls.filterMap Core.Decl.getProc? :=
    List.mem_filterMap.mpr ⟨_, member, rfl⟩
  have annotated : procedureWithoutAnnotations before ∈ procedureSyntax checked := by
    rw [preserved]
    exact List.mem_map_of_mem rawMember
  obtain ⟨result, resultMember, same⟩ := List.mem_map.mp annotated
  have resultName : result.header.name.name = name := by
    have eq := congrArg (fun proc : Core.Procedure => proc.header.name.name) same
    exact eq.trans sameName
  have distinct : ((checked.decls.filterMap Core.Decl.getProc?).map (·.header.name)).Nodup := by
    cases checked
    rw [procedureNames_eq]
    exact typed.1 .proc
  have found : checked.findProcByString? name = some result := by
    rw [← resultName]
    cases checked
    rw [findProc_eq_find]
    exact find_unique_procedure _ _ resultMember distinct
  obtain rfl := Option.some.inj (found.symm.trans lookup)
  exact ⟨before, md, member, declared, same⟩

/-- Match the compiler's source declaration to the annotated Core declaration
using the raw lowering and Strata's declaration and annotation specifications. -/
theorem annotated_origin {source : Boole.Program} {names : GlobalContext} {name : String}
    {prepared : Prepared} {raw checked : Core.Program} {target : Core.Procedure}
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    (compiled : prepare source names name = .ok prepared)
    (lowered : toCoreProgram source names = .ok raw)
    (typed : Core.TypeSpec.ProgramWellTyped context scopes checked)
    (preserved : procedureSyntax checked = procedureSyntax raw)
    (lookup : checked.findProcByString? name = some target) :
    ∃ (command : BooleDDM.Command SourceRange) (before : Core.Procedure)
      (md : Imperative.MetaData Core.Expression),
      (match source with | .prog _ commands => command ∈ commands.val.toList) ∧
      Core.Decl.proc before md ∈ raw.decls ∧
      ProcedureOrigin command prepared.procedure ∧ ProcedureWasLowered command before ∧
      procedureWithoutAnnotations target = procedureWithoutAnnotations before := by
  obtain ⟨command, present, origin⟩ := prepare_origin compiled
  have named := ProcedureOrigin.name origin |>.trans (congrArg some (prepare_name compiled))
  obtain ⟨before, md, member, declared, same⟩ :=
    annotated_lowering present named lowered typed preserved lookup
  exact ⟨command, before, md, present, member, origin, declared, same⟩

def integerGlobal (command : BooleDDM.Command SourceRange) : Option Binding :=
  match command with
  | .command_var _ (.bind_mk _ name _ (.int _)) => some ⟨name.val, .int⟩
  | _ => none

def isIntegerGlobal (command : BooleDDM.Command SourceRange) : Bool :=
  match command with
  | .command_var _ (.bind_mk _ _ _ ty) => match ty with
    | .int _ => true
    | _ => false
  | _ => true

set_option linter.unusedSimpArgs false in
private theorem declaration_integer_globals
    {before after : Scope} {command : BooleDDM.Command SourceRange}
    {procedures result : List Procedure}
    (decl : declaration procedures command before = .ok (result, after))
    (integer : isIntegerGlobal command = true) :
    after.globals = before.globals ++ (integerGlobal command).toList := by
  cases command
  all_goals
    simp only [declaration, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
      modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      reject, throw, throwThe, MonadExceptOf.throw] at decl
    try contradiction
  case command_var range binding =>
    cases binding with
    | bind_mk ann name kind ty =>
      cases ty <;> simp [isIntegerGlobal] at integer
      unfold sourceSort at decl
      simp only [integerGlobal, Option.toList_some, StateT.bind, Except.bind, pure, StateT.pure,
        Except.pure, get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet,
        MonadStateOf.modifyGet, StateT.modifyGet, fresh] at decl ⊢
      repeat' first
        | contradiction
        | simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
            get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet,
            MonadStateOf.modifyGet, StateT.modifyGet, reject, throw, throwThe,
            MonadExceptOf.throw] at decl
        | split at decl
      rename_i sortResult sortRan _ freshResult freshRan
      have sortEq : sortResult = (.int, before) := by
        split at sortRan
        · simp [StateT.lift, StateT.bind, bind, Except.bind, throw, throwThe,
            MonadExceptOf.throw, Function.comp_def] at sortRan
        · exact (Except.ok.inj sortRan).symm
      subst sortResult
      have freshEq : freshResult = ((), before) := by
        repeat' first
        | contradiction
        | simp only [StateT.lift, StateT.bind, bind, Except.bind, throw, throwThe,
            MonadExceptOf.throw, Function.comp_def, StateT.pure, pure, Except.pure] at freshRan
        | split at freshRan
        exact (Except.ok.inj freshRan).symm
      subst freshResult
      exact congrArg (fun p : List Procedure × Scope => p.2.globals) (Except.ok.inj decl).symm
  all_goals
    simp only [integerGlobal, Option.toList_none, List.append_nil]
    repeat' first
    | contradiction
    | simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at decl
    | split at decl
    rename_i pair called
    obtain ⟨proc, next⟩ := pair
    have same := procedure_preserves_scope called
    exact (congrArg (fun p : List Procedure × Scope => p.2.globals) (Except.ok.inj decl).symm).trans
      (congrArg Scope.globals same)

private theorem declarations_integer_globals
    {before after : Scope} {commands : List (BooleDDM.Command SourceRange)}
    {procedures result : List Procedure}
    (decl : declarations commands procedures before = .ok (result, after))
    (integer : ∀ command ∈ commands, isIntegerGlobal command = true) :
    after.globals = before.globals ++ commands.filterMap integerGlobal := by
  induction commands generalizing procedures before with
  | nil =>
    have same : after = before := congrArg Prod.snd (Except.ok.inj decl).symm
    simp [same]
  | cons command rest ih =>
    simp only [declarations, bind, StateT.bind, Except.bind] at decl
    split at decl
    · contradiction
    · rename_i step succeeded
      have head := declaration_integer_globals succeeded (integer command List.mem_cons_self)
      have tail := ih decl (fun cmd mem => integer cmd (List.mem_cons_of_mem _ mem))
      rw [tail, head, List.append_assoc, List.filterMap_cons]
      cases integerGlobal command <;> rfl

/-- Every global represented by the transformer is a declared integer global
in the compatibility fragment, in declaration order. -/
theorem prepare_integer_globals
    {range : SourceRange} {commands : Ann (Array (BooleDDM.Command SourceRange)) SourceRange}
    {names : GlobalContext} {name : String} {prepared : Prepared}
    (ran : prepare (.prog range commands) names name = .ok prepared)
    (integer : commands.val.toList.all isIntegerGlobal = true) :
    prepared.globals = commands.val.toList.filterMap integerGlobal := by
  cases compiled : compile (.prog range commands) names with
  | error error => simp [prepare, compiled, bind, Except.bind] at ran
  | ok program =>
    cases found : program.findProcedure name with
    | none => simp [prepare, compiled, found, bind, Except.bind, throw] at ran
    | some proc =>
      simp [prepare, compiled, found, bind, Except.bind, pure, Except.pure] at ran
      subst prepared
      simp only [compile, StateT.run', Functor.map, Except.map, bind, StateT.bind,
        Except.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure,
        Except.pure] at compiled
      cases decl : declarations commands.val.toList [] { names := names, supportsType := scalar } with
      | error error => simp [decl] at compiled
      | ok result =>
        obtain ⟨procs, scope⟩ := result
        simp only [decl, Except.ok.injEq] at compiled
        subst program
        exact declarations_integer_globals decl (List.all_eq_true.mp integer)

end Strata.Boole.Hoare
