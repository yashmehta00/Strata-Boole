/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.Lowering
public import Strata.Languages.Core.Typing.Spec.TypingSpec
public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.StatementAnnotations
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Lowering
import all Strata.Languages.Core.Program
import all Strata.Languages.Core.Procedure
import all Strata.Languages.Core.Statement
import Strata.Util.ListMapProps
import all Strata.Util.ListMap

public section

namespace Strata.Boole

/-- A procedure in a declaratively well-typed program is typed in the
context at its declaration. The context can differ from the program's
starting context because earlier declarations may introduce types. -/
theorem wellTypedProcedure_of_find
    {program : Core.Program} {context : Core.Expression.TyContext}
    {scopes : Core.TypeSpec.TypeScopes} {name : String} {procedure : Core.Procedure}
    (typed : Core.TypeSpec.ProgramWellTyped context scopes program)
    (found : program.findProcByString? name = some procedure) :
    ∃ localContext, Core.TypeSpec.ProcWellTyped program localContext scopes procedure := by
  obtain ⟨_, finalContext, declarations⟩ := typed
  have member : procedure ∈ program.decls.filterMap Core.Decl.getProc? := by
    cases program
    rw [findProc_eq_find] at found
    exact List.mem_of_find?_eq_some found
  obtain ⟨decl, present, isProcedure⟩ := List.mem_filterMap.mp member
  clear member found
  generalize program.decls = decls at declarations present
  induction declarations with
  | nil => simp at present
  | cons _ _ _ _ first rest firstTyped _ ih =>
    rcases List.mem_cons.mp present with rfl | later
    · cases firstTyped <;> try contradiction
      case proc =>
        obtain rfl := Option.some.inj isProcedure
        exact ⟨_, by assumption⟩
    · exact ih later

/-- The procedures of a Core program, retaining headers and clauses while
erasing expression annotations from their bodies and specifications. -/
def procedureSyntax (program : Core.Program) : List Core.Procedure :=
  (program.decls.filterMap Core.Decl.getProc?).map procedureWithoutAnnotations

private theorem procedureNames_eq (declarations : List Core.Decl) :
    ((declarations.filterMap Core.Decl.getProc?).map (·.header.name)) =
      Core.TypeSpec.programNamesOfKind { decls := declarations } .proc := by
  induction declarations with
  | nil => rfl
  | cons declaration rest ih =>
    unfold Core.TypeSpec.programNamesOfKind at ih ⊢
    cases declaration <;>
      simp only [List.filterMap_cons, Core.Decl.getProc?, List.filter_cons,
        Core.TypeSpec.declNameKind, Core.Decl.kind] <;>
      simp [Core.Decl.names, Core.Decl.name, ih, beq_iff_eq, Core.TypeSpec.declNameKind, Core.Decl.kind]

/-- Match an interpreted Boole declaration with its raw and annotated Core
procedures. Declarative typing gives distinct procedure names and supplies
the typing context at the matched declaration. -/
theorem declarative_procedure_match
    {source : Boole.Program} {names : StrataDDM.GlobalContext}
    {meaning : ProgramMeaning} {raw annotated : Core.Program}
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    (denoted : denoteProgram source names = .ok meaning)
    (lowered : toCoreProgram source names = .ok raw)
    (typed : Core.TypeSpec.ProgramWellTyped context scopes annotated)
    (preserved : procedureSyntax annotated = procedureSyntax raw)
    (procedure : ProcedureMeaning) (member : procedure ∈ meaning.procedures) :
    ∃ command before after localContext,
      ProcedureWasInterpreted denotation command procedure ∧
      ProcedureWasLowered command before ∧
      annotated.findProcByString? procedure.name = some after ∧
      Core.TypeSpec.ProcWellTyped annotated localContext scopes after ∧
      after.header = before.header ∧
      (procedureWithoutAnnotations after).body = (procedureWithoutAnnotations before).body ∧
      Core.Procedure.Spec.eraseTypes after.spec = Core.Procedure.Spec.eraseTypes before.spec ∧
      ∃ metadata, Core.Decl.proc before metadata ∈ raw.decls := by
  obtain ⟨command, before, metadata, interpreted, translated, inRaw, named⟩ :=
    lowered_procedure_origin source names meaning raw denoted lowered procedure member
  have beforePresent : before ∈ raw.decls.filterMap Core.Decl.getProc? :=
    List.mem_filterMap.mpr ⟨_, inRaw, rfl⟩
  have present : procedureWithoutAnnotations before ∈ procedureSyntax annotated := by
    rw [preserved]
    exact List.mem_map_of_mem beforePresent
  obtain ⟨after, afterPresent, same⟩ := List.mem_map.mp present
  have header : after.header = before.header := by
    have equal := congrArg (fun p : Core.Procedure => p.header) same
    simpa [procedureWithoutAnnotations] using equal
  have afterNamed : after.header.name.name = procedure.name := by rw [header, named]
  have distinct : ((annotated.decls.filterMap Core.Decl.getProc?).map (·.header.name)).Nodup := by
    cases annotated
    rw [procedureNames_eq]
    exact typed.1 .proc
  have found : annotated.findProcByString? procedure.name = some after := by
    rw [← afterNamed]
    cases annotated
    rw [findProc_eq_find]
    exact find_unique_procedure _ _ afterPresent distinct
  obtain ⟨localContext, procedureTyped⟩ := wellTypedProcedure_of_find typed found
  have body := congrArg (fun p : Core.Procedure => p.body) same
  have spec := congrArg (fun p : Core.Procedure => p.spec) same
  exact ⟨command, before, after, localContext, interpreted, translated, found, procedureTyped,
    header, body, spec, metadata, inRaw⟩

/-- Invert the typing derivation of a structured procedure. The starting
scopes contain its inputs, outputs, and old snapshots. -/
theorem typed_structured_body
    {program : Core.Program} {context : Core.Expression.TyContext}
    {scopes : Core.TypeSpec.TypeScopes} {procedure : Core.Procedure}
    {statements : List Core.Statement}
    (typed : Core.TypeSpec.ProcWellTyped program context scopes procedure)
    (body : procedure.body = .structured statements) :
    ∃ finalContext finalScopes,
      Core.TypeSpec.StatementsWellTyped program context
        (Core.TypeSpec.procBodyScopes scopes procedure) [] statements finalContext finalScopes := by
  have bodyTyped := typed.bodyTyped
  rw [body] at bodyTyped
  cases bodyTyped with
  | structured _ _ _ derivation => exact ⟨_, _, derivation⟩

/-- Invert a procedure's typing derivation at the named block introduced by
the Boole lowerer. The inner statements are typed with that label in scope. -/
theorem typed_procedure_block
    {program : Core.Program} {context : Core.Expression.TyContext}
    {scopes : Core.TypeSpec.TypeScopes} {procedure : Core.Procedure}
    {label : String} {statements : List Core.Statement}
    (typed : Core.TypeSpec.ProcWellTyped program context scopes procedure)
    (body : procedure.body = .structured [.block label statements .empty]) :
    ∃ finalContext finalScopes,
      Core.TypeSpec.StatementsWellTyped program context
        (Core.TypeSpec.procBodyScopes scopes procedure) [label] statements finalContext finalScopes := by
  obtain ⟨_, _, derivation⟩ := typed_structured_body typed body
  cases derivation with
  | cons _ _ _ _ _ _ _ _ _ first _ =>
    cases first with
    | block _ _ _ _ _ _ _ _ _ _ inner _ => exact ⟨_, _, inner⟩

/-- The annotated body has the same named block as lowering, and its inner
statements have the same syntax after erasing expression annotations. -/
theorem typed_lowered_block
    {program : Core.Program} {context : Core.Expression.TyContext}
    {scopes : Core.TypeSpec.TypeScopes} {raw procedure : Core.Procedure}
    {label : String} {statements : List Core.Statement}
    (typed : Core.TypeSpec.ProcWellTyped program context scopes procedure)
    (rawBody : raw.body = .structured [.block label statements .empty])
    (sameBody : (procedureWithoutAnnotations procedure).body = (procedureWithoutAnnotations raw).body) :
    ∃ annotated finalContext finalScopes,
      procedure.body = .structured [.block label annotated .empty] ∧
      eraseStatementsAnnotations annotated = eraseStatementsAnnotations statements ∧
      Core.TypeSpec.StatementsWellTyped program context
        (Core.TypeSpec.procBodyScopes scopes procedure) [label] annotated finalContext finalScopes := by
  cases body : procedure.body with
  | cfg cfg =>
    simp [procedureWithoutAnnotations, body, rawBody] at sameBody
  | structured bodyStatements =>
    have same : eraseStatementsAnnotations bodyStatements =
        [eraseStatementAnnotations (.block label statements .empty)] := by
      simpa [procedureWithoutAnnotations, body, rawBody, eraseStatementsAnnotations] using sameBody
    rcases bodyStatements with _ | ⟨first, rest⟩
    · simp [eraseStatementsAnnotations] at same
    have empty : rest = [] := by
      have tail := (List.cons.inj same).2
      cases rest <;> simp_all [eraseStatementsAnnotations]
    subst rest
    have firstErased : eraseStatementAnnotations first =
        eraseStatementAnnotations (.block label statements .empty) := (List.cons.inj same).1
    cases first <;> simp [eraseStatementAnnotations] at firstErased
    case block blockLabel inner metadata =>
      obtain ⟨rfl, sameInner, rfl⟩ := firstErased
      obtain ⟨finalContext, finalScopes, derivation⟩ := typed_procedure_block typed body
      exact ⟨inner, finalContext, finalScopes, rfl, sameInner, derivation⟩

/-- A clause at a given position in the raw contract has a Boolean-typed
counterpart at that position in the annotated contract. Erasing its
expression annotations preserves the check, including its label and attributes.
Use the procedure's input scopes for requires and body scopes for ensures. -/
theorem typed_clause_at
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    {raw annotated : ListMap String Core.Procedure.Check} {i : Nat}
    {label : String} {check : Core.Procedure.Check}
    (typed : ∀ c ∈ annotated.values, Core.TypeSpec.ExprWellTyped context scopes c.expr .bool)
    (same : annotated.toList.map (fun (name, c) => (name, Core.Procedure.Check.eraseTypes c)) =
      raw.toList.map (fun (name, c) => (name, Core.Procedure.Check.eraseTypes c)))
    (found : raw.toList[i]? = some (label, check)) :
    ∃ resolved, annotated.toList[i]? = some (label, resolved) ∧
      Core.Procedure.Check.eraseTypes resolved = Core.Procedure.Check.eraseTypes check ∧
      Core.TypeSpec.ExprWellTyped context scopes resolved.expr .bool := by
  have atIndex := congrArg (fun clauses : List (String × Core.Procedure.Check) => clauses[i]?) same
  rw [List.getElem?_map, List.getElem?_map, found] at atIndex
  cases resolvedAt : annotated.toList[i]? with
  | none => simp [resolvedAt] at atIndex
  | some entry =>
    obtain ⟨name, resolved⟩ := entry
    have ⟨nameEq, erased⟩ : name = label ∧
        Core.Procedure.Check.eraseTypes resolved = Core.Procedure.Check.eraseTypes check := by
      simpa [resolvedAt] using atIndex
    subst name
    refine ⟨resolved, rfl, erased, typed _ ?_⟩
    rw [ListMap.values_eq_map_snd]
    exact List.mem_map.mpr ⟨(label, resolved), List.mem_of_getElem? resolvedAt, rfl⟩

end Strata.Boole
