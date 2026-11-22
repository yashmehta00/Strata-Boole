/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.Execution
public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.DeclarativeBodies
public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.ExecutionInvariant
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Execution
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.DeclarativeBodies
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Lowering
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.ExitExecution

public section

namespace Strata.Boole

/-- Static alignment and runtime slot typing needed while relating one
procedure body to its lowered Core statement list. The Core variable scope
must name exactly the source locals, its global table must have exactly the
source global names, and its saved in-out names must match the source
modifies set. The fixed runtime factory is part of `ScalarStoreTyped`. -/
def ProcedureExecutionValid (globals : List Binding) (scope : Scope)
    (before : TranslateState) (_context : Core.Expression.TyContext)
    (scopes : Core.TypeSpec.TypeScopes) (state : State) : Prop :=
  ExecutionStateTyped scope scopes state ∧
  scope.globals = globals ∧
  scope.names = before.gctx ∧
  ((scope.globals ++ scope.locals).map Binding.name).Nodup ∧
  (∀ binding ∈ scope.globals ++ scope.locals, binding.name.contains ' ' = false) ∧
  (∀ name, name ∈ before.currentInoutNames ↔ name ∈ scope.modifies) ∧
  before.bvars = scope.locals.toArray.map
    (fun binding => (.fvar () ⟨binding.name, ()⟩ none : Core.Expression.Expr)) ∧
  (∀ name, before.globalVarTypes.contains name = true ↔ name ∈ scope.globals.map Binding.name)

/-- Changing only the declarative type-scope map preserves this invariant.
This is the compatibility fact needed when list typing inserts scopes for
statements inside the body. -/
theorem procedureExecutionValid_scopeEquiv
    {globals : List Binding} {scope : Scope} {before : TranslateState}
    {context : Core.Expression.TyContext} {scopes other : Core.TypeSpec.TypeScopes}
    {state : State}
    (equiv : Strata.Util.HMaps.Equiv other scopes)
    (valid : ProcedureExecutionValid globals scope before context scopes state) :
    ProcedureExecutionValid globals scope before context other state := by
  obtain ⟨runtime, globalsEq, namesEq, distinct, noSpaces, inoutsEq,
    bvarsEq, registered⟩ := valid
  exact ⟨⟨runtime.locals, runtime.globals, runtime.snapshots,
      scalarStoreTyped_scopeEquiv equiv runtime.core⟩,
    globalsEq, namesEq, distinct, noSpaces, inoutsEq, bvarsEq, registered⟩

/-- The initial Boole state satisfies the runtime part of the body invariant
when Core's declarative scopes accept its scalar slots. The remaining fields
are explicit equalities recovered from procedure interpretation and
lowering. -/
theorem procedureInitialExecutionValid
    {globals : List Binding} {source : ProcedureMeaning} {scope : Scope}
    {before : TranslateState} {context : Core.Expression.TyContext}
    {scopes : Core.TypeSpec.TypeScopes}
    (input : Invocation) (outputs : List Value)
    (scopeGlobals : scope.globals = globals)
    (scopeLocals : scope.locals = source.inputs ++ source.outputs)
    (scopeModifies : scope.modifies = source.contract.modifies)
    (scopeNames : scope.names = before.gctx)
    (scopeDistinct : (scope.globals ++ scope.locals).map Binding.name |>.Nodup)
    (scopeNoSpaces : ∀ binding ∈ scope.globals ++ scope.locals,
      binding.name.contains ' ' = false)
    (inoutsAgree : ∀ name, name ∈ before.currentInoutNames ↔ name ∈ scope.modifies)
    (bvars : before.bvars = scope.locals.toArray.map
      (fun binding => (.fvar () ⟨binding.name, ()⟩ none : Core.Expression.Expr)))
    (registered : ∀ name, before.globalVarTypes.contains name = true ↔
      name ∈ scope.globals.map Binding.name)
    (globalsTyped : valuesMatch globals input.globals = true)
    (inputsTyped : valuesMatch source.inputs input.arguments = true)
    (outputsTyped : valuesMatch source.outputs outputs = true)
    (coreTyped : ScalarStoreTyped scopes (initialState globals source input outputs)) :
    ProcedureExecutionValid globals scope before context scopes
      (initialState globals source input outputs) := by
  exact ⟨initialState_executionStateTyped input outputs scopeGlobals scopeLocals
    scopeModifies globalsTyped inputsTyped outputsTyped coreTyped,
    scopeGlobals, scopeNames, scopeDistinct, scopeNoSpaces, inoutsAgree,
    bvars, registered⟩

/-- Per-statement execution agreement for every body statement except a
direct exit. This isolates the remaining expression, assignment, branch,
loop, declaration, assumption, assertion, and havoc cases at the exact
source/lowering/typing boundary used by the body induction. -/
def ProcedureStatementExecutionExceptExit (program : Core.Program)
    (labels : List String) (globals : List Binding) : Prop :=
  ∀ (source : BooleDDM.Statement SourceRange)
    (entry final : Scope) (before after : TranslateState)
    (context next : Core.Expression.TyContext)
    (scopes nextScopes : Core.TypeSpec.TypeScopes)
    (body : Computation Unit)
    (raw annotated : List Core.Statement),
    (∀ range metadata name,
      source ≠ .exit_statement range metadata name) →
    interpStmt denotation source entry = .ok (body, final) →
    lowerStatementChunk source before = .ok (raw, after) →
    eraseStatementsAnnotations annotated = eraseStatementsAnnotations raw →
    Core.TypeSpec.StatementsWellTyped program context scopes labels annotated next nextScopes →
    ExecutionAgreement program.findProcByString? annotated body
      (ProcedureExecutionValid globals entry before context scopes)
      (ProcedureExecutionValid globals final after next nextScopes)

/-- The exit case is already proved from the actual interpreter and lowerer.
This assembles it with the remaining per-statement obligations under the
same explicit runtime and source/Core alignment invariant. -/
theorem procedureStatementExecution
    (program : Core.Program) (globals : List Binding)
    (labels : List String)
    (otherStatements : ProcedureStatementExecutionExceptExit program labels globals) :
    StatementExecution program labels (ProcedureExecutionValid globals) := by
  intro source entry final before after context next scopes nextScopes body raw annotated
    interpreted lowered erased typed
  by_cases isExit : ∃ range metadata name,
      source = .exit_statement range metadata name
  · obtain ⟨range, metadata, name, rfl⟩ := isExit
    exact interpExit_execution program labels (ProcedureExecutionValid globals)
      range metadata name interpreted lowered erased typed
  · apply otherStatements source entry final before after context next scopes nextScopes
      body raw annotated
    · intro range metadata name same
      exact isExit ⟨range, metadata, name, same⟩
    · exact interpreted
    · exact lowered
    · exact erased
    · exact typed


end Strata.Boole
