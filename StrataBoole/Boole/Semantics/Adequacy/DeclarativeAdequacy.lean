/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.Observations
import all StrataBoole.Boole.Semantics.Adequacy.Observations
import all StrataBoole.Boole.Semantics.Adequacy.Contracts
public import StrataBoole.Boole.Semantics.Adequacy.ProcedureExecution
import StrataBoole.Boole.Semantics.Adequacy.DeclarativeEntry
import all StrataBoole.Boole.Semantics.Adequacy.Bodies
import all StrataBoole.Boole.Semantics.Adequacy.Statements
import all StrataBoole.Boole.Semantics.Semantics
import all StrataBoole.Boole.Semantics.CoreReference
import all StrataBoole.Boole.Interp
import all StrataBoole.Boole.Runtime
import Strata.DL.Imperative.StmtSemanticsProps
import Strata.Languages.Core.StatementSemanticsProps

public section

namespace Strata.Boole

/-- Agreement for the Core wrapper around a structured procedure. -/
private def ProcedureBodyExecution (program : Core.Program) (globals : List Binding)
    (source : ProcedureMeaning) (statements : List Core.Statement) : Prop :=
  (∀ initial, procedureStateWellTyped globals source initial →
    ∀ outcome, source.body.run initial outcome →
      CoreForwardOutcome program.findProcByString?
        (.stmt (.block "" statements .empty) (coreEnv initial)) outcome) ∧
  CoreReplay program.findProcByString?
    (fun initial => .stmt (.block "" statements .empty) (coreEnv initial)) source.body
    (procedureStateWellTyped globals source) (fun _ => True)

private theorem empty_procedure_execution (program : Core.Program) (globals : List Binding)
    (source : ProcedureMeaning) (name : String) (range annotation : SourceRange)
    (entry final : Scope) (body : Computation (model := .builtins) Unit)
    (sourceRun : interpBlock (denotation .builtins) (.block range ⟨annotation, #[]⟩) entry =
      .ok (body, final))
    (sourceBody : source.body = Computation.block name body) :
    ProcedureBodyExecution program globals source [] := by
  have sourceEmpty (initial : State) (outcome : Outcome Unit) :
      source.body.run initial outcome ↔ outcome = .returned () initial := by
    rw [sourceBody]
    change (Computation.block name body).run initial outcome ↔ _
    constructor
    · rintro ⟨inner, ran, rfl⟩
      obtain rfl := (emptyBlock_run _ _ entry final body initial inner sourceRun).mp ran
      rfl
    · rintro rfl
      exact ⟨.returned () initial, (emptyBlock_run _ _ entry final body initial _ sourceRun).mpr rfl, rfl⟩
  constructor
  · intro initial _ outcome ran
    obtain rfl := (sourceEmpty initial outcome).mp ran
    apply forward_admin .step_block
    have nilRun : CoreForwardOutcome program.findProcByString?
        (.stmts [] (coreEnv initial)) (.returned () initial) :=
      forward_admin .step_stmts_nil ⟨[], .refl _, by simp [coreChecksPass]⟩
    simpa [Outcome.mapState, Store.restrict_self, coreEnv] using
      scope_forward program.findProcByString? (some "") initial [] (.returned () initial)
        nilRun (by simp [Outcome.state, Store.restrict_self, Imperative.projectStore_self])
  · constructor
    · intro initial env trace _ run _
      exact ⟨initial, (sourceEmpty _ _).mpr rfl, (coreEmptyBody_run run).2 _ rfl, trivial⟩
    · intro initial label env trace _ run _
      exact False.elim (Imperative.exitsCoveredByBlocks_noEscapeE _
        (.block "" [] .empty) trivial _ _ _ run)
    · intro initial prior check reached _ run _ _
      have impossible := (coreEmptyBody_run run).1
      simp at impossible

/-- Lift the statement-list agreement through the source scope and both Core
blocks. The two executions discard the same newly introduced locals. -/
private theorem block_procedure_execution
    {program : Core.Program} {globals : List Binding} {source : ProcedureMeaning}
    {target : Core.Procedure} (layout : ProcedureLayout globals source target)
    {name : String} {checked : List Core.Statement}
    {sourceStatements : List (BooleDDM.Statement SourceRange)} {entry final : Scope}
    {inner : Computation (model := .builtins) Unit} {entryValid returnValid : State → Prop}
    (interpreted : interpStmts (denotation .builtins) sourceStatements entry = .ok (inner, final))
    (scopeGlobals : entry.globals = globals)
    (sourceBody : source.body = Computation.block name (Computation.scope inner))
    (closed : (Imperative.Stmt.block name checked .empty : Core.Statement).exitsCoveredByBlocks [])
    (ready : ∀ initial, procedureStateWellTyped globals source initial → entryValid initial)
    (agreement : ExecutionAgreement program.findProcByString? checked inner entryValid returnValid) :
    ProcedureBodyExecution program globals source [.block name checked .empty] := by
  have projection := procedure_scope_projection globals source layout sourceStatements entry final
    inner interpreted scopeGlobals
  have replay : CoreReplay program.findProcByString? (fun initial => .stmts checked (coreEnv initial))
      inner (procedureStateWellTyped globals source) (fun _ => True) := by
    constructor
    · intro initial env trace typed ran passing
      obtain ⟨final, returned, same, _⟩ := agreement.replay.returns _ _ _ (ready initial typed) ran passing
      exact ⟨final, returned, same, trivial⟩
    · intro initial label env trace typed ran passing
      exact agreement.replay.exits _ _ _ _ (ready initial typed) ran passing
    · intro initial prior check reached typed ran passing failed
      exact agreement.replay.fails _ _ _ _ (ready initial typed) ran passing failed
  unfold ProcedureBodyExecution
  rw [sourceBody]
  constructor
  · intro initial typed outcome ran
    obtain ⟨_, ⟨innerOutcome, innerRun, rfl⟩, rfl⟩ := ran
    apply procedureWrapper_forward closed
    apply forward_admin .step_block
    have innerWitness := agreement.forward initial (ready initial typed) innerOutcome innerRun
    have witness := scope_forward _ (some name) initial checked innerOutcome innerWitness
      (projection initial _ typed innerRun)
    cases innerOutcome with
    | exited label state =>
      by_cases same : label = name
      · subst label
        simpa [Outcome.mapState, coreEnv] using witness
      · have different : name ≠ label := Ne.symm same
        simpa [Outcome.mapState, same, different, coreEnv] using witness
    | returned | assertionFailed | stuck => exact witness
  · exact procedureWrapper_replays closed
      (namedBlock_replays name checked inner _ replay projection)

/-- Agreement of wrapped executions implies agreement of the actual procedure
observations, including failure at the first false assertion. -/
private theorem observations_of_body_execution
    {program : Core.Program} {globals : List Binding} {source : ProcedureMeaning}
    {target : Core.Procedure} {command : BooleDDM.Command SourceRange}
    (layout : ProcedureLayout globals source target)
    (interpreted : ProcedureWasInterpreted (denotation .builtins) command source)
    {statements : List Core.Statement} (structured : target.body = .structured statements)
    (execution : ProcedureBodyExecution program globals source statements)
    (initial : State) (typed : procedureStateWellTyped globals source initial)
    (observation : Observation) :
    booleBodyObservations globals source initial observation ↔
      coreBodyObservations program globals target (coreStore initial) observation := by
  constructor
  · exact body_observations_forward _ _ _ _ initial statements structured layout.outputNames
      (execution.1 initial typed) (body_return_slots_of_layout interpreted layout initial typed)
      observation
  · cases observation with
    | returned globalValues outputs =>
      rintro ⟨final, trace, run, passing, globalSlots, outputSlots⟩
      rw [layout.outputNames] at outputSlots
      rw [structured] at run
      cases run with
      | structured traced =>
        obtain ⟨sourceFinal, ran, same, _⟩ := execution.2.returns _ _ _ typed traced passing
        have sameStore := congrArg Imperative.Env.store same
        change _ = coreStore sourceFinal at sameStore
        rw [sameStore] at globalSlots outputSlots
        obtain ⟨globalFrame, localFrame⟩ :=
          interpretedProcedure_return_slotTypes interpreted initial sourceFinal ran
        exact ⟨sourceFinal, ran, return_reads layout initial sourceFinal typed globalFrame localFrame
          globalValues outputs globalSlots outputSlots⟩
    | assertionFailure =>
      rintro ⟨body, priorTrace, check, reached, bodyShape, run, passing, failed⟩
      obtain rfl := Imperative.Body.structured.inj (structured.symm.trans bodyShape)
      exact execution.2.fails _ _ _ _ typed run passing failed

/-- An empty structured body has no expression annotations to change. -/
private theorem annotated_empty_body
    {raw annotated : Core.Procedure}
    (rawBody : raw.body = .structured [])
    (sameBody : (procedureWithoutAnnotations annotated).body =
      (procedureWithoutAnnotations raw).body) :
    annotated.body = .structured [] := by
  cases shape : annotated.body with
  | cfg _ => simp [procedureWithoutAnnotations, shape, rawBody] at sameBody
  | structured statements =>
    cases statements <;>
      simp_all [procedureWithoutAnnotations, eraseStatementsAnnotations]

/-- The interpreter's body scope and the lowering state's name table and
local indices refer to the same declarations. A well-typed interface state
therefore establishes the statement induction's entry invariant. -/
private theorem procedure_block_entry
    {program : Core.Program} {globals : List Binding} {source : ProcedureMeaning}
    {command : BooleDDM.Command SourceRange} {raw target : Core.Procedure}
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    {name : String} {range annotation : SourceRange}
    {sourceStatements : Array (BooleDDM.Statement SourceRange)}
    {rawStatements annotatedStatements : List Core.Statement}
    (layout : ProcedureLayout globals source target)
    (interpreted : ProcedureWasInterpreted (denotation .builtins) command source)
    (translated : ProcedureWasLowered command raw)
    (rawBody : raw.body = .structured [.block name rawStatements .empty])
    (bodyOrigin : BlockWasLowered (.block range ⟨annotation, sourceStatements⟩) rawStatements)
    (targetBody : target.body = .structured [.block name annotatedStatements .empty])
    (typed : Core.TypeSpec.ProcWellTyped program context scopes target) :
    ∃ (entry final : Scope) (inner : Computation (model := .builtins) Unit)
      (before after : TranslateState) (chunks : List (List Core.Statement)),
      interpStmts (denotation .builtins) sourceStatements.toList entry = .ok (inner, final) ∧
      source.body = Computation.block name (Computation.scope inner) ∧
      sourceStatements.toList.mapM lowerStatementChunk before = .ok (chunks, after) ∧
      chunks.flatten = rawStatements ∧
      entry.globals = globals ∧
      ∀ initial, procedureStateWellTyped globals source initial →
        ProcedureExecutionValid globals entry before context (Core.TypeSpec.procBodyScopes scopes target) initial := by
  sorry

/-- The statement cases other than exit must replay the actual Core chunk,
produce its forward execution, and re-establish the invariant on return. -/
private theorem procedure_nonexit_statement_execution
    {sourceProgram : Boole.Program} {names : StrataDDM.GlobalContext}
    {program : Core.Program} {globals : List Binding} {source : ProcedureMeaning}
    {command : BooleDDM.Command SourceRange} {target : Core.Procedure}
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    (fragment : inConcreteCoreFragment sourceProgram names)
    (layout : ProcedureLayout globals source target)
    (interpreted : ProcedureWasInterpreted (denotation .builtins) command source)
    (typed : Core.TypeSpec.ProcWellTyped program context scopes target)
    (name : String) :
    ProcedureStatementExecutionExceptExit program [name] globals := by
  sorry

/-- Lift the inner statement proof to procedure bodies. The empty case is
proved directly. The nonempty case supplies the execution lemma with the
actual two traversals and the declarative typing derivation. -/
private theorem declarative_procedure_execution
    {program : Core.Program} {globals : List Binding} {source : ProcedureMeaning}
    {command : BooleDDM.Command SourceRange} {raw target : Core.Procedure}
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    (layout : ProcedureLayout globals source target)
    (interpreted : ProcedureWasInterpreted (denotation .builtins) command source)
    (translated : ProcedureWasLowered command raw)
    (typed : Core.TypeSpec.ProcWellTyped program context scopes target)
    (sameBody : (procedureWithoutAnnotations target).body = (procedureWithoutAnnotations raw).body)
    (statementExecution : ∀ name, ProcedureStatementExecutionExceptExit program [name] globals) :
    ∃ statements, target.body = .structured statements ∧
      ProcedureBodyExecution program globals source statements := by
  obtain ⟨block, name, entry, final, computation, rawStatements, ran, sourceBody, lowered, rawShape⟩ :=
    lowered_body_origin interpreted translated
  cases block with
  | block range statementsAnn =>
    obtain ⟨annotation, sourceStatements⟩ := statementsAnn
    by_cases empty : sourceStatements = #[]
    · subst sourceStatements
      obtain rfl := BlockWasLowered.empty _ _ _ lowered
      have targetEmpty := annotated_empty_body (by simpa using rawShape) sameBody
      exact ⟨[], targetEmpty,
        empty_procedure_execution program globals source name range annotation entry final computation
          ran sourceBody⟩
    · have nonempty := BlockWasLowered.nonempty _ _ _ _ lowered empty
      have rawWrapped : raw.body = .structured [.block name rawStatements .empty] := by
        simpa [List.isEmpty_eq_false_iff.mpr nonempty] using rawShape
      obtain ⟨range, annotation, sourceStatements, entry, final, inner, annotatedStatements,
        finalContext, finalScopes, lowered, interpretedInner, body, targetBody, erased, typedInner, closed⟩ :=
          declarative_body_alignment interpreted translated typed rawWrapped sameBody
      obtain ⟨alignedEntry, alignedFinal, alignedInner, before, after, chunks,
        interpretedRun, interpretedBody, chunkRun, rfl, scopeGlobals, ready⟩ :=
          procedure_block_entry layout interpreted translated rawWrapped lowered targetBody typed
      have agreement := interpStmts_execution program [name] (ProcedureExecutionValid globals)
        (fun _ _ _ _ _ _ equiv valid => procedureExecutionValid_scopeEquiv equiv valid)
        (procedureStatementExecution program globals [name] (statementExecution name))
        sourceStatements.toList interpretedRun chunkRun erased typedInner
      exact ⟨_, targetBody, block_procedure_execution layout interpretedRun
        scopeGlobals interpretedBody closed ready agreement⟩

/-- The starting context for declaratively typing a lowered Boole program. -/
abbrev booleCoreTypingContext : Core.Expression.TyContext :=
  { Lambda.LContext.default with functions := Core.Factory, knownTypes := Core.KnownTypes }

/-- Boole and Core have the same possible returned values and assertion
failures, and agree on the truth of their contracts. The Core program must
be declaratively well typed, with the same procedure syntax as the raw
lowering once expression annotations are erased. -/
theorem denotation_agrees_with_typed_lowering
    (source : Boole.Program) (names : StrataDDM.GlobalContext)
    (meaning : ProgramMeaning) (raw annotated : Core.Program)
    (fragment : inConcreteCoreFragment source names)
    (denoted : denoteProgram source names = .ok meaning)
    (lowered : toCoreProgram source names = .ok raw)
    (typed : Core.TypeSpec.ProgramWellTyped booleCoreTypingContext [] annotated)
    (preserved : procedureSyntax annotated = procedureSyntax raw) :
    (∀ input, meaning.accepts input →
      meaning.observes input = coreObservations annotated meaning.globals input) ∧
    contractsAgree meaning annotated := by
  apply adequacy_of_procedure_correspondence meaning annotated
  intro procedure member
  obtain ⟨command, before, target, context, interpreted, translated, found,
    procedureTyped, sameHeader, sameBody, sameSpec, rawMember⟩ :=
      declarative_procedure_match denoted lowered typed preserved procedure member
  have layout := declarative_procedure_layout fragment denoted lowered member
    interpreted translated procedureTyped sameHeader rawMember
  obtain ⟨statements, structured, execution⟩ :=
    declarative_procedure_execution layout interpreted translated procedureTyped sameBody
      (procedure_nonexit_statement_execution fragment layout interpreted procedureTyped)
  have clauses := declarative_contract_clauses layout interpreted translated procedureTyped sameSpec
  refine ⟨target, found, {
    entry := entry_agrees_of_layout layout
    body := ?_
    requires := fun _ stateTyped => clauses.1.holds stateTyped
    ensures := fun _ stateTyped => clauses.2.holds stateTyped
  }⟩
  intro input globalsTyped inputsTyped outputs outputsTyped observation
  exact observations_of_body_execution layout interpreted structured execution _
    (initialState_wellTyped_of_layout layout input outputs globalsTyped inputsTyped outputsTyped) observation

end Strata.Boole
