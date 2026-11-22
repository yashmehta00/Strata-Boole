/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.Typing
public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.Entry
public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.SourceInterface
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Lowering
import all Strata.Languages.Core.Typing.Spec.TypingSpec
import all Strata.Languages.Core.Procedure

public section

namespace Strata.Boole

/-- The lowerer's input header encodes the source globals and procedure
inputs in an order Core accepts. This is the source-to-header fact needed
to establish that the source and Core procedure entries have the same slots.

This provisional leaf isolates encoding the Boole bindings and the legacy
global table in the Core lowerer. It is independent of Core's typechecker. -/
private theorem lowered_inputs_match_source
    {sourceProgram : Boole.Program} {names : StrataDDM.GlobalContext} {meaning : ProgramMeaning}
    {raw : Core.Program} {command : BooleDDM.Command SourceRange} {procedure : ProcedureMeaning}
    {rawProcedure : Core.Procedure}
    (fragment : inConcreteCoreFragment sourceProgram names)
    (denoted : denoteProgram sourceProgram names = .ok meaning)
    (lowered : toCoreProgram sourceProgram names = .ok raw)
    (member : procedure ∈ meaning.procedures)
    (interpreted : ProcedureWasInterpreted denotation command procedure)
    (translated : ProcedureWasLowered command rawProcedure)
    (rawMember : ∃ metadata, Core.Decl.proc rawProcedure metadata ∈ raw.decls) :
    ∃ orderedGlobals, orderedGlobals.Perm meaning.globals ∧
      (orderedGlobals ++ procedure.inputs).mapM scalarFormal? =
        some rawProcedure.header.inputs.toList := by
  sorry

/-- The lowerer's output header encodes precisely the modified globals and
declared outputs. This is the source-to-header fact needed to establish that
the source and Core procedure entries agree on their output slots.

This provisional leaf isolates the same global-table and scalar-formal
encoding used by lowering. It is independent of Core's typechecker. -/
private theorem lowered_outputs_match_source
    {sourceProgram : Boole.Program} {names : StrataDDM.GlobalContext} {meaning : ProgramMeaning}
    {raw : Core.Program} {command : BooleDDM.Command SourceRange} {procedure : ProcedureMeaning}
    {rawProcedure : Core.Procedure}
    (fragment : inConcreteCoreFragment sourceProgram names)
    (denoted : denoteProgram sourceProgram names = .ok meaning)
    (lowered : toCoreProgram sourceProgram names = .ok raw)
    (member : procedure ∈ meaning.procedures)
    (interpreted : ProcedureWasInterpreted denotation command procedure)
    (translated : ProcedureWasLowered command rawProcedure)
    (outputsNodup : rawProcedure.header.outputs.keys.Nodup)
    (rawMember : ∃ metadata, Core.Decl.proc rawProcedure metadata ∈ raw.decls) :
    ∃ modifiedGlobals, (∀ binding ∈ modifiedGlobals, binding ∈ meaning.globals) ∧
      (modifiedGlobals.map Binding.name).Perm procedure.contract.modifies ∧
      (modifiedGlobals ++ procedure.outputs).mapM scalarFormal? =
        some rawProcedure.header.outputs.toList := by
  sorry

/-- If a declaratively typed procedure has the same header as its source
lowering, that header represents the interpreted Boole interface. The proof
uses declarative output-name distinctness and source-level freshness. -/
theorem declarative_procedure_layout
    {sourceProgram : Boole.Program} {names : StrataDDM.GlobalContext} {meaning : ProgramMeaning}
    {raw : Core.Program} {annotatedProgram : Core.Program}
    {command : BooleDDM.Command SourceRange} {procedure : ProcedureMeaning}
    {rawProcedure annotatedProcedure : Core.Procedure}
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    (fragment : inConcreteCoreFragment sourceProgram names)
    (denoted : denoteProgram sourceProgram names = .ok meaning)
    (lowered : toCoreProgram sourceProgram names = .ok raw)
    (member : procedure ∈ meaning.procedures)
    (interpreted : ProcedureWasInterpreted denotation command procedure)
    (translated : ProcedureWasLowered command rawProcedure)
    (typed : Core.TypeSpec.ProcWellTyped annotatedProgram context scopes annotatedProcedure)
    (sameHeader : annotatedProcedure.header = rawProcedure.header)
    (rawMember : ∃ metadata, Core.Decl.proc rawProcedure metadata ∈ raw.decls) :
    ProcedureLayout meaning.globals procedure annotatedProcedure := by
  have outputsNodup : rawProcedure.header.outputs.keys.Nodup := by
    rw [← sameHeader]
    exact typed.outputsNodup
  obtain ⟨orderedGlobals, orderedInput⟩ :=
    lowered_inputs_match_source fragment denoted lowered member interpreted translated rawMember
  obtain ⟨modifiedGlobals, modifiedInGlobals, modifiedOrder, orderedOutput⟩ :=
    lowered_outputs_match_source fragment denoted lowered member interpreted translated
      outputsNodup rawMember
  have distinctAndFresh := interpreted_procedure_interface_names
    denotation sourceProgram names meaning denoted procedure member
  refine ⟨⟨orderedGlobals, orderedInput.1, ?_⟩,
    ⟨modifiedGlobals, modifiedInGlobals, modifiedOrder, ?_⟩,
    distinctAndFresh.1, fun name _ => distinctAndFresh.2 name⟩
  · simpa [sameHeader] using orderedInput.2
  · simpa [sameHeader] using orderedOutput

end Strata.Boole
