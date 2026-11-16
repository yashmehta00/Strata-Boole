/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Semantics
import all StrataBoole.Boole.Runtime
import all StrataBoole.Boole.Types
public import StrataBoole.Verify
public import Strata.Languages.Core.StatementSemantics
public import Strata.Languages.Core.Logic.FactoryInterp
import all Strata.Languages.Core.Logic.FactoryInterp

/-! # Boole / Core adequacy

The reference side is Core's operational semantics on the existing checked
lowering. It does not execute a second interpreter or construct Core through
the Boole denotation. Native input/output observations keep the overall
statement small; the definitions below spell out their Core meaning.

These definitions select observable results from the existing Core relations.
They are shared by the statement of adequacy and its supporting proofs.
-/

public section
namespace Strata.Boole
open StrataDDM

/-- The reference pipeline, including nat-library insertion and Core's returned
type-annotated program. This is the AST-level counterpart of `Boole.typeCheck`. -/
def checkedCoreProgram (program : Boole.Program) (names : GlobalContext) :
    Except Message Core.Program := do
  let lowered ← toCoreProgram program names
  Core.typeCheck .default (withNatPreamble names lowered)

/-- Use Strata's interpretation of its built-in operators for reference
execution. The scalar fragment uses ground types. -/
@[expose] noncomputable def coreRuntimeFactory : Core.Expression.Factory :=
  ⟨Core.Factory, Core.factoryInterp, Lambda.refTyVarVal⟩

/-- Represent the scalar values of the comparison in the Core runtime model. -/
@[expose] def coreValueIn? (tc : Lambda.TyConstrInterp) (value : Value) : Option Core.Expression.Val :=
  match value with
  | .int value => some (.ofConst tc (.intConst value))
  | .bool value => some (.ofConst tc (.boolConst value))
  | .string value => some (.ofConst tc (.strConst value))
  | .real value => some (.ofConst tc (.rationalConst value))
  | .bitvec width value => some (.ofConst tc (.bitvecConst width value))
  | _ => none

/-- Represent a scalar in the reference model. -/
@[expose] def coreValue? : Value → Option Core.Expression.Val :=
  coreValueIn? Core.FactoryInterpModel.tcInterp

/-- The representation and the runtime factory use the same type interpretation. -/
theorem coreRuntimeFactory_tcInterp :
    coreRuntimeFactory.model.tcInterp = Core.FactoryInterpModel.tcInterp := by
  unfold coreRuntimeFactory Core.factoryInterp Core.FactoryInterpModel.model
  rfl

private def matchesCoreType (value : Value) (ty : Lambda.LMonoTy) : Bool :=
  match value.sort, ty with
  | .int, .int | .bool, .bool | .string, .string | .real, .real => true
  | .bitvec n, .bitvec m => n == m
  | _, _ => false

/-- The comparison is restricted to source constructs and types supported by
the scalar value representation. The Boole denotation itself is broader. -/
def inConcreteCoreFragment (source : Boole.Program) (names : GlobalContext) : Prop :=
  checkFragment ValueType.hasCoreLiteral source names = true

/-- The fragment gate is a computable syntactic check. -/
instance (source : Boole.Program) (names : GlobalContext) :
    Decidable (inConcreteCoreFragment source names) :=
  inferInstanceAs (Decidable (checkFragment ValueType.hasCoreLiteral source names = true))

/-- Bind inputs positionally after Core's generated global parameters. Output
entry values are arbitrary typed native values, represented as Core semantic values.
Core's own call-frame relation installs the old snapshots and fresh formal slots. -/
def coreEntry (globals : List Binding) (procedure : Core.Procedure)
    (input : Invocation) (store : Core.CoreStore) : Prop :=
  let inputs := procedure.header.inputs.toList
  let outputs := procedure.header.outputs.toList.filter fun (id, _) =>
    !inputs.any (fun (other, _) => other.name == id.name)
  let parameters := inputs.filter fun (id, _) => !globals.any (fun g => g.name == id.name)
  let supplied := bindValues globals input.globals ++
    (parameters.zip input.arguments).map (fun ((id, _), value) => (id.name, value))
  ∃ arguments initialOutputs coreArguments coreOutputs,
    valuesMatch globals input.globals = true ∧
    parameters.length = input.arguments.length ∧
    inputs.mapM (fun (id, _) => supplied.lookup id.name) = some arguments ∧
    (inputs.zip arguments).all (fun ((_, ty), value) => matchesCoreType value ty) = true ∧
    outputs.length = initialOutputs.length ∧
    (outputs.zip initialOutputs).all (fun ((_, ty), value) => matchesCoreType value ty) = true ∧
    arguments.mapM coreValue? = some coreArguments ∧
    initialOutputs.mapM coreValue? = some coreOutputs ∧
    Core.InitCallFrame procedure coreArguments coreOutputs store

/-- A trace's assumptions and assertions all reduce to the semantic Boolean true
in their captured environments. This is a passing execution path, not a Hoare
validity judgment. No denotational/evaluator completeness is assumed here. -/
def coreChecksPass (trace : Imperative.Trace Core.Expression) : Prop :=
  ∀ event ∈ trace,
    match event with
    | .assume check | .assert check =>
        Core.Expression.eval check.factory check.store check.expr = some (Imperative.HasBool.ttVal check.factory)
    | .cover _ => True

private def coreStoresValues (names : List String) (values : List Value) (store : Core.CoreStore)
    (tc : Lambda.TyConstrInterp := Core.FactoryInterpModel.tcInterp) : Prop :=
  names.length = values.length ∧
    ∀ name value, (name, value) ∈ names.zip values →
      ∃ represented, coreValueIn? tc value = some represented ∧ store ⟨name, ()⟩ = some represented

/-- Observations of a Core body from one particular entry store. An assertion
failure is witnessed by a finite passing prefix, even when the rest diverges. -/
def coreBodyObservations (program : Core.Program) (globals : List Binding)
    (procedure : Core.Procedure) (entry : Core.CoreStore) (observation : Observation)
    (factory : Core.Expression.Factory := coreRuntimeFactory) : Prop :=
  match observation with
  | .returned globalValues outputValues =>
      ∃ final trace,
        Core.CoreBodyExecE program.findProcByString? procedure.body
          ⟨entry, factory⟩ final trace ∧
        coreChecksPass trace ∧
        coreStoresValues (globals.map (·.name)) globalValues final factory.model.tcInterp ∧
        coreStoresValues
          (procedure.header.outputs.toList.filterMap fun (id, _) =>
            if globals.any (fun g => g.name == id.name) then none else some id.name)
          outputValues final factory.model.tcInterp
  | .assertionFailure =>
      ∃ statements precedingTrace check configuration,
        procedure.body = .structured statements ∧
        Core.CoreStepStarE program.findProcByString?
          (.stmt (.block "" statements .empty) ⟨entry, factory⟩)
          (precedingTrace ++ [.assert check]) configuration ∧
        coreChecksPass precedingTrace ∧
        Core.Expression.eval check.factory check.store check.expr =
          some (Imperative.HasBool.ffVal check.factory)

/-- Choose a procedure and an entry frame, then observe its body. `globals`
is source interface metadata; this definition does not read Boole denotations. -/
def coreObservations (program : Core.Program) (globals : List Binding)
    (input : Invocation) (observation : Observation) : Prop :=
  ∃ procedure entry,
    program.findProcByString? input.procedure = some procedure ∧
    coreEntry globals procedure input entry ∧
    coreBodyObservations program globals procedure entry observation

/-- Flatten a source state for the expression/specification comparison only.
Current slots keep their source names; snapshots get Core's reserved old names. -/
def coreStore (state : State) : Core.CoreStore := fun id =>
  match state.locals.lookup id.name with
  | some value => coreValue? value
  | none => match state.globals.lookup id.name with
    | some value => coreValue? value
    | none => state.snapshots.findSome? fun (name, value) =>
        if id.name == (Core.CoreIdent.mkOld name).name then coreValue? value else none

/-- Interface bindings have correctly typed values. The snapshot domain is
exactly the modified globals, and its values have their declared types. -/
def procedureStateWellTyped (globals : List Binding) (procedure : ProcedureMeaning) (state : State) : Prop :=
  (∃ values, valuesMatch globals values = true ∧ state.globals = bindValues globals values) ∧
  (∃ values, valuesMatch (procedure.inputs ++ procedure.outputs) values = true ∧
    state.locals = bindValues (procedure.inputs ++ procedure.outputs) values) ∧
  (∀ name value, (name, value) ∈ state.snapshots →
    name ∈ procedure.contract.modifies ∧
    ∃ binding ∈ globals, binding.name = name ∧ binding.sort = value.sort) ∧
  (∀ name ∈ procedure.contract.modifies, (state.snapshots.lookup name).isSome)

def coreClausesHold (clauses : ListMap String Core.Procedure.Check) (state : State) : Prop :=
  ∀ entry ∈ clauses.toList,
    Core.Expression.eval coreRuntimeFactory (coreStore state) entry.2.expr = some (Imperative.HasBool.ttVal coreRuntimeFactory)

/-- Contract expressions agree on well-typed source interface states. This
compares the conjunctions, including free clauses, and ensures that every source
procedure has its target procedure. It does not assert contract validity or
preserve automatically generated clause labels. -/
def contractsAgree (meaning : ProgramMeaning) (checked : Core.Program) : Prop :=
  ∀ procedure ∈ meaning.procedures,
    ∃ target, checked.findProcByString? procedure.name = some target ∧
      ∀ state, procedureStateWellTyped meaning.globals procedure state →
        (procedure.requiresHold state ↔ coreClausesHold target.spec.preconditions state) ∧
        (procedure.ensuresHold state ↔ coreClausesHold target.spec.postconditions state)

end Strata.Boole
