/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.Bodies
public import StrataBoole.Boole.Semantics.Adequacy.Contracts
import all StrataBoole.Boole.Semantics.Adequacy.Bodies

import StrataBoole.Boole.Semantics.Adequacy.Lowering
import StrataBoole.Boole.Semantics.Adequacy.Entry
import all StrataBoole.Boole.Semantics.CoreReference
import all StrataBoole.Boole.Semantics.Semantics
import all StrataBoole.Boole.Runtime
import Strata.Languages.Core.StatementSemanticsProps

public section

/-! ## From procedure correspondence to program adequacy -/

namespace Strata.Boole

/-- Boole observations from a fixed procedure and initial state. -/
def booleBodyObservations (globals : List Binding) (procedure : ProcedureMeaning)
    (initial : State) : Observation → Prop
  | .returned globalValues outputValues =>
      ∃ final, procedure.body.run initial (.returned () final) ∧
        readValues globals final.globals = some globalValues ∧
        readValues procedure.outputs final.locals = some outputValues
  | .assertionFailure =>
      ∃ label final, procedure.body.run initial (.assertionFailed label final)

private theorem readValues_zip {bindings : List Binding} {store : Store} {values : List Value}
    (read : readValues bindings store = some values) :
    (bindings.map (·.name)).length = values.length ∧
    ∀ name value, (name, value) ∈ (bindings.map (·.name)).zip values →
      store.lookup name = some value := by
  induction bindings generalizing values with
  | nil =>
    obtain rfl := Option.some.inj read
    simp
  | cons binding rest ih =>
    simp only [readValues, List.mapM_cons, bind, Option.bind, pure] at read
    split at read
    · contradiction
    · rename_i first found
      dsimp only at read

      split at read
      · contradiction
      · rename_i tail readRest
        have same : first :: tail = values := Option.some.inj read
        subst values
        obtain ⟨size, reads⟩ := ih readRest
        constructor
        · simpa using size
        · intro name value member
          rcases List.mem_cons.mp member with equal | later
          · cases equal
            exact found
          · exact reads _ _ later

/-- Lift Core witnesses for Boole runs to the forward observational conclusion.
Source returns supply globals and outputs by name, and an assertion failure
supplies a passing prefix ending at the false assertion. -/
theorem body_observations_forward (checked : Core.Program) (globals : List Binding)
    (source : ProcedureMeaning) (target : Core.Procedure) (initial : State)
    (statements : List Core.Statement) (structured : target.body = .structured statements)
    (outputNames : (target.header.outputs.toList.filterMap fun (id, _) =>
      if globals.any (fun g => g.name == id.name) then none else some id.name) =
        source.outputs.map (·.name))
    (witnesses : ∀ outcome, source.body.run initial outcome →
      CoreForwardOutcome checked.findProcByString?
        (.stmt (.block "" statements .empty) (coreEnv initial)) outcome)
    (returnedSlots : ∀ final, source.body.run initial (.returned () final) →
      (∀ name value, final.globals.lookup name = some value →
        final.locals.lookup name = none ∧ value.sort.hasCoreLiteral = true) ∧
      (∀ name value, final.locals.lookup name = some value → value.sort.hasCoreLiteral = true))
    (observation : Observation) :
    booleBodyObservations globals source initial observation →
      coreBodyObservations checked globals target (coreStore initial) observation := by
  cases observation with
  | returned globalValues outputValues =>
    rintro ⟨final, ran, readGlobals, readOutputs⟩
    obtain ⟨trace, steps, passing⟩ := witnesses _ ran
    obtain ⟨globalSlots, localSlots⟩ := returnedSlots final ran
    obtain ⟨globalLength, globalReads⟩ := readValues_zip readGlobals
    obtain ⟨outputLength, outputReads⟩ := readValues_zip readOutputs
    rw [coreBodyObservations, structured, outputNames]
    refine ⟨coreStore final, trace, Core.CoreBodyExecE.structured steps, passing,
      ⟨globalLength, ?_⟩, ⟨outputLength, ?_⟩⟩
    · intro name value present
      have slot := globalReads name value present
      obtain ⟨notLocal, typed⟩ := globalSlots name value slot
      obtain ⟨literal, represented⟩ := Option.isSome_iff_exists.mp
        ((coreValue?_isSome_iff value).trans typed)
      exact ⟨literal, represented, (coreStore_of_global final name value notLocal slot).trans represented⟩
    · intro name value present
      have slot := outputReads name value present
      obtain ⟨literal, represented⟩ := Option.isSome_iff_exists.mp
        ((coreValue?_isSome_iff value).trans (localSlots name value slot))
      exact ⟨literal, represented, (coreStore_of_local final name value slot).trans represented⟩
  | assertionFailure =>
    rintro ⟨label, final, ran⟩
    obtain ⟨priorTrace, check, reached, steps, passing, failed⟩ := witnesses _ ran
    exact ⟨statements, priorTrace, check, reached, structured, steps, passing, failed⟩

/-- What a successful translation and type check must establish for one
procedure. Both body meanings start from the same supplied inputs and chosen
initial outputs; the public theorem subsequently hides the output choices. -/
structure ProcedureCorrespondence (checked : Core.Program) (globals : List Binding)
    (source : ProcedureMeaning) (target : Core.Procedure) : Prop where
  entry : ∀ (input : Invocation),
    valuesMatch globals input.globals = true → valuesMatch source.inputs input.arguments = true →
    ∀ store, coreEntry globals target input store ↔
      ∃ outputs, valuesMatch source.outputs outputs = true ∧
        store = coreStore (initialState globals source input outputs)
  body : ∀ (input : Invocation),
    valuesMatch globals input.globals = true → valuesMatch source.inputs input.arguments = true →
    ∀ outputs, valuesMatch source.outputs outputs = true → ∀ observation,
      booleBodyObservations globals source (initialState globals source input outputs) observation ↔
      coreBodyObservations checked globals target
        (coreStore (initialState globals source input outputs)) observation
  requires : ∀ state, procedureStateWellTyped globals source state →
    (source.requiresHold state ↔ coreClausesHold target.spec.preconditions state)
  ensures : ∀ state, procedureStateWellTyped globals source state →
    (source.ensuresHold state ↔ coreClausesHold target.spec.postconditions state)

private theorem observations_of_source_lookup (meaning : ProgramMeaning) (input : Invocation)
    (procedure : ProcedureMeaning) (found : meaning.findProcedure input.procedure = some procedure)
    (globalsMatch : valuesMatch meaning.globals input.globals = true)
    (inputsMatch : valuesMatch procedure.inputs input.arguments = true)
    (observation : Observation) :
    meaning.observes input observation ↔
      ∃ outputs, valuesMatch procedure.outputs outputs = true ∧
        booleBodyObservations meaning.globals procedure
          (initialState meaning.globals procedure input outputs) observation := by
  have sameProcedure : ∀ other, meaning.findProcedure input.procedure = some other → other = procedure :=
    fun _ lookup => Option.some.inj (lookup.symm.trans found)
  cases observation with
  | returned globalValues outputValues =>
    constructor
    · rintro ⟨observed, final, observedFound, ran, globals, outputsRead⟩
      obtain ⟨ranProc, ranFound, _, _, outputs, typed, bodyRun⟩ := ran
      obtain rfl := sameProcedure observed observedFound
      obtain rfl := sameProcedure ranProc ranFound
      exact ⟨outputs, typed, final, bodyRun, globals, outputsRead⟩
    · rintro ⟨outputs, typed, final, ran, globals, outputsRead⟩
      exact ⟨procedure, final, found,
        ⟨procedure, found, globalsMatch, inputsMatch, outputs, typed, ran⟩, globals, outputsRead⟩
  | assertionFailure =>
    constructor
    · rintro ⟨label, final, ranProc, ranFound, _, _, outputs, typed, ran⟩
      obtain rfl := sameProcedure ranProc ranFound
      exact ⟨outputs, typed, label, final, ran⟩
    · rintro ⟨outputs, typed, label, final, ran⟩
      exact ⟨label, final, procedure, found, globalsMatch, inputsMatch, outputs, typed, ran⟩

/-- Procedure correspondences suffice for the whole-program conclusion of
adequacy, in both directions and for both kinds of observations. -/
theorem adequacy_of_procedure_correspondence (meaning : ProgramMeaning) (checked : Core.Program)
    (procedures : ∀ source ∈ meaning.procedures,
      ∃ target, checked.findProcByString? source.name = some target ∧
        ProcedureCorrespondence checked meaning.globals source target) :
    (∀ input, meaning.accepts input →
      meaning.observes input = coreObservations checked meaning.globals input) ∧
    contractsAgree meaning checked := by
  constructor
  · rintro input ⟨source, found, globalsMatch, inputsMatch⟩
    have lookup : meaning.procedures.find? (fun p => p.name == input.procedure) = some source := found
    have member := List.mem_of_find?_eq_some lookup
    have foundName := List.find?_some lookup
    have nameEq : source.name = input.procedure := beq_iff_eq.mp foundName
    obtain ⟨target, foundTarget, correspondence⟩ := procedures source member
    rw [nameEq] at foundTarget
    funext observation
    apply propext
    rw [observations_of_source_lookup meaning input source found globalsMatch inputsMatch]
    constructor
    · rintro ⟨outputs, typed, observed⟩
      exact ⟨target, _, foundTarget,
        (correspondence.entry input globalsMatch inputsMatch _).mpr ⟨outputs, typed, rfl⟩,
        (correspondence.body input globalsMatch inputsMatch outputs typed observation).mp observed⟩
    · rintro ⟨observedProc, store, observedFound, entered, observed⟩
      have sameTarget : observedProc = target := Option.some.inj (observedFound.symm.trans foundTarget)
      subst observedProc
      obtain ⟨outputs, typed, rfl⟩ := (correspondence.entry input globalsMatch inputsMatch store).mp entered
      exact ⟨outputs, typed,
        (correspondence.body input globalsMatch inputsMatch outputs typed observation).mpr observed⟩
  · intro source member
    obtain ⟨target, foundTarget, correspondence⟩ := procedures source member
    exact ⟨target, foundTarget,
      fun state typed => ⟨correspondence.requires state typed, correspondence.ensures state typed⟩⟩

end Strata.Boole

