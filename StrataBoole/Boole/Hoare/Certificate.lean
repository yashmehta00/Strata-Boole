/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Hoare.Compile
import all StrataBoole.Boole.Hoare.Compile
import all StrataBoole.Boole.Hoare.Rules
import all StrataBoole.Boole.Runtime
import all StrataBoole.Boole.Types
public meta import Lean

/-! Procedure certificates and the adapter to Lean's `vcgen`. -/

public section
namespace Strata.Boole.Hoare

open StrataDDM

structure Prepared where
  globals : List Binding
  procedure : Procedure

def prepare (source : Boole.Program) (names : GlobalContext) (name : String) :
    Except InterpError Prepared := do
  let program ← compile source names
  let some proc := program.findProcedure name
    | throw ⟨default, s!"Unknown procedure '{name}'"⟩
  return ⟨program.globals, proc⟩

/-- The reflected source AST and the name context needed to resolve free variables. -/
structure Source where
  ast : Boole.Program
  names : GlobalContext

def prepareSource (source : Source) (name : String) : Except InterpError Prepared :=
  prepare source.ast source.names name

/-- Quantify over the native carrier of each declared slot in order. -/
def forValues (bindings : List Binding) (post : List Value → Prop) : Prop :=
  match bindings with
  | [] => post []
  | binding :: rest =>
    ∀ value : binding.sort.denote .builtins,
      forValues rest (fun values => post (⟨binding.sort, value⟩ :: values))

def Prepared.entryState (p : Prepared) (globals arguments outputs : List Value) : State :=
  initialState p.globals p.procedure ⟨p.procedure.name, globals, arguments⟩ outputs

def Prepared.postcondition (p : Prepared) : Control → Assertion
  | none => clausesHold (p.procedure.contract.ensures.filter (! ·.free))
  | some _ => fun _ => False

def Prepared.Valid (p : Prepared) : Prop :=
  forValues p.globals fun globals =>
  forValues p.procedure.inputs fun arguments =>
  forValues p.procedure.outputs fun outputs =>
    let entry := p.entryState globals arguments outputs
    clausesHold p.procedure.contract.requires entry →
    Triple (fun state => state = entry) p.procedure.body p.postcondition

private theorem forValues_apply {bindings : List Binding} {values : List Value}
    {post : List Value → Prop} (all : forValues bindings post)
    (matching : valuesMatch bindings values = true) : post values := by
  induction bindings generalizing values post with
  | nil =>
    cases values with
    | nil => exact all
    | cons value values => simp [valuesMatch] at matching
  | cons binding bindings ih =>
    cases values with
    | nil => simp [valuesMatch] at matching
    | cons value values =>
      have pieces : binding.sort = value.sort ∧ valuesMatch bindings values = true := by
        simp [valuesMatch, and_left_comm] at matching ⊢
        exact matching
      obtain ⟨sort, data⟩ := value
      change binding.sort = sort ∧ valuesMatch bindings values = true at pieces
      obtain ⟨sortEq, tail⟩ := pieces
      subst sort
      exact ih (post := fun tail => post (⟨binding.sort, data⟩ :: tail)) (all data) tail

/-- Instantiate a certificate at an entry with correctly typed source values. -/
theorem Prepared.Valid.atEntry {p : Prepared} (valid : p.Valid)
    {globals arguments outputs : List Value}
    (globalTypes : valuesMatch p.globals globals = true)
    (argumentTypes : valuesMatch p.procedure.inputs arguments = true)
    (outputTypes : valuesMatch p.procedure.outputs outputs = true)
    (requires : clausesHold p.procedure.contract.requires (p.entryState globals arguments outputs)) :
    p.procedure.body.transform p.postcondition (p.entryState globals arguments outputs) := by
  unfold Prepared.Valid at valid
  have withGlobals := forValues_apply valid globalTypes
  have withArguments := forValues_apply withGlobals argumentTypes
  have withOutputs := forValues_apply withArguments outputTypes
  exact (withOutputs requires).le_wp _ rfl

@[cbv_opaque] private def checked : Except InterpError Prepared → Prop
  | .ok p => p.Valid
  | .error _ => False

/-- A procedure certificate includes successful static checking and the
generated Hoare obligations. -/
def Verified (source : Boole.Program) (names : GlobalContext) (name : String) : Prop :=
  checked (prepare source names name)

/-- Convenience entry point for a reflected `#strata` Boole program. -/
def VerifiedSource (source : Source) (name : String) : Prop :=
  Verified source.ast source.names name

/-- Extract the compiled procedure and its verified precondition. -/
theorem verified_iff {source : Boole.Program} {names : GlobalContext} {name : String} :
    Verified source names name ↔ ∃ p, prepare source names name = .ok p ∧ p.Valid := by
  unfold Verified
  cases prepare source names name <;> simp [checked]

theorem verifiedSource_iff {source : Source} {name : String} :
    VerifiedSource source name ↔ ∃ p, prepareSource source name = .ok p ∧ p.Valid :=
  verified_iff

open Lean Elab Tactic in
/-- Reduce the compiler on the concrete source and report any compilation error. -/
elab "boole_prepare" : tactic => do
  evalTactic (← `(tactic| cbv))
  withMainContext do
    let target ← getMainTarget
    let some result := target.app1? ``checked
      | throwError "expected Hoare.Verified or Hoare.VerifiedSource"
    if result.isAppOf ``Except.error then
      let error := result.appArg!
      let message ← Meta.withTransparency .all
        (Meta.whnf (mkApp (mkConst ``InterpError.message) error))
      throwError "Boole Hoare checking failed: {message}"
    unless result.isAppOf ``Except.ok do
      throwError "could not specialize the Boole AST; provide a concrete source and procedure name"
    evalTactic (← `(tactic| simp only [checked]))

open Lean Elab Tactic in
elab "boole_label" : tactic => do
  for goal in ← getGoals do
    goal.withContext do
      let target ← instantiateMVars (← goal.getType)
      if let some clause := target.find? (·.isAppOfArity ``Obligation 2) then
        if let .lit (.strVal label) := clause.getArg! 0 then
          goal.setTag ((← goal.getTag).str label)

open Lean.Parser.Tactic in
/-- Simplify nested WPs and expose predicates over Boole's native values. -/
macro "boole_lift" location:location : tactic => `(tactic|
  simp (config := { failIfUnchanged := false })
    [wp_eq, Transformer.skip, Transformer.seq, Transformer.exit, Transformer.block,
      Transformer.scope, Transformer.step, Transformer.assignState, Transformer.initState,
      Transformer.arbitrary, Transformer.assertion, Transformer.assumption,
      Transformer.branch, Transformer.loop, Transformer.loopHead, Transformer.decreases,
      withChanges, test, clausesHold, Holds, binary, binaryValue_int, binaryValue_bool,
      binaryValue_nat, binaryValue_bitvec, binaryValue_real, binaryValue_string,
      Prepared.entryState, Prepared.postcondition, initialState, bindValues, Expression.read,
      Expression.old, Expression.unary,
      Expression.conditional, State.lookup, State.update, Store.lookup, Store.update,
      Store.restrict, Value.int, Value.bool, Value.nat, Value.bitvec, Value.string, Value.real,
      ValueType.denote, bind, pure, Except.instMonad, Except.bind, Except.pure] $location:location)

macro "boole_lift" : tactic => `(tactic| boole_lift at *)

/-- Compile the source, apply the Hoare rules with `vcgen`, and simplify the verification goals. -/
macro "boole_vcgen" : tactic => `(tactic| (
  boole_prepare
  simp only [Prepared.Valid, forValues]
  repeat intro
  vcgen
  all_goals try subst_vars
  all_goals boole_lift
  boole_label
  all_goals (try simp only [Obligation, decide_eq_true_eq, beq_iff_eq] at *)))

end Strata.Boole.Hoare
