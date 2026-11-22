/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Interp
public import Mathlib.Data.Set.Operations
import all StrataBoole.Boole.Interpretation.Interp
import all StrataBoole.Boole.Interpretation.Expressions

/-! # Denotational semantics of Boole commands

A command means a set of pairs of an initial state and a finite outcome.
The equations follow the store-pair presentation of denotational semantics,
extended with nondeterministic choice, assertion failure and named exits.
-/

public section
namespace Strata.Boole.Denotational
open Interpretation

/-- All possible finite outcomes paired with their initial states.
A deterministic command has at most one outcome for any initial state. -/
abbrev Command := Set (State × Result)

namespace Command

/-- Skip completes normally with the initial state. -/
def skip : Command :=
  { (initial, final) | final = (.normal, initial) }

/-- Sequencing composes normal outcomes through an intermediate state and
propagates an early exit or failure of the first command. -/
def seq (first second : Command) : Command :=
  { (initial, final) |
      (∃ middle,
        (initial, (.normal, middle)) ∈ first ∧
        (middle, final) ∈ second) ∨
      (final.1 ≠ .normal ∧ (initial, final) ∈ first) }

/-- Assignment evaluates the expression in the initial state and updates its
existing, correctly typed slot. Invalid slots or expressions produce an error. -/
def assign (reference : Variable) (expression : Interpretation.Expr t) : Command :=
  { (initial, final) |
      match Interpretation.Expr.read t reference initial with
      | .error reason => final = (.runtimeError reason, initial)
      | .ok _ =>
          match expression initial with
          | .ok value => final = (.normal, initial.update reference ⟨t, value⟩)
          | .error reason => final = (.runtimeError reason, initial) }

/-- A declaration adds a fresh local slot. An omitted initializer admits
every value of the declared type. An initializer is evaluated in the initial state, before the new slot is added. -/
def declare (binding : Binding) (initializer : Option (Interpretation.Expr binding.sort)) : Command :=
  { (initial, final) |
      if (initial.locals.lookup binding.name).isSome then
        final = (.runtimeError (.duplicateLocal binding.name), initial)
      else
        match initializer with
        | none =>
            ∃ value : binding.sort.denote,
              final = (.normal, { initial with
                locals := initial.locals ++ [(binding.name, ⟨binding.sort, value⟩)] })
        | some expression =>
            match expression initial with
            | .ok value => final = (.normal, { initial with
                locals := initial.locals ++ [(binding.name, ⟨binding.sort, value⟩)] })
            | .error reason => final = (.runtimeError reason, initial) }

/-- Havoc admits an assignment for each mathematical value of the slot's type. -/
def havoc (reference : Variable) (t : ValueType) : Command :=
  { (initial, final) |
      ∃ value : t.denote,
        (initial, final) ∈ assign reference (Interpretation.Expr.constant t value) }

/-- A true assertion preserves the state. A false assertion produces a labelled
failure, and an invalid expression produces a runtime error. -/
def assertion (label : String) (expression : Interpretation.Expr .bool) : Command :=
  { (initial, final) |
      match expression initial with
      | .ok true => final = (.normal, initial)
      | .ok false => final = (.assertionFailure label, initial)
      | .error reason => final = (.runtimeError reason, initial) }

/-- An assumption preserves the state when true and admits no outcome when
false. An invalid expression produces a runtime error. -/
def assumption (expression : Interpretation.Expr .bool) : Command :=
  { (initial, final) |
      match expression initial with
      | .ok true => final = (.normal, initial)
      | .ok false => False
      | .error reason => final = (.runtimeError reason, initial) }

/-- A Boolean guard selects an arm. An absent guard admits the union of both
arms. An invalid guard produces a runtime error. -/
def branch (guard : Guard) (yes no : Command) : Command :=
  { (initial, final) |
      match guard with
      | none => (initial, final) ∈ yes ∨ (initial, final) ∈ no
      | some test =>
          match test initial with
          | .ok true => (initial, final) ∈ yes
          | .ok false => (initial, final) ∈ no
          | .error reason => final = (.runtimeError reason, initial) }

/-- The first approximation is empty. Each next approximation tests the guard,
then stops or composes the body with the preceding approximation. -/
def unroll (guard : Guard) (body : Command) : Nat → Command
  | 0 => ∅
  | n + 1 => branch guard (seq body (unroll guard body n)) skip

/-- A loop is the union of all its finite approximations. The quantifier ranges
over every natural number, so the meaning has no fixed iteration bound. -/
def loop (guard : Guard) (body : Command) : Command :=
  { (initial, final) | ∃ n, (initial, final) ∈ unroll guard body n }

/-- A scope retains the final values of the locals that existed at entry,
removing the slots introduced inside the body on every finite completion. -/
def scope (body : Command) : Command :=
  { (initial, final) |
      ∃ inner, (initial, inner) ∈ body ∧ final = Result.leaveScope initial inner }

/-- A labelled block consumes an exit to its own label and propagates every
other completion with its final state. -/
def block (label : String) (body : Command) : Command :=
  { (initial, final) |
      ∃ inner, (initial, inner) ∈ body ∧ final = Result.catchExit label inner }

/-- An exit produces the named completion without changing the state. -/
def exit (label : String) : Command :=
  { (initial, final) | final = (.exit label, initial) }

/-- On a correctly typed target slot, a normal assignment outcome is exactly
the initial state updated with a successful value of the expression. -/
theorem mem_assign_normal_iff (reference : Variable) (expression : Interpretation.Expr t)
    (initial final : State) (previous : t.denote)
    (slot : Interpretation.Expr.read t reference initial = .ok previous) :
    (initial, (.normal, final)) ∈ assign reference expression ↔
      ∃ value, expression initial = .ok value ∧
        final = initial.update reference ⟨t, value⟩ := by
  cases evaluated : expression initial <;> simp [assign, Set.mem_ofPred_eq, slot, evaluated]

/-- Normal sequencing outcomes are exactly relational composition through a
normal intermediate state. -/
theorem mem_seq_normal_iff (first second : Command) (initial final : State) :
    (initial, (.normal, final)) ∈ seq first second ↔
      ∃ middle, (initial, (.normal, middle)) ∈ first ∧
        (middle, (.normal, final)) ∈ second := by
  simp [seq, Set.mem_ofPred_eq]

/-- The assignment equation describes exactly the shared state update used by
the executable interpretation, including invalid-state errors. -/
theorem mem_assign_iff (reference : Variable) (expression : Interpretation.Expr t)
    (initial : State) (final : Result) :
    (initial, final) ∈ assign reference expression ↔
      final = Effect.assign reference expression initial := by
  simp only [assign, Set.mem_ofPred_eq]
  cases slot : Interpretation.Expr.read t reference initial <;>
    cases evaluated : expression initial <;>
    simp [Effect.assign, slot, evaluated]

/-- Initializing a local has exactly the result of the shared declaration
effect, including duplicate-slot and expression errors. -/
theorem mem_declare_some_iff (binding : Binding) (expression : Interpretation.Expr binding.sort)
    (initial : State) (final : Result) :
    (initial, final) ∈ declare binding (some expression) ↔
      final = Effect.declare binding expression initial := by
  simp only [declare, Set.mem_ofPred_eq]
  by_cases duplicate : (initial.locals.lookup binding.name).isSome = true
  · simp [Effect.declare, duplicate]
  · cases evaluated : expression initial <;>
      simp [Effect.declare, duplicate, evaluated]

/-- The assertion equation has exactly the result of the shared assertion
effect, including its label and final state on failure. -/
theorem mem_assertion_iff (label : String) (expression : Interpretation.Expr .bool)
    (initial : State) (final : Result) :
    (initial, final) ∈ assertion label expression ↔
      final = Effect.assertion label expression initial := by
  simp only [assertion, Set.mem_ofPred_eq]
  cases evaluated : expression initial with
  | error reason => simp [Effect.assertion, evaluated]
  | ok value => cases value <;> simp [Effect.assertion, evaluated]

end Command

/-- Instantiate the source fold with the mathematical command equations. -/
def commands : CommandAlgebra Command where
  skip := Command.skip
  seq := Command.seq
  declare := Command.declare
  assign := Command.assign
  havoc := Command.havoc
  assertion := Command.assertion
  assumption := Command.assumption
  branch := Command.branch
  loop := Command.loop
  scope := Command.scope
  block := Command.block
  exit := Command.exit

open Classical in
noncomputable def equality : Equality := fun t =>
  some ((scalarEquality t).getD (fun a b => decide (a = b)))

abbrev Program := Interpretation.Program Command

/-- Construct the mathematical meaning directly from the Boole source syntax. -/
noncomputable def denoteProgram (source : Boole.Program) (names : StrataDDM.GlobalContext) :
    Except InterpError Program :=
  Interpretation.interpProgram commands equality (fun _ => true) source names

/-- An invocation admits a result when a matching procedure admits it from an
entry state containing the supplied typed inputs and some typed initial outputs. -/
def runs (program : Program) (input : Invocation) (result : Result) : Prop :=
  ∃ procedure, program.findProcedure input.procedure = some procedure ∧
    valuesMatch program.globals input.globals = true ∧
    valuesMatch procedure.inputs input.arguments = true ∧
    ∃ outputs, valuesMatch procedure.outputs outputs = true ∧
      (initialState program.globals procedure input outputs, result) ∈ procedure.body

end Strata.Boole.Denotational
