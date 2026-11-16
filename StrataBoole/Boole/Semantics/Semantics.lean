/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Runtime
import all StrataBoole.Boole.Runtime
import all StrataBoole.Boole.Types

/-! # Relational denotational semantics of Boole

The semantic domains are explicit: expressions denote functions
`(State model) → Except RuntimeError (Value model)`; statements denote relations
`(State model) → Outcome Unit model → Prop`, packaged as `Computation (model := model) Unit`. `Value model` contains
native Lean integers and Booleans. Globals remain globals, and entry snapshots
are separate from the current store. No definition in this module calls the
Core translator, evaluator or operational semantics.

`denotation` supplies the compositional operations used by the structural
functions in `Interp.lean`; `denoteProgram` applies that algebra to source
syntax. Sequencing is relational composition on returned values and propagates
other outcomes. Thus equal relations are interchangeable as arguments to these
semantic operations; reasoning does not depend on their implementation text.

There may be many outcomes (havoc), or none (a blocked assumption or divergence).
The loop meaning is the least relation closed under finite iteration, without
a fuel bound. This finite-outcome model does not distinguish a blocked path
from an infinite path, or record whether an otherwise returning nondeterministic
computation also has an infinite path. Total-correctness reasoning would need
additional semantic information. Contracts are separate predicates; a body
does not assume or assert its contract. Invariants and measures are annotations
for verification and do not determine execution behavior.

For the relational approach and compositional equations, see Cornell CS 4110,
Lecture 7 (2020):
https://www.cs.cornell.edu/courses/cs4110/2020fa/lectures/lecture07.pdf
Lecture 8 explains least fixed points and reasoning by equality of denotations:
https://www.cs.cornell.edu/courses/cs4110/2020fa/lectures/lecture08.pdf
-/

public section
namespace Strata.Boole

/-- A possibly nondeterministic denotation. `computation.run state outcome`
means that the outcome belongs to the meaning at that state; `run` is relation
membership, not an algorithm that enumerates outcomes. -/
structure Computation {model : TypeModel} (α : Type) where
  run : State model → Outcome α model → Prop

namespace Computation
variable {model : TypeModel}
def pure (value : α) : Computation (model := model) α := ⟨fun state outcome => outcome = .returned value state⟩

/-- Relational composition on returned values. Exits, assertion failures and
runtime errors propagate without consulting the continuation. -/
def bind (first : Computation (model := model) α) (next : α → Computation (model := model) β) : Computation (model := model) β :=
  ⟨fun state outcome =>
    (∃ value middle, first.run state (.returned value middle) ∧ (next value).run middle outcome) ∨
    (∃ label final, first.run state (.exited label final) ∧ outcome = .exited label final) ∨
    (∃ label final, first.run state (.assertionFailed label final) ∧ outcome = .assertionFailed label final) ∨
    (∃ reason final, first.run state (.stuck reason final) ∧ outcome = .stuck reason final)⟩

instance instMonad : Monad (Computation (model := model)) where
  pure := Computation.pure
  bind := Computation.bind

def get : Computation (model := model) (State model) := ⟨fun state outcome => outcome = .returned state state⟩
def put (state : State model) : Computation (model := model) Unit := ⟨fun _ outcome => outcome = .returned () state⟩
def stuck (reason : RuntimeError) : Computation (model := model) α := ⟨fun state outcome => outcome = .stuck reason state⟩

/-- Choose any value of the requested source type. -/
def choose (sort : ValueType) : Computation (model := model) (Value model) := ⟨fun state outcome =>
  ∃ value, value.sort = sort ∧ outcome = .returned value state⟩
end Computation

namespace Computation
variable {model : TypeModel}
def evaluate (expression : Expression model) : Computation (model := model) (Value model) := ⟨fun state outcome =>
  match expression state with
  | .ok value => outcome = .returned value state
  | .error reason => outcome = .stuck reason state⟩

def test (guard : Option (Expression model)) : Computation (model := model) Bool :=
  match guard with
  | none => ⟨fun state outcome => outcome = .returned true state ∨ outcome = .returned false state⟩
  | some expression => do
      match ← evaluate expression with
      | .bool value => pure value
      | _ => stuck .wrongType

def declare (binding : Binding) (initializer : Option (Expression model)) : Computation (model := model) Unit := do
  let state ← get
  if (state.locals.lookup binding.name).isSome then stuck (.duplicateLocal binding.name)
  else
    let value ← match initializer with | none => choose binding.sort | some e => evaluate e
    if value.sort ≠ binding.sort then stuck .wrongType
    else put { state with locals := state.locals ++ [(binding.name, value)] }

def assign (reference : Variable) (expression : Expression model) : Computation (model := model) Unit := do
  let state ← get
  let previous ← evaluate (Expression.read reference)
  let value ← evaluate expression
  if previous.sort ≠ value.sort then stuck .wrongType
  else put (state.update reference value)

def havoc (reference : Variable) (sort : ValueType) : Computation (model := model) Unit := do
  let value ← choose sort
  assign reference (fun _ => .ok value)

def assertion (label : String) (expression : Expression model) : Computation (model := model) Unit := do
  if ← test (some expression) then pure ()
  else ⟨fun state outcome => outcome = .assertionFailed label state⟩

def assumption (expression : Expression model) : Computation (model := model) Unit := do
  if ← test (some expression) then pure ()
  else ⟨fun _ _ => False⟩

def branch (guard : Option (Expression model)) (yes no : Computation (model := model) Unit) : Computation (model := model) Unit := do
  if ← test guard then yes else no

/-- Drop block-local slots on every outcome, preserving updates to outer slots. -/
def scope (body : Computation (model := model) Unit) : Computation (model := model) Unit := ⟨fun initial outcome =>
  ∃ inner, body.run initial inner ∧ outcome = inner.mapState
    (fun final => { final with locals := final.locals.restrict initial.locals })⟩

def block (name : String) (body : Computation (model := model) Unit) : Computation (model := model) Unit := ⟨fun state outcome =>
  ∃ inner, body.run state inner ∧ outcome = match inner with
    | .exited label final => if label == name then .returned () final else .exited label final
    | other => other⟩

def exit (label : String) : Computation (model := model) Unit := ⟨fun state outcome => outcome = .exited label state⟩

/-- The least relation closed under the iteration clauses. Inductive generation
includes exactly the outcomes with finite derivations. These clauses operate on
guard and body denotations, not on Boole syntax. -/
inductive Iteration (guard : Computation (model := model) Bool) (body : Computation (model := model) Unit) : State model → Outcome Unit model → Prop
  | stop : guard.run initial (.returned false final) → Iteration guard body initial (.returned () final)
  | next : guard.run initial (.returned true middle) → body.run middle (.returned () nextState) →
      Iteration guard body nextState outcome → Iteration guard body initial outcome
  | guardExit : guard.run initial (.exited label final) → Iteration guard body initial (.exited label final)
  | guardFailure : guard.run initial (.assertionFailed label final) →
      Iteration guard body initial (.assertionFailed label final)
  | guardStuck : guard.run initial (.stuck reason final) → Iteration guard body initial (.stuck reason final)
  | bodyExit : guard.run initial (.returned true middle) → body.run middle (.exited label final) →
      Iteration guard body initial (.exited label final)
  | bodyFailure : guard.run initial (.returned true middle) → body.run middle (.assertionFailed label final) →
      Iteration guard body initial (.assertionFailed label final)
  | bodyStuck : guard.run initial (.returned true middle) → body.run middle (.stuck reason final) →
      Iteration guard body initial (.stuck reason final)

/-- Loop denotation, ordered by inclusion of permitted outcomes. The inductive
closure selects the least solution of the unfolding equation
`L = do if ← guard then body >>= (fun _ => L) else pure ()`.
In particular, `while true { skip }` has no finite outcome, whereas a reachable
failure in its body remains an outcome. -/
def loop (guard : Computation (model := model) Bool) (body : Computation (model := model) Unit) : Computation (model := model) Unit :=
  ⟨Iteration guard body⟩
end Computation

/-- Boole's semantic algebra over native values and state-to-outcome relations.
Combined with `interpProgram`, this defines the compositional source meaning.
No operation constructs Core expressions or turns globals into parameters. -/
@[expose] noncomputable def denotation (model : TypeModel := .builtins) : Interpretation where
  supportsType := ValueType.supported model
  Expression := (Expression model)
  Statement := Computation (model := model) Unit
  intLiteral := fun value _ => .ok (.int value)
  boolLiteral := fun value _ => .ok (.bool value)
  stringLiteral := fun value _ => .ok (.string value)
  bitvecLiteral := fun width value _ => .ok (.bitvec width (BitVec.ofNat width value))
  apply := Expression.apply
  mapGet := Expression.mapGet
  mapSet := Expression.mapSet
  mapConst := Expression.mapConst
  sequenceEmpty := Expression.sequenceEmpty
  sequenceLength := Expression.sequenceLength
  sequenceAppend := Expression.sequenceAppend
  sequenceBuild := Expression.sequenceBuild
  read := Expression.read
  unary := Expression.unary
  binary := Expression.binary
  conditional := Expression.conditional
  old := Expression.old
  skip := pure ()
  seq := fun first second => first >>= fun _ => second
  declare := Computation.declare
  assign := Computation.assign
  havoc := Computation.havoc
  assertion := Computation.assertion
  assumption := Computation.assumption
  branch := Computation.branch
  loop := fun guard => Computation.loop (Computation.test guard)
  scope := Computation.scope
  block := Computation.block
  exit := Computation.exit

abbrev ProcedureMeaning (model : TypeModel := .builtins) := InterpProcedure (Expression model) (Computation (model := model) Unit)
abbrev ProgramMeaning (model : TypeModel := .builtins) := InterpProgram (Expression model) (Computation (model := model) Unit)

/-- Assign a Boole program its compositional denotation. The result contains
procedure-body relations and separate contract predicates. A construction error
means the source has no denotation in the supported fragment; it is distinct
from a runtime error or a denotation with no outcomes. -/
noncomputable def denoteProgram (program : Boole.Program) (names : StrataDDM.GlobalContext)
    (model : TypeModel := .builtins) :
    Except InterpError (ProgramMeaning model) := interpProgram (denotation model) program names

variable {model : TypeModel}

/-- Run a procedure body, choosing arbitrary initial values for its output-only
slots. Contract predicates are retained separately and are not runtime checks. -/
def InterpProgram.runs (program : ProgramMeaning model) (input : Invocation model) (outcome : Outcome Unit model) : Prop :=
  ∃ procedure, program.findProcedure input.procedure = some procedure ∧
    valuesMatch program.globals input.globals = true ∧
    valuesMatch procedure.inputs input.arguments = true ∧
    ∃ outputs, valuesMatch procedure.outputs outputs = true ∧
      procedure.body.run (initialState program.globals procedure input outputs) outcome

/-- The procedure observations compared by adequacy. Returned globals are in
declaration order; outputs are in parameter order. Failure labels/stores, local
temporaries, runtime errors, divergence and full traces are not observations here. -/
inductive Observation (model : TypeModel := .builtins) where
  | returned (globals outputs : List (Value model))
  | assertionFailure
  deriving Repr

/-- Successful body results and reachable assertion failure. A failure before
later divergence remains observable because sequencing propagates failure. -/
def InterpProgram.observes (program : ProgramMeaning model) (input : Invocation model) : (Observation model) → Prop
  | .returned globals outputs =>
      ∃ procedure final, program.findProcedure input.procedure = some procedure ∧
        program.runs input (.returned () final) ∧
        readValues program.globals final.globals = some globals ∧
        readValues procedure.outputs final.locals = some outputs
  | .assertionFailure => ∃ label final, program.runs input (.assertionFailed label final)

end Strata.Boole
