/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Legacy.Runtime
import all StrataBoole.Boole.Interpretation.Legacy.Runtime
import all StrataBoole.Boole.Interpretation.Runtime
import all StrataBoole.Boole.Interpretation.Types

/-! # Relational denotational semantics of Boole

The semantic domains are explicit: expressions denote functions
`State → Except RuntimeError Value`; statements denote relations
`State → Outcome Unit → Prop`, packaged as `Computation Unit`. `Value` contains
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
structure Computation (α : Type) where
  run : State → Outcome α → Prop

namespace Computation
def pure (value : α) : Computation α := ⟨fun state outcome => outcome = .returned value state⟩

/-- Relational composition on returned values. Exits, assertion failures and
runtime errors propagate without consulting the continuation. -/
def bind (first : Computation α) (next : α → Computation β) : Computation β :=
  ⟨fun state outcome =>
    (∃ value middle, first.run state (.returned value middle) ∧ (next value).run middle outcome) ∨
    (∃ label final, first.run state (.exited label final) ∧ outcome = .exited label final) ∨
    (∃ label final, first.run state (.assertionFailed label final) ∧ outcome = .assertionFailed label final) ∨
    (∃ reason final, first.run state (.stuck reason final) ∧ outcome = .stuck reason final)⟩

instance instMonad : Monad (Computation) where
  pure := Computation.pure
  bind := Computation.bind

abbrev emit (outcome : State → Outcome α) : Computation α :=
  ⟨fun state result => result = outcome state⟩

abbrev get : Computation State := emit fun state => .returned state state
abbrev put (state : State) : Computation Unit := emit fun _ => .returned () state
abbrev stuck (reason : RuntimeError) : Computation α := emit (.stuck reason)

/-- Choose any value of the requested source type. -/
def choose (sort : ValueType) : Computation Value := ⟨fun state outcome =>
  ∃ value, value.sort = sort ∧ outcome = .returned value state⟩
end Computation

namespace Computation
abbrev evaluate (expression : Expression) : Computation Value :=
  StatementSemantics.evaluate emit expression

abbrev test : Option Expression → Computation Bool
  | none => ⟨fun state outcome => outcome = .returned true state ∨ outcome = .returned false state⟩
  | some expression => StatementSemantics.test emit expression

def declare (binding : Binding) (initializer : Option Expression) : Computation Unit :=
  StatementSemantics.declare emit choose binding initializer

def assign (reference : Variable) (expression : Expression) : Computation Unit :=
  StatementSemantics.assign emit reference expression

def havoc (reference : Variable) (sort : ValueType) : Computation Unit :=
  StatementSemantics.havoc emit choose reference sort

def assertion (label : String) (expression : Expression) : Computation Unit :=
  StatementSemantics.assertion emit label expression

def assumption (expression : Expression) : Computation Unit :=
  StatementSemantics.assumption emit ⟨fun _ _ => False⟩ expression

def branch (guard : Option Expression) (yes no : Computation Unit) : Computation Unit :=
  StatementSemantics.branch (test guard) yes no

/-- Drop block-local slots on every outcome, preserving updates to outer slots. -/
def scope (body : Computation Unit) : Computation Unit := ⟨fun initial outcome =>
  ∃ inner, body.run initial inner ∧ outcome = inner.mapState
    (fun final => { final with locals := final.locals.restrict initial.locals })⟩

def block (name : String) (body : Computation Unit) : Computation Unit := ⟨fun state outcome =>
  ∃ inner, body.run state inner ∧ outcome = match inner with
    | .exited label final => if label == name then .returned () final else .exited label final
    | other => other⟩

def exit (label : String) : Computation Unit := ⟨fun state outcome => outcome = .exited label state⟩

private def loopStep (guard : Computation Bool) (body rest : Computation Unit) :
    Computation Unit :=
  StatementSemantics.branch guard (bind body fun _ => rest) (pure ())

private def loopUnfold (guard : Computation Bool) (body : Computation Unit) : Nat → Computation Unit
  | 0 => ⟨fun _ _ => False⟩
  | n + 1 => loopStep guard body (loopUnfold guard body n)

/-- A loop permits every outcome reached in some finite unfolding. Taking all
unfoldings gives the least solution of the loop equation. -/
def loop (guard : Computation Bool) (body : Computation Unit) : Computation Unit :=
  ⟨fun state outcome => ∃ n, (loopUnfold guard body n).run state outcome⟩
end Computation

/-- Boole's semantic algebra over native values and state-to-outcome relations.
Combined with `interpProgram`, this defines the compositional source meaning.
No operation constructs Core expressions or turns globals into parameters. -/
@[expose] noncomputable def denotation : Interpretation where
  Expression := Expression
  Statement := Computation Unit
  literal := fun value _ => .ok value
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

abbrev ProcedureMeaning := InterpProcedure Expression (Computation Unit)
abbrev ProgramMeaning := InterpProgram Expression (Computation Unit)

/-- Assign a Boole program its compositional denotation. The result contains
procedure-body relations and separate contract predicates. A construction error
means the source has no denotation in the supported fragment; it is distinct
from a runtime error or a denotation with no outcomes. -/
noncomputable def denoteProgram (program : Boole.Program) (names : StrataDDM.GlobalContext)
    :
    Except InterpError (ProgramMeaning) := interpProgram denotation program names


/-- Run a procedure body, choosing arbitrary initial values for its output-only
slots. Contract predicates are retained separately and are not runtime checks. -/
def InterpProgram.runs (program : ProgramMeaning) (input : Invocation) (outcome : Outcome Unit) : Prop :=
  ∃ procedure, program.findProcedure input.procedure = some procedure ∧
    valuesMatch program.globals input.globals = true ∧
    valuesMatch procedure.inputs input.arguments = true ∧
    ∃ outputs, valuesMatch procedure.outputs outputs = true ∧
      procedure.body.run (initialState program.globals procedure input outputs) outcome

/-- The procedure observations compared by adequacy. Returned globals are in
declaration order; outputs are in parameter order. Failure labels/stores, local
temporaries, runtime errors, divergence and full traces are not observations here. -/
inductive Observation where
  | returned (globals outputs : List Value)
  | assertionFailure
  deriving Repr

/-- Successful body results and reachable assertion failure. A failure before
later divergence remains observable because sequencing propagates failure. -/
def InterpProgram.observes (program : ProgramMeaning) (input : Invocation) : Observation → Prop
  | .returned globals outputs =>
      ∃ procedure final, program.findProcedure input.procedure = some procedure ∧
        program.runs input (.returned () final) ∧
        readValues program.globals final.globals = some globals ∧
        readValues procedure.outputs final.locals = some outputs
  | .assertionFailure => ∃ label final, program.runs input (.assertionFailed label final)

end Strata.Boole
