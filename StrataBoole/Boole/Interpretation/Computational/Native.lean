/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Runtime
import all StrataBoole.Boole.Runtime
import all StrataBoole.Boole.Types

/-! # An executable backend scaffold

This module deliberately imports no relational semantics. It shares source
traversal, values, state, expression operations, contracts and entry setup.
Only primitive-carrier programs are accepted. A supplied choice function selects
one execution; this is not exhaustive nondeterministic execution. Each loop's
recursive unfolding is bounded. Exhaustion and missing choices are inconclusive
runner results, never source assertion failures. No native-correctness theorem
is claimed by this scaffold.
-/

public section
namespace Strata.Boole.Native

/-- The runner separates actual semantic outcomes from blocked and incomplete
attempts. In particular, fuel exhaustion does not establish divergence. -/
inductive Result (α : Type) where
  | outcome (value : Outcome α)
  | blocked
  | exhausted
  | unavailable (reason : String)
  deriving Repr

/-- A basic fixed choice policy and a bound on recursive loop unfolding.
A later runner may thread a choice stream and a global step budget instead. -/
structure Config where
  fuel : Nat := 100
  choose : ValueType → Option Value := fun _ => none

structure Computation (α : Type) where
  run : Config → State → Result α

namespace Computation

def pure (value : α) : Computation α := ⟨fun _ state => .outcome (.returned value state)⟩

def bind (first : Computation α) (next : α → Computation β) : Computation β := ⟨fun config state =>
  match first.run config state with
  | .outcome (.returned value middle) => (next value).run config middle
  | .outcome (.exited label final) => .outcome (.exited label final)
  | .outcome (.assertionFailed label final) => .outcome (.assertionFailed label final)
  | .outcome (.stuck reason final) => .outcome (.stuck reason final)
  | .blocked => .blocked | .exhausted => .exhausted | .unavailable reason => .unavailable reason⟩

instance : Monad Computation where
  pure := Computation.pure
  bind := Computation.bind

private abbrev emit (outcome : State → Outcome α) : Computation α :=
  ⟨fun _ state => .outcome (outcome state)⟩

def choose (sort : ValueType) : Computation Value := ⟨fun config state =>
  match config.choose sort with
  | some value => if value.sort == sort then .outcome (.returned value state)
      else .unavailable "Choice policy returned a value of the wrong type"
  | none => .unavailable "Choice policy supplied no value"⟩

def test : Option Expression → Computation Bool
  | some expression => StatementSemantics.test emit expression
  | none => do
    match ← choose .bool with
    | .bool value => pure value
    | _ => emit (.stuck .wrongType)

def declare (binding : Binding) (initializer : Option Expression) : Computation Unit :=
  StatementSemantics.declare emit choose binding initializer

def assign (reference : Variable) (expression : Expression) : Computation Unit :=
  StatementSemantics.assign emit reference expression

def havoc (reference : Variable) (sort : ValueType) : Computation Unit :=
  StatementSemantics.havoc emit choose reference sort

def assertion (label : String) (expression : Expression) : Computation Unit :=
  StatementSemantics.assertion emit label expression

def assumption (expression : Expression) : Computation Unit :=
  StatementSemantics.assumption emit ⟨fun _ _ => .blocked⟩ expression

def branch (guard : Option Expression) (yes no : Computation Unit) : Computation Unit :=
  StatementSemantics.branch (test guard) yes no

def scope (body : Computation Unit) : Computation Unit := ⟨fun config initial =>
  match body.run config initial with
  | .outcome outcome => .outcome (outcome.mapState fun final =>
      { final with locals := final.locals.restrict initial.locals })
  | other => other⟩

def block (label : String) (body : Computation Unit) : Computation Unit := ⟨fun config state =>
  match body.run config state with
  | .outcome (.exited name final) =>
      if name == label then .outcome (.returned () final) else .outcome (.exited name final)
  | other => other⟩

def exit (label : String) : Computation Unit := ⟨fun _ state => .outcome (.exited label state)⟩

def loop (guard : Option Expression) (body : Computation Unit) : Computation Unit := ⟨fun config initial =>
  iterate config.fuel config initial⟩
where
  iterate : Nat → Config → State → Result Unit
  | 0, _, _ => .exhausted
  | fuel + 1, config, state =>
      let step : Computation Unit := do
        if ← test guard then
          let current : Computation Unit := ⟨fun cfg state => body.run { cfg with fuel } state⟩
          current
          (⟨iterate fuel⟩ : Computation Unit)
        else pure ()
      step.run config state

end Computation

/-- The native backend rejects compound types before they reach statement
execution. Its equality function is the decidable primitive comparison. -/
def interpretation : Interpretation where
  supportsType := fun
    | .bool | .int | .nat | .real | .string | .bitvec _ => true
    | _ => false
  Expression := Expression
  Statement := Computation Unit
  literal := fun value _ => .ok value
  read := Expression.read
  unary := Expression.unary
  binary := Expression.binaryWith (fun a b => match a.equal? b with
    | some result => .ok result | none => .error .wrongType)
  conditional := Expression.conditional
  old := Expression.old
  apply := Expression.apply
  mapGet := Expression.mapGet
  -- Compound types are rejected during construction, so this field is unreachable
  -- for successfully constructed programs in the native fragment.
  mapSet := fun _ _ _ _ => .error .wrongType
  mapConst := Expression.mapConst
  sequenceEmpty := Expression.sequenceEmpty
  sequenceLength := Expression.sequenceLength
  sequenceAppend := Expression.sequenceAppend
  sequenceBuild := Expression.sequenceBuild
  skip := pure ()
  seq := fun first second => first >>= fun _ => second
  declare := Computation.declare
  assign := Computation.assign
  havoc := Computation.havoc
  assertion := Computation.assertion
  assumption := Computation.assumption
  branch := Computation.branch
  loop := Computation.loop
  scope := Computation.scope
  block := Computation.block
  exit := Computation.exit

abbrev Program := InterpProgram Expression (Computation Unit)

/-- Execute one procedure body. Contracts remain available separately and are
not injected as runtime assumptions or checks by this entry point. -/
def run (program : Program) (input : Invocation) (config : Config) : Result Unit :=
  match program.findProcedure input.procedure with
  | none => .unavailable "Unknown procedure"
  | some procedure =>
      if !(valuesMatch program.globals input.globals && valuesMatch procedure.inputs input.arguments) then
        .unavailable "Invocation has incorrect argument counts or types"
      else match procedure.outputs.mapM (fun binding => config.choose binding.sort) with
      | none => .unavailable "Initial output values require choices"
      | some outputs =>
          if valuesMatch procedure.outputs outputs then
            procedure.body.run config (initialState program.globals procedure input outputs)
          else .unavailable "Initial output choices have incorrect types"

end Strata.Boole.Native

namespace Strata.Boole
/-- Construct an executable program using the shared Boole syntax traversal. -/
def nativeProgram (source : Boole.Program) (names : StrataDDM.GlobalContext) :
    Except InterpError Native.Program := interpProgram Native.interpretation source names
end Strata.Boole
