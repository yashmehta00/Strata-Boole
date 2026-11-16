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

def get : Computation State := ⟨fun _ state => .outcome (.returned state state)⟩
def put (state : State) : Computation Unit := ⟨fun _ _ => .outcome (.returned () state)⟩
def stuck (reason : RuntimeError) : Computation α := ⟨fun _ state => .outcome (.stuck reason state)⟩

def evaluate (expression : Expression) : Computation Value := ⟨fun _ state =>
  match expression state with
  | .ok value => .outcome (.returned value state)
  | .error reason => .outcome (.stuck reason state)⟩

def choose (sort : ValueType) : Computation Value := ⟨fun config state =>
  match config.choose sort with
  | some value => if value.sort == sort then .outcome (.returned value state)
      else .unavailable "Choice policy returned a value of the wrong type"
  | none => .unavailable "Choice policy supplied no value"⟩

def test (guard : Option Expression) : Computation Bool := do
  let value ← match guard with | some expression => evaluate expression | none => choose .bool
  match value with | .bool b => pure b | _ => stuck .wrongType

def declare (binding : Binding) (initializer : Option Expression) : Computation Unit := do
  let state ← get
  if (state.locals.lookup binding.name).isSome then stuck (.duplicateLocal binding.name)
  else
    let value ← match initializer with | some expression => evaluate expression | none => choose binding.sort
    if value.sort == binding.sort then put { state with locals := state.locals ++ [(binding.name, value)] }
    else stuck .wrongType

def assign (reference : Variable) (expression : Expression) : Computation Unit := do
  let state ← get
  let previous ← evaluate (Expression.read reference)
  let value ← evaluate expression
  if previous.sort == value.sort then put (state.update reference value) else stuck .wrongType

def havoc (reference : Variable) (sort : ValueType) : Computation Unit := do
  let value ← choose sort
  assign reference (fun _ => .ok value)

def assertion (label : String) (expression : Expression) : Computation Unit := do
  if ← test (some expression) then pure ()
  else ⟨fun _ state => .outcome (.assertionFailed label state)⟩

def assumption (expression : Expression) : Computation Unit := do
  if ← test (some expression) then pure () else ⟨fun _ _ => .blocked⟩

def branch (guard : Option Expression) (yes no : Computation Unit) : Computation Unit := do
  if ← test guard then yes else no

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
      match (test guard).run config state with
      | .outcome (.returned false final) => .outcome (.returned () final)
      | .outcome (.returned true middle) =>
          match body.run { config with fuel := fuel } middle with
          | .outcome (.returned () final) => iterate fuel config final
          | other => other
      | .outcome (.exited label final) => .outcome (.exited label final)
      | .outcome (.assertionFailed label final) => .outcome (.assertionFailed label final)
      | .outcome (.stuck reason final) => .outcome (.stuck reason final)
      | .blocked => .blocked | .exhausted => .exhausted | .unavailable reason => .unavailable reason

end Computation

/-- The native backend rejects compound types before they reach statement
execution. Its equality function is the decidable primitive comparison. -/
def interpretation : Interpretation where
  supportsType := fun ty => ty.hasCoreLiteral || ty == .nat
  Expression := Expression
  Statement := Computation Unit
  intLiteral := fun value _ => .ok (.int value)
  boolLiteral := fun value _ => .ok (.bool value)
  stringLiteral := fun value _ => .ok (.string value)
  bitvecLiteral := fun width value _ => .ok (.bitvec width (BitVec.ofNat width value))
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
