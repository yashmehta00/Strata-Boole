/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Interp

/-! An executable interpretation of structured Boole commands. The runner
follows one choice policy and bounds recursive loop unfolding. -/

public section
namespace Strata.Boole.Native
open Interpretation

inductive Result where
  | outcome (result : Interpretation.Result)
  | blocked
  | exhausted
  | unavailable (reason : String)
  deriving Repr

structure Config where
  fuel : Nat := 100
  choose : ValueType → Option Value := fun _ => none

abbrev Command := Config → State → Result

namespace Result

def mapOutcome (f : Interpretation.Result → Interpretation.Result) : Result → Result
  | .outcome result => .outcome (f result)
  | other => other

end Result

namespace Command

def seq (first next : Command) : Command := fun config state =>
  match first config state with
  | .outcome (.normal, middle) => next config middle
  | other => other

private def choose (t : ValueType) (next : t.denote → Command) : Command := fun config state =>
  match config.choose t with
  | none => .unavailable "Choice policy supplied no value"
  | some value =>
      if h : value.sort = t then next (h ▸ value.data) config state
      else .unavailable "Choice policy supplied a value of the wrong type"

def declare (binding : Binding) (initializer : Option (Interpretation.Expr binding.sort)) : Command :=
  match initializer with
  | some value => fun _ state => .outcome (Effect.declare binding value state)
  | none => fun config state =>
      if (state.locals.lookup binding.name).isSome then
        .outcome (.runtimeError (.duplicateLocal binding.name), state)
      else choose binding.sort (fun value _ state =>
        .outcome (Effect.declare binding (Interpretation.Expr.constant binding.sort value) state)) config state

def branch (guard : Guard) (yes no : Command) : Command :=
  match guard with
  | none => choose .bool (fun b => if b then yes else no)
  | some test => fun config state =>
      match test state with
      | .ok true => yes config state
      | .ok false => no config state
      | .error reason => .outcome (.runtimeError reason, state)

def loop (guard : Guard) (body : Command) : Command := fun config state =>
  unroll config.fuel config state
where
  unroll : Nat → Command
  | 0 => fun _ _ => .exhausted
  | fuel + 1 =>
      branch guard
        (seq (fun config => body { config with fuel }) (unroll fuel))
        (fun _ state => .outcome (.normal, state))

end Command

def commands : CommandAlgebra Command where
  skip := fun _ state => .outcome (.normal, state)
  seq := Command.seq
  declare := Command.declare
  assign := fun reference expression _ state => .outcome (Effect.assign reference expression state)
  havoc := fun reference t => Command.choose t fun value _ state =>
    .outcome (Effect.assign reference (Interpretation.Expr.constant t value) state)
  assertion := fun label expression _ state => .outcome (Effect.assertion label expression state)
  assumption := fun expression _ state =>
    match expression state with
    | .ok true => .outcome (.normal, state)
    | .ok false => .blocked
    | .error reason => .outcome (.runtimeError reason, state)
  branch := Command.branch
  loop := Command.loop
  scope := fun body config state => (body config state).mapOutcome (Interpretation.Result.leaveScope state)
  block := fun label body config state => (body config state).mapOutcome (Interpretation.Result.catchExit label)
  exit := fun label _ state => .outcome (.exit label, state)

abbrev Program := Interpretation.Program Command

def run (program : Program) (input : Invocation) (config : Config) : Result :=
  match program.findProcedure input.procedure with
  | none => .unavailable "Unknown procedure"
  | some procedure =>
      if !(valuesMatch program.globals input.globals && valuesMatch procedure.inputs input.arguments) then
        .unavailable "Invocation has incorrect argument counts or types"
      else match procedure.outputs.mapM (fun binding => config.choose binding.sort) with
      | none => .unavailable "Initial output values require choices"
      | some outputs =>
          if valuesMatch procedure.outputs outputs then
            procedure.body config (initialState program.globals procedure input outputs)
          else .unavailable "Initial output choices have incorrect types"

end Strata.Boole.Native

namespace Strata.Boole

/-- Construct the executable meaning of a primitive-carrier Boole program. -/
def nativeProgram (source : Boole.Program) (names : StrataDDM.GlobalContext) :
    Except InterpError Native.Program :=
  Interpretation.interpProgram Native.commands Interpretation.scalarEquality
    (fun t => (Interpretation.scalarEquality t).isSome) source names

end Strata.Boole
