/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Source

/-! # States and procedure entry shared by both interpretations -/

public section
namespace Strata.Boole

instance : Repr Value where
  reprPrec value _ := match value with
    | .int n => repr n | .bool b => repr b | .nat n => repr n
    | .real r => repr r | .string t => repr t | .bitvec _ b => repr b
    | other => Std.Format.text s!"<value of {repr other.sort}>"

/-- A finite source store. Source scoping and procedure entry ensure unique names. -/
abbrev Store := List (String × Value)

namespace Store
def lookup (store : Store) (name : String) : Option Value :=
  store.findSome? fun (key, value) => if key == name then some value else none

/-- Update an existing slot, preserving the domain and order of the store. -/
def update (store : Store) (name : String) (value : Value) : Store :=
  store.map fun (key, previous) => (key, if key == name then value else previous)

/-- Retain the current values of slots that existed at block entry. -/
def restrict (current entry : Store) : Store :=
  current.filter fun (name, _) => (entry.lookup name).isSome
end Store

/-- Runtime state, separate from the lexical `Scope` used during interpretation.
`snapshots` contains only globals in the current procedure's modifies clause. -/
structure State where
  globals : Store := []
  locals : Store := []
  snapshots : Store := []
  deriving Repr

/-- Read one source slot without changing the state. -/
def State.lookup (state : State) : Variable → Option Value
  | .global name => state.globals.lookup name
  | .local name => state.locals.lookup name

/-- Update one existing source slot. Entry snapshots are immutable. -/
def State.update (state : State) (reference : Variable) (value : Value) : State :=
  match reference with
  | .global name => { state with globals := state.globals.update name value }
  | .local name => { state with locals := state.locals.update name value }

inductive RuntimeError where
  | undefinedVariable (reference : Variable)
  | duplicateLocal (name : String)
  | wrongType
  deriving Repr

namespace Interpretation

/-- How a command completed. Every finite completion carries its final state. -/
inductive Completion where
  | normal
  | exit (label : String)
  | assertionFailure (label : String)
  | runtimeError (reason : RuntimeError)
  deriving Repr

abbrev Result := Completion × State

namespace Result

def leaveScope (entry : State) (result : Result) : Result :=
  let (completion, final) := result
  (completion, { final with locals := final.locals.restrict entry.locals })

def catchExit (label : String) (result : Result) : Result :=
  match result with
  | (.exit target, final) => if target == label then (.normal, final) else result
  | _ => result

end Result

end Interpretation

/-- Procedure invocation with global values in declaration order and arguments
in parameter order. Output-only variables receive arbitrary typed entry values. -/
structure Invocation where
  procedure : String
  globals : List Value
  arguments : List Value
  deriving Repr

def valuesMatch (bindings : List Binding) (values : List Value) : Bool :=
  bindings.length == values.length &&
    (bindings.zip values).all (fun (binding, value) => binding.sort == value.sort)

def bindValues (bindings : List Binding) (values : List Value) : Store :=
  (bindings.zip values).map fun (binding, value) => (binding.name, value)

/-- Look up a procedure by its source name. -/
def InterpProgram.findProcedure (program : InterpProgram E S) (name : String) :
    Option (InterpProcedure E S) :=
  program.procedures.find? (fun procedure => procedure.name == name)

def initialState (globals : List Binding) (procedure : InterpProcedure E S)
    (input : Invocation) (outputs : List Value) : State :=
  let globalStore := bindValues globals input.globals
  { globals := globalStore
    locals := bindValues procedure.inputs input.arguments ++ bindValues procedure.outputs outputs
    snapshots := globalStore.filter (fun (name, _) => procedure.contract.modifies.contains name) }

def readValues (bindings : List Binding) (store : Store) : Option (List Value) :=
  bindings.mapM fun binding => store.lookup binding.name

end Strata.Boole
