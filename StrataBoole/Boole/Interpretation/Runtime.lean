/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interp
import all StrataBoole.Boole.Types

/-! # Shared state and semantic operations

These definitions are used by the semantics and the native scaffold.
Procedure invocation and contracts are independent of the statement carrier.
-/

public section
namespace Strata.Boole

instance : Repr Value where
  reprPrec value _ := match value with
    | .int n => repr n | .bool b => repr b | .nat n => repr n
    | .real r => repr r | .string t => repr t | .bitvec _ b => repr b
    | other => Std.Format.text s!"<value of {repr other.sort}>"

/-- Decidable equality for the primitive executable fragment. The function returns none for compound carriers. -/
def Value.equal? (a b : Value) : Option Bool :=
  match a, b with
  | .int a, .int b => some (a == b)
  | .bool a, .bool b => some (a == b)
  | .nat a, .nat b => some (a == b)
  | .string a, .string b => some (a == b)
  | .real a, .real b => some (a == b)
  | .bitvec n a, .bitvec m b =>
      if h : n = m then some (decide (h ▸ a = b)) else some false
  | _, _ => none

open Classical in
/-- Mathematical equality, including extensional equality of maps and functions.
Only this fallback needs classical decidability; primitive comparisons compute. -/
noncomputable def Value.equal (a b : Value) : Bool :=
  match a.equal? b with
  | some result => result
  | none => decide (a = b)

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

/-- Early exit, assertion failure and invalid runtime state are distinct effects. -/
inductive Outcome (α : Type) where
  | returned (value : α) (state : State)
  | exited (label : String) (state : State)
  | assertionFailed (label : String) (state : State)
  | stuck (reason : RuntimeError) (state : State)
  deriving Repr

/-- The final state carried by any finite outcome, including early outcomes. -/
def Outcome.state : Outcome α → State
  | .returned _ state | .exited _ state | .assertionFailed _ state | .stuck _ state => state

def Outcome.mapState (f : State → State) : Outcome α → Outcome α
  | .returned value state => .returned value (f state)
  | .exited label state => .exited label (f state)
  | .assertionFailed label state => .assertionFailed label (f state)
  | .stuck reason state => .stuck reason (f state)

/-- Expressions are read-only computations with explicit errors on invalid states. -/
abbrev Expression := State → Except RuntimeError Value

namespace Expression
def read (reference : Variable) : Expression := fun state =>
  let value := state.lookup reference
  match value with
  | some value => .ok value
  | none => .error (.undefinedVariable reference)

/-- Read a value at a requested type, with a checked transport of its carrier. -/
def atType (value : Value) (sort : ValueType) : Except RuntimeError (sort.denote) :=
  if h : value.sort = sort then .ok (h ▸ value.data) else .error .wrongType

def unary (op : UnaryOp) (expression : Expression) : Expression := fun state => do
  match op, ← expression state with
  | .neg, .int value => pure (.int (-value))
  | .intToNat, .int value => pure (.nat value.toNat)
  | .natToInt, .nat value => pure (.int (Int.ofNat value))
  | .neg, .bitvec width value => pure (.bitvec width (-value))
  | .neg, .real value => pure (.real (-value))
  | .not, .bool value => pure (.bool (!value))
  | _, _ => throw .wrongType

def binaryWith (equal : Value → Value → Except RuntimeError Bool) (op : BinaryOp) (left right : Expression) : Expression := fun state => do
  let left ← left state
  let right ← right state
  match op, left, right with
  | .add, .int a, .int b => pure (.int (a + b))
  | .sub, .int a, .int b => pure (.int (a - b))
  | .mul, .int a, .int b => pure (.int (a * b))
  | .lt, .int a, .int b => pure (.bool (decide (a < b)))
  | .le, .int a, .int b => pure (.bool (decide (a ≤ b)))
  | .gt, .int a, .int b => pure (.bool (decide (a > b)))
  | .ge, .int a, .int b => pure (.bool (decide (a ≥ b)))
  | .add, .nat a, .nat b => pure (.nat (a + b))
  | .sub, .nat a, .nat b => pure (.nat (a - b))
  | .mul, .nat a, .nat b => pure (.nat (a * b))
  | .div, .nat a, .nat b => pure (.nat (a / b))
  | .mod, .nat a, .nat b => pure (.nat (a % b))
  | .lt, .nat a, .nat b => pure (.bool (decide (a < b)))
  | .le, .nat a, .nat b => pure (.bool (decide (a ≤ b)))
  | .gt, .nat a, .nat b => pure (.bool (decide (a > b)))
  | .ge, .nat a, .nat b => pure (.bool (decide (a ≥ b)))
  | .add, .real a, .real b => pure (.real (a + b))
  | .sub, .real a, .real b => pure (.real (a - b))
  | .mul, .real a, .real b => pure (.real (a * b))
  | .div, .real a, .real b => pure (.real (a / b))
  | .lt, .real a, .real b => pure (.bool (decide (a < b)))
  | .le, .real a, .real b => pure (.bool (decide (a ≤ b)))
  | .gt, .real a, .real b => pure (.bool (decide (a > b)))
  | .ge, .real a, .real b => pure (.bool (decide (a ≥ b)))
  | .add, .bitvec width a, b =>
      let b : BitVec width ← atType b (.bitvec width)
      return .bitvec width (a + b)
  | .sub, .bitvec width a, b =>
      let b : BitVec width ← atType b (.bitvec width)
      return .bitvec width (a - b)
  | .mul, .bitvec width a, b =>
      let b : BitVec width ← atType b (.bitvec width)
      return .bitvec width (a * b)
  | .lt, .bitvec width a, b =>
      let b ← atType b (.bitvec width)
      return .bool (decide (a.toNat < b.toNat))
  | .le, .bitvec width a, b =>
      let b ← atType b (.bitvec width)
      return .bool (decide (a.toNat ≤ b.toNat))
  | .gt, .bitvec width a, b =>
      let b ← atType b (.bitvec width)
      return .bool (decide (a.toNat > b.toNat))
  | .ge, .bitvec width a, b =>
      let b ← atType b (.bitvec width)
      return .bool (decide (a.toNat ≥ b.toNat))
  | .eq, a, b => if a.sort = b.sort then return .bool (← equal a b) else throw .wrongType
  | .ne, a, b => if a.sort = b.sort then return .bool (!(← equal a b)) else throw .wrongType
  | .and, .bool a, .bool b => pure (.bool (a && b))
  | .or, .bool a, .bool b => pure (.bool (a || b))
  | .implies, .bool a, .bool b => pure (.bool (!a || b))
  | .iff, .bool a, .bool b => pure (.bool (a == b))
  | _, _, _ => throw .wrongType

/-- Equality is mathematical in the denotational backend. -/
noncomputable def binary (op : BinaryOp) (left right : Expression) : Expression :=
  binaryWith (fun a b => .ok (Value.equal a b)) op left right

/-- Apply a native function value. -/
def apply (fn argument : Expression) : Expression := fun state => do
  match ← fn state with
  | ⟨.arrow domain range, f⟩ => return ⟨range, f (← atType (← argument state) domain)⟩
  | _ => throw .wrongType

def mapGet (map index : Expression) : Expression := fun state => do
  match ← map state with
  | ⟨.map key value, f⟩ => return ⟨value, f (← atType (← index state) key)⟩
  | _ => throw .wrongType

open Classical in
noncomputable def mapSet (map index newValue : Expression) : Expression := fun state => do
  match ← map state with
  | ⟨.map key value, f⟩ =>
      let index ← atType (← index state) key
      let newValue ← atType (← newValue state) value
      return ⟨.map key value, fun k => if k = index then newValue else f k⟩
  | _ => throw .wrongType

def mapConst (key : ValueType) (initializer : Expression) : Expression := fun state => do
  let value ← initializer state
  return ⟨.map key value.sort, fun _ => value.data⟩

def sequenceEmpty (element : ValueType) : Expression := fun _ => .ok ⟨.sequence element, []⟩

def sequenceLength (sequence : Expression) : Expression := fun state => do
  match ← sequence state with
  | ⟨.sequence _, values⟩ => return .int (Int.ofNat values.length)
  | _ => throw .wrongType

def sequenceAppend (left right : Expression) : Expression := fun state => do
  match ← left state with
  | ⟨.sequence element, values⟩ =>
      return ⟨.sequence element, List.append values (← atType (← right state) (.sequence element))⟩
  | _ => throw .wrongType

def sequenceBuild (sequence element : Expression) : Expression := fun state => do
  match ← sequence state with
  | ⟨.sequence ty, values⟩ => return ⟨.sequence ty, List.append values [← atType (← element state) ty]⟩
  | _ => throw .wrongType

def conditional (guard yes no : Expression) : Expression := fun state => do
  match ← guard state with
  | .bool true => yes state
  | .bool false => no state
  | _ => throw .wrongType

/-- Only modified globals are read from entry snapshots; locals and other
globals keep their current meaning, including inside a nested `old`. -/
def old (expression : Expression) : Expression := fun state =>
  expression { state with globals := state.snapshots ++ state.globals }

end Expression

/-! Statement meanings shared by the relational and executable computations. -/
namespace StatementSemantics

variable {M : Type → Type} [Monad M]
variable (emit : {α : Type} → (State → Outcome α) → M α)
variable (choose : ValueType → M Value)

abbrev evaluate (expression : Expression) : M Value :=
  emit fun state =>
    match expression state with
    | .ok value => .returned value state
    | .error reason => .stuck reason state

abbrev test (expression : Expression) : M Bool := do
  match ← evaluate emit expression with
  | .bool value => pure value
  | _ => emit (.stuck .wrongType)

abbrev declare (binding : Binding) (initializer : Option Expression) : M Unit := do
  let state ← emit (fun state => .returned state state)
  if (state.locals.lookup binding.name).isSome then
    emit (.stuck (.duplicateLocal binding.name))
  else
    let value ← match initializer with
      | none => choose binding.sort
      | some expression => evaluate emit expression
    if value.sort ≠ binding.sort then emit (.stuck .wrongType)
    else
      let updated := { state with locals := state.locals ++ [(binding.name, value)] }
      emit fun _ => .returned () updated

abbrev assign (reference : Variable) (expression : Expression) : M Unit := do
  let state ← emit (fun state => .returned state state)
  let previous ← evaluate emit (Expression.read reference)
  let value ← evaluate emit expression
  if previous.sort ≠ value.sort then emit (.stuck .wrongType)
  else emit fun _ => .returned () (state.update reference value)

abbrev havoc (reference : Variable) (sort : ValueType) : M Unit := do
  let value ← choose sort
  assign emit reference (fun _ => .ok value)

abbrev assertion (label : String) (expression : Expression) : M Unit := do
  if ← test emit expression then pure ()
  else emit (.assertionFailed label)

abbrev assumption (blocked : M Unit) (expression : Expression) : M Unit := do
  if ← test emit expression then pure () else blocked

abbrev branch (test : M Bool) (yes no : M Unit) : M Unit := do
  if ← test then yes else no

end StatementSemantics

def Clause.holds (clause : Clause Expression) (state : State) : Prop :=
  clause.condition state = .ok (.bool true)

def InterpProcedure.requiresHold (procedure : InterpProcedure Expression S) (state : State) : Prop :=
  ∀ clause ∈ procedure.contract.requires, clause.holds state

def InterpProcedure.ensuresHold (procedure : InterpProcedure Expression S) (state : State) : Prop :=
  ∀ clause ∈ procedure.contract.ensures, clause.holds state

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

def InterpProgram.findProcedure (program : InterpProgram Expression S) (name : String) : Option (InterpProcedure Expression S) :=
  program.procedures.find? (fun procedure => procedure.name == name)

/-- The entry interface agrees on argument counts and declared types. This is
independent of Core and does not assume preconditions or execution correspondence. -/
def InterpProgram.accepts (program : InterpProgram Expression S) (input : Invocation) : Prop :=
  ∃ procedure, program.findProcedure input.procedure = some procedure ∧
    valuesMatch program.globals input.globals = true ∧
    valuesMatch procedure.inputs input.arguments = true

def initialState (globals : List Binding) (procedure : InterpProcedure Expression S)
    (input : Invocation) (outputs : List Value) : State :=
  let globalStore := bindValues globals input.globals
  { globals := globalStore
    locals := bindValues procedure.inputs input.arguments ++ bindValues procedure.outputs outputs
    snapshots := globalStore.filter (fun (name, _) => procedure.contract.modifies.contains name) }

def readValues (bindings : List Binding) (store : Store) : Option (List Value) :=
  bindings.mapM fun binding => store.lookup binding.name


end Strata.Boole
