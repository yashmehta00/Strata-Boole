/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Runtime

/-! A Boole expression of type `t` denotes a state-dependent Lean value of
type `t.denote`. Variable lookup extracts typed values from the heterogeneous store.
Source syntax traversal is defined in `Interp.lean`. -/

public section
namespace Strata.Boole.Interpretation

abbrev Expr (t : ValueType) := State → Except RuntimeError t.denote

namespace Expr

def constant (t : ValueType) (value : t.denote) : Expr t := fun _ => .ok value

def map {a b : ValueType} (f : a.denote → b.denote) (x : Expr a) : Expr b :=
  fun state => f <$> x state

def zip {a b c : ValueType} (f : a.denote → b.denote → c.denote)
    (x : Expr a) (y : Expr b) : Expr c := fun state => do
  return f (← x state) (← y state)

/-- A lifted unary operation returns exactly the operation applied to a
successful value of its operand. -/
theorem map_eq_ok_iff {a b : ValueType} (f : a.denote → b.denote) (expression : Expr a)
    (state : State) (value : b.denote) :
    map f expression state = .ok value ↔
      ∃ operand, expression state = .ok operand ∧ f operand = value := by
  cases evaluated : expression state <;> simp [map, evaluated, Functor.map, Except.map]

/-- A lifted binary operation returns exactly the operation applied to the
successful values of both operands in the same initial state. -/
theorem zip_eq_ok_iff {a b c : ValueType} (f : a.denote → b.denote → c.denote)
    (left : Expr a) (right : Expr b) (state : State) (value : c.denote) :
    zip f left right state = .ok value ↔
      ∃ x y, left state = .ok x ∧ right state = .ok y ∧ f x y = value := by
  cases evaluatedLeft : left state <;>
    cases evaluatedRight : right state <;>
    simp [zip, evaluatedLeft, evaluatedRight, Bind.bind, Except.bind, Pure.pure, Except.pure]

def read (t : ValueType) (reference : Variable) : Expr t := fun state =>
  match state.lookup reference with
  | none => .error (.undefinedVariable reference)
  | some value => if h : value.sort = t then .ok (h ▸ value.data) else .error .wrongType

/-- A map update denotes function update using the supplied equality on keys.
All three subexpressions are evaluated in the same initial state. -/
def mapSet {key value : ValueType} (equal : key.denote → key.denote → Bool)
    (mapping : Expr (.map key value)) (index : Expr key) (replacement : Expr value) :
    Expr (.map key value) := fun state => do
  let f ← mapping state
  let index ← index state
  let replacement ← replacement state
  return fun x => if equal x index then replacement else f x

def ite (guard : Expr .bool) (yes no : Expr t) : Expr t := fun state => do
  if ← guard state then yes state else no state

def old (expression : Expr t) : Expr t := fun state =>
  expression { state with globals := state.snapshots ++ state.globals }

end Expr

/-- Which carriers admit a Boolean equality test. The mathematical
interpretation can use classical equality for function spaces. -/
abbrev Equality := (t : ValueType) → Option (t.denote → t.denote → Bool)

def scalarEquality : Equality
  | .bool => some (· == ·)
  | .int => some (· == ·)
  | .nat => some (· == ·)
  | .real => some (· == ·)
  | .string => some (· == ·)
  | .bitvec _ => some (· == ·)
  | _ => none

end Strata.Boole.Interpretation
