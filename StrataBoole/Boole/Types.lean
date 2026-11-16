/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-! # Boole types and their mathematical carriers

This domain is independent of Core syntax. Maps are total functions; sequences
are lists. Open type constructors and type variables require an explicit model.
The built-in model rejects open types instead of assigning them arbitrary Unit
carriers. `real` follows the current Lean/Core denotation's rational domain;
this is not a claim of agreement with SMT mathematical reals.
-/

public section
namespace Strata.Boole

/-- Source types, including open applications and type variables. Width markers
are syntax for bitvector widths, not standalone value types. -/
inductive ValueType where
  | con (name : String) (arguments : List ValueType)
  | bitvec (width : Nat)
  | variable (name : String)
  deriving Repr, Inhabited

@[match_pattern] abbrev ValueType.bool := ValueType.con "bool" []
@[match_pattern] abbrev ValueType.int := ValueType.con "int" []
@[match_pattern] abbrev ValueType.nat := ValueType.con "nat" []
@[match_pattern] abbrev ValueType.real := ValueType.con "real" []
@[match_pattern] abbrev ValueType.string := ValueType.con "string" []
@[match_pattern] abbrev ValueType.regex := ValueType.con "regex" []
@[match_pattern] abbrev ValueType.arrow (a b : ValueType) := ValueType.con "arrow" [a, b]
@[match_pattern] abbrev ValueType.map (a b : ValueType) := ValueType.con "Map" [a, b]
@[match_pattern] abbrev ValueType.sequence (a : ValueType) := ValueType.con "Sequence" [a]
@[match_pattern] abbrev ValueType.set (a : ValueType) := ValueType.con "Set" [a]
abbrev ValueType.named := ValueType.con

/-- Structural equality, including arguments of open type constructors. -/
def ValueType.decEq : (a b : ValueType) → Decidable (a = b)
  | .con n as, .con m bs =>
      if h : n = m then
        match decEqList as bs with
        | .isTrue e => .isTrue (by rw [h, e])
        | .isFalse e => .isFalse (by intro h; cases h; exact e rfl)
      else .isFalse (by intro e; cases e; exact h rfl)
  | .bitvec n, .bitvec m =>
      if h : n = m then .isTrue (by rw [h]) else .isFalse (by intro e; cases e; exact h rfl)
  | .variable n, .variable m =>
      if h : n = m then .isTrue (by rw [h]) else .isFalse (by intro e; cases e; exact h rfl)
  | .con .., .bitvec .. | .con .., .variable .. | .bitvec .., .con ..
  | .bitvec .., .variable .. | .variable .., .con .. | .variable .., .bitvec .. => .isFalse nofun
where
  decEqList : (a b : List ValueType) → Decidable (a = b)
  | [], [] => .isTrue rfl
  | [], _ :: _ | _ :: _, [] => .isFalse nofun
  | a :: as, b :: bs =>
      match ValueType.decEq a b, decEqList as bs with
      | .isTrue h, .isTrue e => .isTrue (by rw [h, e])
      | .isFalse h, _ => .isFalse (by intro e; cases e; exact h rfl)
      | _, .isFalse h => .isFalse (by intro e; cases e; exact h rfl)

instance : DecidableEq ValueType := ValueType.decEq

instance : BEq ValueType := ⟨fun a b => decide (a = b)⟩

/-- Boolean type checks agree with mathematical type equality. -/
instance : LawfulBEq ValueType where
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
  rfl := by intro a; exact decide_eq_true rfl

/-- A mathematical interpretation for externally declared types. A model must
explicitly advertise which constructors/variables it interprets. This record
alone does not interpret datatype constructors, functions, or program axioms. -/
structure TypeModel where
  typeConstructor : String → List ValueType → Type
  typeVariable : String → Type
  hasConstructor : String → Nat → Bool
  hasVariable : String → Bool

/-- Closed built-in types need no external model. Open types are rejected. -/
def TypeModel.builtins : TypeModel where
  typeConstructor := fun _ _ => Empty
  typeVariable := fun _ => Empty
  hasConstructor := fun _ _ => false
  hasVariable := fun _ => false

/-- Assign each source type its Lean carrier. Functions, maps and predicates
need not be decidable or executable; these are mathematical domains. -/
@[expose, reducible] def ValueType.denote (model : TypeModel) : ValueType → Type
  | .bool => Bool
  | .int => Int
  | .nat => Nat
  | .real => Rat
  | .string => String
  | .regex => String → Prop
  | .bitvec width => BitVec width
  | .arrow domain range => domain.denote model → range.denote model
  | .map key value => key.denote model → value.denote model
  | .sequence element => List (element.denote model)
  | .set element => element.denote model → Prop
  | .con name arguments => model.typeConstructor name arguments
  | .variable name => model.typeVariable name

/-- Whether all open type names in a type have meanings in the supplied model. -/
def ValueType.supported (model : TypeModel) : ValueType → Bool
  | .bool | .int | .nat | .real | .string | .regex | .bitvec _ => true
  | .arrow a b | .map a b => a.supported model && b.supported model
  | .sequence a | .set a => a.supported model
  | .con name arguments => model.hasConstructor name arguments.length &&
      arguments.attach.all (fun a => a.val.supported model)
  | .variable name => model.hasVariable name
termination_by ty => sizeOf ty
decreasing_by
  all_goals simp_all
  all_goals first
    | omega
    | (have bound := List.sizeOf_lt_of_mem a.property; omega)

/-- Types whose values have a direct Core literal representation in this
prototype. Nat and compound values require a different representation bridge. -/
def ValueType.hasCoreLiteral : ValueType → Bool
  | .bool | .int | .real | .string | .bitvec _ => true
  | _ => false

end Strata.Boole
