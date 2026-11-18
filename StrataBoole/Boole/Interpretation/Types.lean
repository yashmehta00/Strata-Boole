/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-! # Boole types and their mathematical carriers

Maps denote total functions, sequences denote lists, and sets denote
predicates. Real values have the rational carrier `Rat`.
-/

public section
namespace Strata.Boole

/-- The built-in value types of the denotational fragment. -/
inductive ValueType where
  | bool | int | nat | real | string | regex
  | bitvec (width : Nat)
  | arrow (domain range : ValueType)
  | map (key value : ValueType)
  | sequence (element : ValueType)
  | set (element : ValueType)
  deriving DecidableEq, Repr, Inhabited

instance : BEq ValueType := ⟨fun a b => decide (a = b)⟩

instance : LawfulBEq ValueType where
  eq_of_beq := by intro a b h; exact of_decide_eq_true h
  rfl := by intro a; exact decide_eq_true rfl

/-- The Lean type of mathematical values denoted by each Boole type. -/
@[expose, reducible] def ValueType.denote : ValueType → Type
  | .bool => Bool
  | .int => Int
  | .nat => Nat
  | .real => Rat
  | .string => String
  | .regex => String → Prop
  | .bitvec width => BitVec width
  | .arrow domain range => domain.denote → range.denote
  | .map key value => key.denote → value.denote
  | .sequence element => List element.denote
  | .set element => element.denote → Prop

/-- A source value paired with its native mathematical carrier. The type code
ensures that an integer contains an Int, a sequence contains a List, and so on. -/
structure Value where
  sort : ValueType
  data : sort.denote

@[expose, match_pattern] def Value.int (value : Int) : Value := ⟨.int, value⟩
@[expose, match_pattern] def Value.bool (value : Bool) : Value := ⟨.bool, value⟩
@[expose, match_pattern] def Value.nat (value : Nat) : Value := ⟨.nat, value⟩
@[expose, match_pattern] def Value.string (value : String) : Value := ⟨.string, value⟩
@[expose, match_pattern] def Value.real (value : Rat) : Value := ⟨.real, value⟩
@[expose, match_pattern] def Value.bitvec (width : Nat) (value : BitVec width) : Value := ⟨.bitvec width, value⟩

end Strata.Boole
