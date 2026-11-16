/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interp
import all StrataBoole.Boole.Interp

/-! The content of the bridge's source check for expressions. `checkFragment`
runs the shared interpreter with only `int` and `bool` supported, so every type
annotation it accepts resolves to one of those two sorts. The expression proof
consumes this predicate; `FragmentTypes.lean` derives it from the check. -/

public section

namespace Strata.Boole.Hoare

open StrataDDM

/-- A type annotation that resolves to `int` or `bool` under the given names.
This is stated through `sourceSort` rather than syntax because a type
constructor named `int` or `bool` resolves to the same sort as the built-in. -/
def bridgeType (names : GlobalContext) (ty : Boole.Type) : Prop :=
  ∀ scope sort final, scope.names = names →
    sourceSort ty scope = .ok (sort, final) → sort = .int ∨ sort = .bool

/-- An expression accepted by the bridge's source check. Typed operators
carry a type that resolves to `int` or `bool`. Natural-number, map and
sequence operators are absent. Forms that the Hoare compiler rejects by itself
(`app`, string and bitvector literals outside a typed position) need no
restriction. -/
inductive BridgeTyped (names : GlobalContext) : Boole.Expr → Prop where
  | natToInt (r n) : BridgeTyped names (.natToInt r n)
  | strLit (r s) : BridgeTyped names (.strLit r s)
  | bv1Lit (r n) : BridgeTyped names (.bv1Lit r n)
  | bv8Lit (r n) : BridgeTyped names (.bv8Lit r n)
  | bv16Lit (r n) : BridgeTyped names (.bv16Lit r n)
  | bv32Lit (r n) : BridgeTyped names (.bv32Lit r n)
  | bv64Lit (r n) : BridgeTyped names (.bv64Lit r n)
  | bv128Lit (r n) : BridgeTyped names (.bv128Lit r n)
  | app (r f a) : BridgeTyped names (.app r f a)
  | btrue (r) : BridgeTyped names (.btrue r)
  | bfalse (r) : BridgeTyped names (.bfalse r)
  | fvar (r i) : BridgeTyped names (.fvar r i)
  | bvar (r i) : BridgeTyped names (.bvar r i)
  | not (r) {a} : BridgeTyped names a → BridgeTyped names (.not r a)
  | neg (r) {ty a} : bridgeType names ty → BridgeTyped names a →
      BridgeTyped names (.neg_expr r ty a)
  | add (r) {ty a b} : bridgeType names ty → BridgeTyped names a → BridgeTyped names b →
      BridgeTyped names (.add_expr r ty a b)
  | sub (r) {ty a b} : bridgeType names ty → BridgeTyped names a → BridgeTyped names b →
      BridgeTyped names (.sub_expr r ty a b)
  | mul (r) {ty a b} : bridgeType names ty → BridgeTyped names a → BridgeTyped names b →
      BridgeTyped names (.mul_expr r ty a b)
  | le (r) {ty a b} : bridgeType names ty → BridgeTyped names a → BridgeTyped names b →
      BridgeTyped names (.le r ty a b)
  | lt (r) {ty a b} : bridgeType names ty → BridgeTyped names a → BridgeTyped names b →
      BridgeTyped names (.lt r ty a b)
  | ge (r) {ty a b} : bridgeType names ty → BridgeTyped names a → BridgeTyped names b →
      BridgeTyped names (.ge r ty a b)
  | gt (r) {ty a b} : bridgeType names ty → BridgeTyped names a → BridgeTyped names b →
      BridgeTyped names (.gt r ty a b)
  | equal (r) {ty a b} : bridgeType names ty → BridgeTyped names a → BridgeTyped names b →
      BridgeTyped names (.equal r ty a b)
  | notEqual (r) {ty a b} : bridgeType names ty → BridgeTyped names a → BridgeTyped names b →
      BridgeTyped names (.not_equal r ty a b)
  | and (r) {a b} : BridgeTyped names a → BridgeTyped names b → BridgeTyped names (.and r a b)
  | or (r) {a b} : BridgeTyped names a → BridgeTyped names b → BridgeTyped names (.or r a b)
  | implies (r) {a b} : BridgeTyped names a → BridgeTyped names b →
      BridgeTyped names (.implies r a b)
  | equiv (r) {a b} : BridgeTyped names a → BridgeTyped names b →
      BridgeTyped names (.equiv r a b)
  | ite (r) {ty c yes no} : bridgeType names ty → BridgeTyped names c →
      BridgeTyped names yes → BridgeTyped names no → BridgeTyped names (.if r ty c yes no)
  | old (r) {ty a} : bridgeType names ty → BridgeTyped names a →
      BridgeTyped names (.old r ty a)

end Strata.Boole.Hoare
