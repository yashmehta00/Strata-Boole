/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interp

/-! The syntactic content of the bridge's source check. `checkFragment` runs
the shared interpreter with only `int` and `bool` supported, so every type
annotation it accepts is one of those two. The expression proof consumes this
predicate; `FragmentTypes.lean` derives it from the check. -/

public section

namespace Strata.Boole.Hoare

open StrataDDM

/-- Type syntax accepted by the bridge's source check. -/
@[expose] def bridgeType : Boole.Type → Prop
  | .int _ | .bool _ => True
  | _ => False

/-- An expression accepted by the bridge's source check. Typed operators
carry `int` or `bool`. Natural-number, map and sequence operators are absent.
Forms that the Hoare compiler rejects by itself (`app`, string and bitvector
literals outside a typed position) need no restriction. -/
inductive BridgeTyped : Boole.Expr → Prop where
  | natToInt (r n) : BridgeTyped (.natToInt r n)
  | strLit (r s) : BridgeTyped (.strLit r s)
  | bv1Lit (r n) : BridgeTyped (.bv1Lit r n)
  | bv8Lit (r n) : BridgeTyped (.bv8Lit r n)
  | bv16Lit (r n) : BridgeTyped (.bv16Lit r n)
  | bv32Lit (r n) : BridgeTyped (.bv32Lit r n)
  | bv64Lit (r n) : BridgeTyped (.bv64Lit r n)
  | bv128Lit (r n) : BridgeTyped (.bv128Lit r n)
  | app (r f a) : BridgeTyped (.app r f a)
  | btrue (r) : BridgeTyped (.btrue r)
  | bfalse (r) : BridgeTyped (.bfalse r)
  | fvar (r i) : BridgeTyped (.fvar r i)
  | bvar (r i) : BridgeTyped (.bvar r i)
  | not (r) {a} : BridgeTyped a → BridgeTyped (.not r a)
  | neg (r) {ty a} : bridgeType ty → BridgeTyped a → BridgeTyped (.neg_expr r ty a)
  | add (r) {ty a b} : bridgeType ty → BridgeTyped a → BridgeTyped b →
      BridgeTyped (.add_expr r ty a b)
  | sub (r) {ty a b} : bridgeType ty → BridgeTyped a → BridgeTyped b →
      BridgeTyped (.sub_expr r ty a b)
  | mul (r) {ty a b} : bridgeType ty → BridgeTyped a → BridgeTyped b →
      BridgeTyped (.mul_expr r ty a b)
  | le (r) {ty a b} : bridgeType ty → BridgeTyped a → BridgeTyped b →
      BridgeTyped (.le r ty a b)
  | lt (r) {ty a b} : bridgeType ty → BridgeTyped a → BridgeTyped b →
      BridgeTyped (.lt r ty a b)
  | ge (r) {ty a b} : bridgeType ty → BridgeTyped a → BridgeTyped b →
      BridgeTyped (.ge r ty a b)
  | gt (r) {ty a b} : bridgeType ty → BridgeTyped a → BridgeTyped b →
      BridgeTyped (.gt r ty a b)
  | equal (r) {ty a b} : bridgeType ty → BridgeTyped a → BridgeTyped b →
      BridgeTyped (.equal r ty a b)
  | notEqual (r) {ty a b} : bridgeType ty → BridgeTyped a → BridgeTyped b →
      BridgeTyped (.not_equal r ty a b)
  | and (r) {a b} : BridgeTyped a → BridgeTyped b → BridgeTyped (.and r a b)
  | or (r) {a b} : BridgeTyped a → BridgeTyped b → BridgeTyped (.or r a b)
  | implies (r) {a b} : BridgeTyped a → BridgeTyped b → BridgeTyped (.implies r a b)
  | equiv (r) {a b} : BridgeTyped a → BridgeTyped b → BridgeTyped (.equiv r a b)
  | ite (r) {ty c yes no} : bridgeType ty → BridgeTyped c → BridgeTyped yes → BridgeTyped no →
      BridgeTyped (.if r ty c yes no)
  | old (r) {ty a} : bridgeType ty → BridgeTyped a → BridgeTyped (.old r ty a)

end Strata.Boole.Hoare
