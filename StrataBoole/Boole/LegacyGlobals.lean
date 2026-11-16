/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole
import Strata.Util.Tactics

/-! # Compatibility with the original global pre-pass

The legacy lowering omits a global when its declared type cannot be lowered in
an empty type-variable scope. This policy is about membership in a procedure's
global interface, not which types Boole values can denote. It needs no Core
values, typing rules, or evaluation.
-/

public section
namespace Strata.Boole

/-- Does the legacy global pre-pass retain a declaration of this type? -/
def retainLegacyGlobal (names : StrataDDM.GlobalContext) (ty : Boole.Type) : Bool :=
  match ty with
  | .bool _ | .int _ | .string _ | .nat _ | .tvar .. => true
  | .bv _ width =>
      match width with
      | .W1 _ | .W8 _ | .W16 _ | .W32 _ | .W64 _ | .W128 _ => true
      | _ => false
  | .arrow _ domain range => retainLegacyGlobal names domain && retainLegacyGlobal names range
  | .Map _ value key => retainLegacyGlobal names key && retainLegacyGlobal names value
  | .Sequence _ element => retainLegacyGlobal names element
  | .fvar _ index arguments =>
      (names.nameOf? index).isSome && arguments.toList.attach.all (fun argument => retainLegacyGlobal names argument.val)
  | _ => false
termination_by sizeOf ty
decreasing_by
  all_goals first
    | (simp_all; omega)
    | (have bound := List.sizeOf_lt_of_mem argument.property; cases arguments; simp_all; omega)

end Strata.Boole
