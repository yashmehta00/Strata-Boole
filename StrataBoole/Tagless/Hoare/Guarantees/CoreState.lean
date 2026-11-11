/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.Tagless.Embed
import StrataBoole.Tagless.Hoare.Interpretation
import Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.Transform.CoreSpecification
import Strata.Languages.Core.Logic.TraceInterpUsingDenote

/-! # Core entry environments and native state correspondence

Definitions shared by source soundness and input admission. This module defines
neither an execution relation nor an additional correctness predicate: source
execution and entry well-formedness are the existing Core definitions.
-/

namespace Strata.Tagless.Hoare

/-- Entry-environment parameters for the call-free fragment: no identifier
prefixes are reserved, and all built-in Core factory functions are declared. -/
def entryParams : Core.Logic.InitEnvWFParams := {
  prefixIdents := []
  declaredFuncs := fun id => Core.isNameInFactory id.name
}

/-- Interpret a typed Core integer or Boolean expression as a native value in
a fixed Core model and semantic valuation. -/
noncomputable def denoteNative (model : Lambda.Interp Core.Factory)
    (world : Core.Logic.DenoteValuation model) (ty : Ty) (e : Core.Expression.Expr)
    (h : Lambda.LExpr.HasTypeA [] e ty.core) : ty.denote :=
  match ty with
  | .int => Lambda.LExpr.denote model.tcInterp model.opInterp
      world.freeVarVal world.tyVarVal .nil e (.tcons "int" []) h
  | .bool => Lambda.LExpr.denote model.tcInterp model.opInterp
      world.freeVarVal world.tyVarVal .nil e (.tcons "bool" []) h

/-- Each variable in the static context has a stored, typed Core expression
whose denotation equals the corresponding native value in the chosen model and
valuation. Variables outside the context are unconstrained. This relation alone
does not assert that stored expressions are runtime values; Core's entry and
execution premises supply store well-formedness where it is needed. -/
def StoreDenotes (model : Lambda.Interp Core.Factory)
    (world : Core.Logic.DenoteValuation model) (context : List Binding)
    (store : Core.CoreStore) (σ : State) : Prop :=
  ∀ binding ∈ context,
    ∃ value, store ⟨binding.name, ()⟩ = some value ∧
      ∃ h : Lambda.LExpr.HasTypeA [] value binding.ty.core,
        denoteNative model world binding.ty value h = σ.read binding.ty binding.name

end Strata.Tagless.Hoare
