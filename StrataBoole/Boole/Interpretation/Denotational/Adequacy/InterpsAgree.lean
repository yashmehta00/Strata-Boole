/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Denotational.CoreReference
public import Strata.Languages.Core.Logic.ContractToHoareTriple

/-! Model independence for the integer and Boolean fragment of Core lowered from Boole. -/

public section

namespace Strata.Boole

open StrataDDM

/-- Equality of scalar payloads across models, including absence of a binding. Each
present value carries the type interpretation of its own runtime factory. -/
def scalarStoresAgree (left right : Core.Expression.Factory) (σ τ : Core.CoreStore) : Prop :=
  ∀ id, (σ id = none ∧ τ id = none) ∨
    (∃ n : Int, σ id = some (.ofInt left.model.tcInterp n) ∧
      τ id = some (.ofInt right.model.tcInterp n)) ∨
    (∃ b : Bool, σ id = some (.ofBool left.model.tcInterp b) ∧
      τ id = some (.ofBool right.model.tcInterp b))

/-- Compare two models at corresponding stores. Body observations include returned
values and reachable assertion failures. The separate clause comparison applies at
both entry and exit, including clauses that read saved `old` values. -/
theorem interpsAgree
    (source : Boole.Program) (names : GlobalContext) (checked : Core.Program)
    (lowered : checkedCoreProgram source names = .ok checked)
    (fragment : checkFragment (fun ty => ty == .int || ty == .bool) source names = true)
    (name : String) (proc : Core.Procedure)
    (lookup : checked.findProcByString? name = some proc)
    (left right : Core.Expression.Factory)
    (leftFactory : left.factory = Core.Factory) (rightFactory : right.factory = Core.Factory) :
    (∀ globals σ τ, scalarStoresAgree left right σ τ → ∀ observation,
      coreBodyObservations checked globals proc σ observation left ↔
      coreBodyObservations checked globals proc τ observation right) ∧
    (∀ σ τ, scalarStoresAgree left right σ τ →
      ∀ labeled ∈ (proc.spec.preconditions.toList ++ proc.spec.postconditions.toList),
      ∀ b : Bool,
        Core.Expression.eval left σ labeled.2.expr = some (.ofBool left.model.tcInterp b) ↔
        Core.Expression.eval right τ labeled.2.expr = some (.ofBool right.model.tcInterp b)) := by
  sorry

end Strata.Boole
