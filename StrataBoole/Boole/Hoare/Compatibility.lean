/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Hoare.Certificate
public import StrataBoole.Boole.Semantics.CoreReference
public import Strata.Languages.Core.Logic.ContractToHoareTriple
import all Strata.Languages.Core.CmdType
import all Strata.DL.Imperative.Stmt

/-! The statement relating Boole verification to the contract on the checked Core lowering. -/

public section

namespace Strata.Boole.Hoare

open StrataDDM

private def ready (unwritten : List Core.CoreIdent) (e : Core.Expression.Expr) : Bool :=
  (Core.CmdType.freeVars e).all fun id => !unwritten.contains id

/- Track output-only slots whose entry values cannot yet be relied upon.
Require deterministic value writes and reject escaping control in the first
Core compatibility fragment. Branches must initialize a slot on both paths.
A loop may execute zero iterations. -/
mutual
  private def coreStatement (s : Core.Statement) (unwritten : List Core.CoreIdent) :
      Option (List Core.CoreIdent) := do
    match s with
    | .cmd (.cmd (.init _ _ (.det e) _)) => if ready unwritten e then some unwritten else none
    | .cmd (.cmd (.set target (.det e) _)) =>
      if ready unwritten e then some (unwritten.filter (· != target)) else none
    | .cmd (.cmd (.assert _ e _)) | .cmd (.cmd (.assume _ e _)) =>
      if ready unwritten e then some unwritten else none
    | .block _ body _ => coreStatements body unwritten
    | .ite (.det guard) yes no _ =>
      if !ready unwritten guard then none else
        let yes ← coreStatements yes unwritten
        let no ← coreStatements no unwritten
        some (yes ++ no).eraseDups
    | .loop (.det guard) _ _ body _ =>
      if !ready unwritten guard then none else
        let _ ← coreStatements body unwritten
        some unwritten
    | _ => none
  termination_by sizeOf s

  private def coreStatements (ss : Core.Statements) (unwritten : List Core.CoreIdent) :
      Option (List Core.CoreIdent) := do
    match ss with
    | [] => some unwritten
    | s :: rest => coreStatements rest (← coreStatement s unwritten)
  termination_by sizeOf ss
end

private def sourceInFragment (source : Boole.Program) (names : GlobalContext) : Prop :=
  let .prog _ declarations := source
  -- The legacy lowering can drop globals whose type it cannot lower.
  declarations.val.all (fun
    | .command_var _ (.bind_mk _ _ _ (.int _)) => true
    | .command_var .. => false
    | _ => true) = true ∧
  checkFragment (fun ty => ty == .int || ty == .bool) source names = true

private def bodyInFragment (procedure : Core.Procedure) (body : Core.Statements) : Prop :=
  (procedure.header.inputs.toList ++ procedure.header.outputs.toList).all (·.2 == .int) = true ∧
  coreStatements body procedure.header.getOutputOnlyParams.keys = some []

/-- Integer interfaces and deterministic writes. Output-only slots must be
written before they are read and on every path that completes. -/
def CoreBridgeFragment (source : Boole.Program) (names : GlobalContext)
    (checked : Core.Program) (name : String) : Prop :=
  sourceInFragment source names ∧
    ∃ procedure body, checked.findProcByString? name = some procedure ∧
      procedure.body = .structured body ∧ bodyInFragment procedure body

/-- The compatibility statement for verified procedures in the Core bridge fragment. -/
def CoreCompatibility : Prop :=
  ∀ source names name checked params,
    checkedCoreProgram source names = .ok checked →
    CoreBridgeFragment source names checked name →
    Verified source names name →
    Core.Logic.Hoare.Procedure.contractTriple checked params name

end Strata.Boole.Hoare
