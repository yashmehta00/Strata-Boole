/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.CoreReference
import all Strata.Languages.Core.CmdType
import all Strata.DL.Imperative.Stmt

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

/-- Compose definite-write checks along a sequence. -/
private theorem coreStatements_append (first rest : Core.Statements)
    (unwritten : List Core.CoreIdent) :
    coreStatements (first ++ rest) unwritten =
      (coreStatements first unwritten).bind (coreStatements rest) := by
  induction first generalizing unwritten with
  | nil => simp [coreStatements, Option.bind]
  | cons stmt first ih =>
    simp only [List.cons_append, coreStatements, bind]
    cases coreStatement stmt unwritten <;> simp [Option.bind, ih]

/-- This fragment contains no escaping control transfers. -/
private theorem coreStatements_closed (statements : Core.Statements)
    (unwritten remaining : List Core.CoreIdent)
    (ready : coreStatements statements unwritten = some remaining) :
    Imperative.Block.exitsCoveredByBlocks (P := Core.Expression) (CmdT := Core.Command)
      [] statements := by
  suffices covers : ∀ remaining, coreStatements statements unwritten = some remaining →
      ∀ labels, Imperative.Block.exitsCoveredByBlocks (P := Core.Expression) (CmdT := Core.Command)
        labels statements by
    exact covers remaining ready []
  apply coreStatements.induct
    (motive1 := fun stmt unwritten => ∀ remaining, coreStatement stmt unwritten = some remaining →
      ∀ labels, Imperative.Stmt.exitsCoveredByBlocks labels stmt)
    (motive2 := fun stmts unwritten => ∀ remaining, coreStatements stmts unwritten = some remaining →
      ∀ labels, Imperative.Block.exitsCoveredByBlocks labels stmts)
  case case9 =>
    intro unwritten label body md ih remaining run labels
    exact ih remaining (by simpa [coreStatement] using run) (label :: labels)
  case case10 =>
    intro unwritten guard yes no md skipped remaining run _
    simp [coreStatement, skipped] at run
  case case11 =>
    intro unwritten guard yes no md checked ihYes ihNo remaining run labels
    simp only [coreStatement, ite_eq_right checked, bind] at run
    cases yesRun : coreStatements yes unwritten <;> simp [yesRun, Option.bind] at run
    cases noRun : coreStatements no unwritten <;> simp [noRun] at run
    exact ⟨ihYes _ yesRun labels, ihNo _ noRun labels⟩
  case case12 =>
    intro unwritten guard measure invariants body md skipped remaining run _
    simp [coreStatement, skipped] at run
  case case13 =>
    intro unwritten guard measure invariants body md checked ih remaining run labels
    simp only [coreStatement, ite_eq_right checked, bind] at run
    cases bodyRun : coreStatements body unwritten <;> simp [bodyRun, Option.bind] at run
    exact ih _ bodyRun labels
  case case14 =>
    intro stmt unwritten _ _ _ _ _ _ _ remaining run _
    rw [coreStatement.eq_def] at run
    split at run <;> first | contradiction | solve_by_elim
  case case16 =>
    intro unwritten stmt rest ihStmt ihRest remaining run labels
    rw [coreStatements.eq_def] at run
    cases next : coreStatement stmt unwritten with
    | none => simp [next, bind, Option.bind] at run
    | some seen =>
      have restRun : coreStatements rest seen = some remaining := by
        simpa [next, bind, Option.bind] using run
      exact ⟨ihStmt _ next labels, ihRest _ _ restRun labels⟩
  all_goals intros <;> trivial

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

end Strata.Boole.Hoare
