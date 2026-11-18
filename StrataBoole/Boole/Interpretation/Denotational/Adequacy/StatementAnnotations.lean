/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Procedure
import all Strata.Languages.Core.Procedure
import all Strata.Languages.Core.Statement

public section

namespace Strata.Boole

mutual

/-- Erase expression annotations in a structured Core statement, including
conditions and loop specifications. Keep declared types and metadata. -/
@[expose] def eraseStatementAnnotations : Core.Statement → Core.Statement
  | .cmd command => .cmd command.eraseTypes
  | .block label body md => .block label (eraseStatementsAnnotations body) md
  | .ite guard yes no md =>
    .ite (guard.map Lambda.LExpr.eraseTypes)
      (eraseStatementsAnnotations yes) (eraseStatementsAnnotations no) md
  | .loop guard measure invariants body md =>
    .loop (guard.map Lambda.LExpr.eraseTypes) (measure.map Lambda.LExpr.eraseTypes)
      (invariants.map fun (label, invariant) => (label, invariant.eraseTypes))
      (eraseStatementsAnnotations body) md
  | .exit label md => .exit label md
  | .typeDecl ty md => .typeDecl ty md

/-- Erase expression annotations across a structured statement list. -/
@[expose] def eraseStatementsAnnotations : List Core.Statement → List Core.Statement
  | [] => []
  | statement :: rest => eraseStatementAnnotations statement :: eraseStatementsAnnotations rest

end

/-- Keep the header, erase the contract expressions, and erase annotations
throughout the structured body. CFG bodies are outside the Boole fragment. -/
@[expose] def procedureWithoutAnnotations (procedure : Core.Procedure) : Core.Procedure :=
  let body := match procedure.body with
    | .structured statements => .structured (eraseStatementsAnnotations statements)
    | .cfg cfg => .cfg (Core.DetCFG.eraseTypes cfg)
  { procedure with body, spec := Core.Procedure.Spec.eraseTypes procedure.spec }

end Strata.Boole
