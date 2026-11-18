/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.AssumptionExecution
public import StrataBoole.Boole.Semantics.Adequacy.ExpressionExecution
import all StrataBoole.Verify
import all StrataBoole.Boole.Semantics.Adequacy.Lowering
import all StrataBoole.Boole.Semantics.Adequacy.ExecutionLowering
import all StrataBoole.Boole.Semantics.Adequacy.SourceFreshness
import all StrataBoole.Boole.Interp
import all StrataBoole.Boole.Semantics.Semantics
import all Strata.Languages.Core.Statement
import all Strata.DL.Lambda.LExpr

public section
namespace Strata.Boole
open StrataDDM

/-- Successful assumption interpretation preserves scope and exposes its condition. -/
theorem interpAssume_origin (range : SourceRange)
    (annotations : Ann (Option (BooleDDM.MetadataAnn SourceRange)) SourceRange)
    (label : Ann (Option (BooleDDM.Label SourceRange)) SourceRange)
    (expression : Boole.Expr) (scope final : Scope)
    (body : denotation.Statement)
    (success : interpStmt denotation
      (.assume range annotations label expression) scope = .ok (body, final)) :
    final = scope ∧
      ∃ condition,
        interpExpr denotation expression scope = .ok (condition, scope) ∧
        body = denotation.assumption condition := by
  simp only [interpStmt.eq_def] at success
  simp only [bind, StateT.bind, Except.bind] at success
  cases expressionRun : interpExpr denotation expression scope with
  | error error => simp [expressionRun] at success
  | ok result =>
    obtain ⟨condition, middle⟩ := result
    simp only [expressionRun] at success
    have resultEq := Except.ok.inj success
    obtain ⟨bodyEq, finalEq⟩ := Prod.mk.inj resultEq
    have middleEq : middle = scope := interpExpr_readOnly _ _ _ _ _ expressionRun
    refine ⟨finalEq.symm.trans middleEq, condition, ?_, ?_⟩
    · simpa [middleEq] using expressionRun
    · exact bodyEq.symm

/-- Recover the actual lowering call for the condition of a source assumption. -/
theorem loweredAssume_origin (range : SourceRange)
    (annotations : Ann (Option (BooleDDM.MetadataAnn SourceRange)) SourceRange)
    (label : Ann (Option (BooleDDM.Label SourceRange)) SourceRange)
    (expression : Boole.Expr) (entry final : TranslateState) (raw : List Core.Statement)
    (success : lowerStatementChunk (.assume range annotations label expression) entry =
      .ok (raw, final)) :
    ∃ targetLabel md exprEntry target,
      raw = [Core.Statement.assume targetLabel target md] ∧
      ExpressionWasLowered expression exprEntry target := by
  simp only [lowerStatementChunk] at success
  rw [toCoreStmt] at success
  simp only [toCoreMetaData, bind, StateT.bind, Except.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure] at success
  cases labeled : defaultLabel range "assume" label.val entry with
  | error => simp [labeled] at success
  | ok result =>
    obtain ⟨targetLabel, middle⟩ := result
    simp only [labeled] at success
    cases targetRan : toCoreExpr expression middle with
    | error => simp [targetRan] at success
    | ok result =>
      obtain ⟨target, after⟩ := result
      simp only [targetRan] at success
      have same := congrArg Prod.fst (Except.ok.inj success)
      exact ⟨targetLabel, _, middle, target, same.symm, ⟨after, targetRan⟩⟩

/-- Lift Boolean expression agreement to the corresponding lowered assumption. -/
theorem interpAssume_execution (procedures : String → Option Core.Procedure)
    (valid : State → Prop) (range : SourceRange)
    (annotations : Ann (Option (BooleDDM.MetadataAnn SourceRange)) SourceRange)
    (label : Ann (Option (BooleDDM.Label SourceRange)) SourceRange)
    (expression : Boole.Expr) (scope final : Scope) (entry after : TranslateState)
    (body : Computation Unit) (raw annotated : List Core.Statement)
    (interpreted : interpStmt denotation (.assume range annotations label expression) scope =
      .ok (body, final))
    (lowered : lowerStatementChunk (.assume range annotations label expression) entry = .ok (raw, after))
    (erased : eraseStatementsAnnotations annotated = eraseStatementsAnnotations raw)
    (expressions : ∀ condition exprEntry target targetAnnotated,
      interpExpr denotation expression scope = .ok (condition, scope) →
      ExpressionWasLowered expression exprEntry target →
      targetAnnotated.eraseTypes = target.eraseTypes →
      ∀ state, valid state → ∃ result, condition state = .ok (.bool result) ∧
        Core.Expression.eval coreRuntimeFactory (coreStore state) targetAnnotated =
          some (if result then Imperative.HasBool.ttVal coreRuntimeFactory
            else Imperative.HasBool.ffVal coreRuntimeFactory)) :
    ExecutionAgreement procedures annotated body valid valid := by
  obtain ⟨_, condition, exprRun, rfl⟩ :=
    interpAssume_origin range annotations label expression scope final body interpreted
  obtain ⟨targetLabel, md, exprEntry, target, rfl, targetRun⟩ :=
    loweredAssume_origin range annotations label expression entry after raw lowered
  rcases annotated with _ | ⟨stmt, rest⟩
  · simp [eraseStatementsAnnotations] at erased
  have restNil : rest = [] := by
    have h := (List.cons.inj erased).2
    cases rest <;> simp_all [eraseStatementsAnnotations]
  subst rest
  have same := (List.cons.inj erased).1
  cases stmt <;> simp [eraseStatementAnnotations] at same
  case cmd command =>
    cases command <;> simp [Core.Command.eraseTypes] at same
    case cmd primitive =>
      cases primitive <;> simp at same
      case assume actualLabel actualCondition actualMetadata =>
        obtain ⟨rfl, condEq, _⟩ := same
        have agreement := expressions _ _ _ _ exprRun targetRun condEq
        apply assumption_executionAgreement
        · intro state ready
          obtain ⟨result, source, _⟩ := agreement state ready
          exact ⟨result, source⟩
        · intro state ready result
          obtain ⟨actual, source, core⟩ := agreement state ready
          exact boolean_execution_iff source core result

end Strata.Boole
