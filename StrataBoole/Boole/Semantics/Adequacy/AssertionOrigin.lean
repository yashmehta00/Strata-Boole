/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.AssertionExecution
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

/-- A successfully interpreted assert denotes its interpreted condition and
leaves the lexical scope unchanged. Source and Core default labels are kept
separate because the two frontends generate them independently. -/
theorem interpAssert_origin (range : SourceRange)
    (annotations : Ann (Option (BooleDDM.MetadataAnn SourceRange)) SourceRange)
    (label : Ann (Option (BooleDDM.Label SourceRange)) SourceRange)
    (expression : Boole.Expr) (scope final : Scope)
    (body : (denotation .builtins).Statement)
    (success : interpStmt (denotation .builtins)
      (.assert range annotations label expression) scope = .ok (body, final)) :
    final = scope ∧
      ∃ condition,
        interpExpr (denotation .builtins) expression scope = .ok (condition, scope) ∧
        ∃ sourceAssertionLabel,
          body = (denotation .builtins).assertion sourceAssertionLabel condition := by
  have annotationNone : annotations.val = none := by
    cases annotation : annotations.val with
    | none => rfl
    | some value =>
      rw [interpStmt.eq_def] at success
      simp [annotation, reject, bind, StateT.bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw, StateT.lift, Function.comp_apply] at success
  simp only [interpStmt.eq_def, annotationNone] at success
  simp only [Option.isSome, Bool.false_eq_true, ite_false,
    bind, StateT.bind, Except.bind] at success
  cases expressionRun : interpExpr (denotation .builtins) expression scope with
  | error error => simp [expressionRun] at success
  | ok result =>
    obtain ⟨condition, middle⟩ := result
    simp only [expressionRun] at success
    have resultEq := Except.ok.inj success
    obtain ⟨bodyEq, finalEq⟩ := Prod.mk.inj resultEq
    have middleEq : middle = scope := interpExpr_readOnly _ _ _ _ _ expressionRun
    refine ⟨finalEq.symm.trans middleEq, condition, ?_, ?_⟩
    · simpa [middleEq] using expressionRun
    · exact ⟨_, by simpa [denotation] using bodyEq.symm⟩

/-- Trace a lowered assertion back to the call that lowered its condition.
The lowering state may have advanced its generated-label counter first. -/
theorem loweredAssert_origin (range : SourceRange)
    (annotations : Ann (Option (BooleDDM.MetadataAnn SourceRange)) SourceRange)
    (label : Ann (Option (BooleDDM.Label SourceRange)) SourceRange)
    (expression : Boole.Expr) (entry final : TranslateState) (raw : List Core.Statement)
    (success : lowerStatementChunk (.assert range annotations label expression) entry =
      .ok (raw, final)) :
    ∃ targetLabel md exprEntry target,
      raw = [Core.Statement.assert targetLabel target md] ∧
      ExpressionWasLowered expression exprEntry target := by
  simp only [lowerStatementChunk] at success
  rw [toCoreStmt] at success
  simp only [toCoreMetaData, bind, StateT.bind, Except.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure] at success
  cases labeled : defaultLabel range "assert" label.val entry with
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

/-- For an actual assertion, two-way execution follows from equal Boolean
evaluation of the two interpretations of its source expression. -/
theorem interpAssert_execution (procedures : String → Option Core.Procedure)
    (valid : State → Prop) (range : SourceRange)
    (annotations : Ann (Option (BooleDDM.MetadataAnn SourceRange)) SourceRange)
    (label : Ann (Option (BooleDDM.Label SourceRange)) SourceRange)
    (expression : Boole.Expr) (scope final : Scope) (entry after : TranslateState)
    (body : Computation (model := .builtins) Unit) (raw annotated : List Core.Statement)
    (interpreted : interpStmt (denotation .builtins) (.assert range annotations label expression) scope =
      .ok (body, final))
    (lowered : lowerStatementChunk (.assert range annotations label expression) entry = .ok (raw, after))
    (erased : eraseStatementsAnnotations annotated = eraseStatementsAnnotations raw)
    (expressions : ∀ condition exprEntry target targetAnnotated,
      interpExpr (denotation .builtins) expression scope = .ok (condition, scope) →
      ExpressionWasLowered expression exprEntry target →
      targetAnnotated.eraseTypes = target.eraseTypes →
      ∀ state, valid state → ∃ result, condition state = .ok (.bool result) ∧
        Core.Expression.eval coreRuntimeFactory (coreStore state) targetAnnotated =
          some (if result then Imperative.HasBool.ttVal coreRuntimeFactory
            else Imperative.HasBool.ffVal coreRuntimeFactory)) :
    ExecutionAgreement procedures annotated body valid valid := by
  obtain ⟨_, condition, exprRun, sourceLabel, rfl⟩ :=
    interpAssert_origin range annotations label expression scope final body interpreted
  obtain ⟨targetLabel, md, exprEntry, target, rfl, targetRun⟩ :=
    loweredAssert_origin range annotations label expression entry after raw lowered
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
      case assert actualLabel actualCondition actualMetadata =>
        obtain ⟨rfl, condEq, _⟩ := same
        have agreement := expressions _ _ _ _ exprRun targetRun condEq
        apply assertion_executionAgreement
        · intro state ready
          obtain ⟨result, source, _⟩ := agreement state ready
          exact ⟨result, source⟩
        · intro state ready result
          obtain ⟨actual, source, core⟩ := agreement state ready
          exact boolean_execution_iff source core result

/-- The complete assertion case for a source Boolean literal, with no
expression-agreement premise. -/
theorem interpLiteralAssert_execution (procedures : String → Option Core.Procedure)
    (valid : State → Prop) (range literalRange : SourceRange)
    (annotations : Ann (Option (BooleDDM.MetadataAnn SourceRange)) SourceRange)
    (label : Ann (Option (BooleDDM.Label SourceRange)) SourceRange)
    (value : Bool) (scope final : Scope) (entry after : TranslateState)
    (body : Computation (model := .builtins) Unit) (raw annotated : List Core.Statement)
    (interpreted : interpStmt (denotation .builtins)
      (.assert range annotations label (if value then .btrue literalRange else .bfalse literalRange)) scope =
      .ok (body, final))
    (lowered : lowerStatementChunk
      (.assert range annotations label (if value then .btrue literalRange else .bfalse literalRange)) entry =
      .ok (raw, after))
    (erased : eraseStatementsAnnotations annotated = eraseStatementsAnnotations raw) :
    ExecutionAgreement procedures annotated body valid valid := by
  apply interpAssert_execution _ _ _ _ _ _ _ _ _ _ _ _ _ interpreted lowered erased
  intro condition expressionEntry target targetAnnotated ran sourceLowered same state _
  exact ⟨value, booleanLiteral_execution literalRange value ran sourceLowered same state⟩

end Strata.Boole
