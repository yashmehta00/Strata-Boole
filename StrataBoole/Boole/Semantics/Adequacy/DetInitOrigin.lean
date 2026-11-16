/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.DetDeclarationExecution
import all Strata.Languages.Core.Statement
import all Strata.DL.Imperative.Cmd
import all StrataBoole.Boole.Semantics.Adequacy.Lowering
import all StrataBoole.Boole.Semantics.Adequacy.ExecutionLowering
import all StrataBoole.Verify
import all StrataBoole.Boole.Interp
import all StrataBoole.Boole.Semantics.Semantics
import all StrataBoole.Boole.Semantics.Adequacy.SourceInterface
import all StrataBoole.Boole.Semantics.Adequacy.SourceFreshness
import all StrataDDM.AST

public section

namespace Strata.Boole
open StrataDDM

/-- A successfully lowered deterministic initialization emits one Core init
statement, and its RHS is the result of lowering the source initializer. -/
theorem loweredInit_origin (range : SourceRange)
    (annotations : Ann (Option (BooleDDM.MetadataAnn SourceRange)) SourceRange)
    (ty : Boole.Type) (name : Ann String SourceRange)
    (expression : Boole.Expr) (entry final : TranslateState) (raw : List Core.Statement)
    (success : lowerStatementChunk (.initStatement range annotations ty name expression) entry =
      .ok (raw, final)) :
    ∃ target targetTy md,
      raw = [Core.Statement.init ⟨name.val, ()⟩ targetTy (.det target) md] ∧
      ExpressionWasLowered expression entry target := by
  simp only [lowerStatementChunk] at success
  rw [toCoreStmt] at success
  simp only [toCoreMetaData, bind, StateT.bind, Except.bind, pure, StateT.pure,
    Except.pure] at success
  cases targetRun : toCoreExpr expression entry with
  | error error => simp [targetRun] at success
  | ok result =>
    obtain ⟨target, exprEntry⟩ := result
    simp only [targetRun] at success
    let afterBinders := { exprEntry with
      bvars := exprEntry.bvars.push (.fvar () (mkIdent name.val) none) }
    simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at success
    have hstate : ({ exprEntry with
      bvars := exprEntry.bvars.push (.fvar () (mkIdent name.val) none) }) = afterBinders := rfl
    rw [hstate] at success
    cases typeRun : toCoreType ty afterBinders with
    | error error => simp [typeRun] at success
    | ok result =>
      obtain ⟨targetTy, afterTy⟩ := result
      simp only [typeRun, get, getThe, MonadStateOf.get, StateT.get] at success
      have rawEq := congrArg Prod.fst (Except.ok.inj success)
      exact ⟨target, targetTy, _, rawEq.symm, ⟨exprEntry, targetRun⟩⟩

/-- Recover the interpreted initializer and the binding it adds to the
procedure scope, from the successful statement traversal. -/
theorem interpInit_origin (range : SourceRange)
    (annotations : Ann (Option (BooleDDM.MetadataAnn SourceRange)) SourceRange)
    (ty : Boole.Type) (name : Ann String SourceRange) (expression : Boole.Expr)
    {entry final : Scope} {body : Computation (model := .builtins) Unit}
    (distinct : ((entry.globals ++ entry.locals).map Binding.name).Nodup)
    (noSpaces : ∀ b ∈ entry.globals ++ entry.locals, b.name.contains ' ' = false)
    (success : interpStmt (denotation .builtins) (.initStatement range annotations ty name expression)
      entry = .ok (body, final)) :
    ∃ initializer binding,
      interpExpr (denotation .builtins) expression entry = .ok (initializer, entry) ∧
      binding.name = name.val ∧ final = { entry with locals := entry.locals ++ [binding] } ∧
      body = Computation.declare binding (some initializer) := by
  rw [interpStmt] at success
  obtain ⟨initializer, middle, first, rest⟩ := split_run success
  have same := interpExpr_readOnly _ _ _ _ _ first
  subst middle
  obtain ⟨binding, next, added, done⟩ := split_run rest
  have ⟨named, nextEq, _⟩ := addLocal_names ⟨distinct, noSpaces⟩ added
  have result := Except.ok.inj done
  exact ⟨initializer, binding, first, named,
    (congrArg Prod.snd result).symm.trans nextEq, (congrArg Prod.fst result).symm⟩

/-- Execute a deterministic initializer from the actual source and Core
traversals. The initializer premise supplies agreement on its value and the
fresh slot, and the preservation premise establishes the extended invariant. -/
theorem interpInit_execution
    (procedures : String → Option Core.Procedure)
    (range : SourceRange)
    (annotations : Ann (Option (BooleDDM.MetadataAnn SourceRange)) SourceRange)
    (ty : Boole.Type) (name : Ann String SourceRange) (expression : Boole.Expr)
    {entry final : Scope} {before after : TranslateState}
    {body : Computation (model := .builtins) Unit} {raw annotated : List Core.Statement}
    (entryValid returnValid : State → Prop)
    (distinct : ((entry.globals ++ entry.locals).map Binding.name).Nodup)
    (noSpaces : ∀ b ∈ entry.globals ++ entry.locals, b.name.contains ' ' = false)
    (interpreted : interpStmt (denotation .builtins)
      (.initStatement range annotations ty name expression) entry = .ok (body, final))
    (lowered : lowerStatementChunk (.initStatement range annotations ty name expression) before =
      .ok (raw, after))
    (erased : eraseStatementsAnnotations annotated = eraseStatementsAnnotations raw)
    (initializerFacts : ∀ initializer binding rawInit coreInit coreTy,
      interpExpr (denotation .builtins) expression entry = .ok (initializer, entry) →
      ExpressionWasLowered expression before rawInit →
      coreInit.eraseTypes = rawInit.eraseTypes →
      binding.name = name.val →
      final = { entry with locals := entry.locals ++ [binding] } →
      body = Computation.declare binding (some initializer) →
      (∀ state, entryValid state → ∃ value literal,
        state.locals.lookup binding.name = none ∧
        coreStore state ⟨binding.name, ()⟩ = none ∧
        initializer state = .ok value ∧ value.sort = binding.sort ∧
        coreValue? value = some literal ∧
        Imperative.HasVal.valueOfTy (P := Core.Expression) coreRuntimeFactory literal coreTy ∧
        Core.Expression.eval coreRuntimeFactory (coreStore state) coreInit = some literal) ∧
      (∀ state value, entryValid state → value.sort = binding.sort →
        returnValid { state with locals := state.locals ++ [(binding.name, value)] })) :
    ExecutionAgreement procedures annotated body entryValid returnValid := by
  obtain ⟨initializer, binding, exprRun, named, scopeEq, bodyEq⟩ :=
    interpInit_origin range annotations ty name expression distinct noSpaces interpreted
  obtain ⟨target, targetTy, md, rfl, targetRun⟩ :=
    loweredInit_origin range annotations ty name expression before after raw lowered
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
      case init id declared init actualMd =>
        cases init <;> simp [Imperative.ExprOrNondet.map] at same
        case det coreInit =>
          obtain ⟨idEq, typeEq, exprEq, _⟩ := same
          have ⟨facts, keeps⟩ :=
            initializerFacts _ _ _ _ declared exprRun targetRun exprEq named scopeEq bodyEq
          rw [bodyEq]
          have idBinding : id = (⟨binding.name, ()⟩ : Core.CoreIdent) := by
            rw [idEq, named]
          rw [idBinding]
          exact deterministicDeclaration_executionAgreement _ _ _ _ _ _ _ _ facts keeps

end Strata.Boole
