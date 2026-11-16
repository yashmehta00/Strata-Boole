/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all StrataBoole.Boole.Hoare.Compatibility.Body
import all StrataBoole.Boole.Hoare.Compatibility.Condition
import all StrataBoole.Boole.Hoare.Compatibility.Entry
import all StrataBoole.Boole.Hoare.Compatibility.Fragment
import all StrataBoole.Boole.Hoare.Compatibility.Transfer
import all StrataBoole.Boole.Hoare.Compile
import all StrataBoole.Boole.Hoare.Rules
import all StrataBoole.Boole.Interp
import all StrataBoole.Boole.Semantics.Adequacy.SourceInterface
import all StrataBoole.Boole.Semantics.Adequacy.ExpressionExecution
import all StrataBoole.Boole.Semantics.Adequacy.Execution
import all StrataBoole.Boole.Semantics.Adequacy.ExecutionLowering
import all StrataBoole.Verify
import all Strata.Languages.Core.CmdType
import all Strata.Languages.Core.Statement
import all Strata.DL.Imperative.Cmd
import all Strata.DL.Lambda.LExpr

namespace Strata.Boole.Hoare

open StrataDDM Core.TypeSpec Core.Logic Imperative

private def compileElse (alternative : BooleDDM.Else SourceRange) (readOnly : List String) :
    InterpM Compiled :=
  match alternative with
  | .else0 _ => pure { command := .skip }
  | .else1 _ body => block body readOnly

private def lowerElse (alternative : BooleDDM.Else SourceRange) :
    TranslateM Core.Statements :=
  match alternative with
  | .else0 _ => pure []
  | .else1 _ body => toCoreBlock body

private theorem compiled_if_det
    {range guardRange : SourceRange} {annotations} {expression : Boole.Expr}
    {thenBlock : BooleDDM.Block SourceRange} {elseBlock : BooleDDM.Else SourceRange}
    {readOnly : List String} {entry final : Scope} {result : Compiled}
    (built : stmt (.if_statement range annotations (.condDet guardRange expression)
      thenBlock elseBlock) readOnly entry = .ok (result, final)) :
    ∃ (guard : TypedExpr) (yes no : Compiled),
      expr expression {} entry = .ok (guard, entry) ∧
      block thenBlock readOnly entry = .ok (yes, entry) ∧
      compileElse elseBlock readOnly entry = .ok (no, entry) ∧
      final = entry ∧
      result.command = Transformer.branch (some guard.eval) yes.command no.command := by
  rw [stmt.eq_def] at built
  obtain ⟨guardResult, middle, guardRun, rest⟩ := split_run built
  have stable := guardExpr_readOnly (.condDet guardRange expression) _ _ _ guardRun
  subst middle
  have guardRun' : (some <$> boolean guardRange expression) entry = .ok (guardResult, entry) :=
    guardRun
  rw [← bind_pure_comp] at guardRun'
  obtain ⟨guard, mid, booleanRun, done⟩ := split_run guardRun'
  have stable := boolean_readOnly guardRange expression {} _ _ _ booleanRun
  subst mid
  have guardEq : some guard = guardResult := congrArg Prod.fst (Except.ok.inj done)
  subst guardResult
  unfold boolean at booleanRun
  obtain ⟨value, mid, exprRun, expectRun⟩ := split_run booleanRun
  have stable := expr_readOnly expression {} _ _ _ exprRun
  subst mid
  unfold TypedExpr.expect at expectRun
  split at expectRun
  rotate_left
  · contradiction
  have guardEq : value.eval = guard := congrArg Prod.fst (Except.ok.inj expectRun)
  subst guard
  obtain ⟨yes, mid, yesRun, rest⟩ := split_run rest
  have stable := block_readOnly thenBlock readOnly _ _ _ yesRun
  subst mid
  have combined : (compileElse elseBlock readOnly >>= fun no => pure
      { command := Transformer.branch (some value.eval) yes.command no.command
        writes := (yes.writes ++ no.writes).eraseDups }) entry = .ok (result, final) := by
    cases elseBlock <;> exact rest
  obtain ⟨no, mid, noRun, done⟩ := split_run combined
  change compileElse elseBlock readOnly entry = .ok (no, mid) at noRun
  have noStable : mid = entry := by
    cases elseBlock with
    | else0 => exact (congrArg Prod.snd (Except.ok.inj noRun)).symm
    | else1 _ blk => exact block_readOnly blk readOnly _ _ _ noRun
  subst mid
  exact ⟨value, yes, no, exprRun, yesRun, noRun,
    (congrArg Prod.snd (Except.ok.inj done)).symm,
    (congrArg (fun pair : Compiled × Scope => pair.1.command) (Except.ok.inj done)).symm⟩

private theorem lowered_if_det
    {range guardRange : SourceRange} {annotations} {expression : Boole.Expr}
    {thenBlock : BooleDDM.Block SourceRange} {elseBlock : BooleDDM.Else SourceRange}
    {entry final : TranslateState} {raw : Core.Statements}
    (lowered : lowerStatementChunk (.if_statement range annotations (.condDet guardRange expression)
      thenBlock elseBlock) entry = .ok (raw, final)) :
    ∃ (yesRaw noRaw : Core.Statements) (rawGuard : Core.Expression.Expr)
      (afterYes afterNo : TranslateState) (md : Imperative.MetaData Core.Expression),
      withBVars [] (toCoreBlock thenBlock) entry = .ok (yesRaw, afterYes) ∧
      withBVars [] (lowerElse elseBlock) afterYes = .ok (noRaw, afterNo) ∧
      toCoreExpr expression afterNo = .ok (rawGuard, final) ∧
      raw = [.ite (.det rawGuard) yesRaw noRaw md] := by
  simp only [lowerStatementChunk] at lowered
  obtain ⟨rawStmt, afterStmt, stmtRun, done⟩ := split_run lowered
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj done)
  rw [toCoreStmt.eq_def] at stmtRun
  obtain ⟨yesRaw, afterYes, yesRun, rest⟩ := split_run stmtRun
  obtain ⟨noRaw, afterNo, noRun, rest⟩ := split_run rest
  obtain ⟨rawGuard, guardExit, expressionRun, rest⟩ := split_run rest
  unfold toCoreMetaData at rest
  simp only [get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, Except.bind,
    pure, StateT.pure, Except.pure] at rest
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj rest)
  exact ⟨yesRaw, noRaw, rawGuard, afterYes, afterNo, _, yesRun, noRun, expressionRun, rfl⟩

/-- A branch arm restores the lexical scope while retaining the values of
outer slots. Its local declarations can be dropped from the Core post-state. -/
private def BranchArmTransfer (program : Core.Program) (params : InitEnvWFParams)
    (factory : Lambda.Factory Core.CoreLParams) (labels : List String)
    (source : InterpM Compiled) (lower : TranslateM Core.Statements) : Prop :=
  ∀ (entry : CompilerScopes) (after : TranslateState) (compiled : Compiled)
    (raw annotated : Core.Statements) (unwritten remaining : List Core.CoreIdent)
    (nextContext : Core.Expression.TyContext) (nextVariables : TypeScopes),
    source entry.source = .ok (compiled, entry.source) →
    withBVars [] lower entry.lowering = .ok (raw, after) →
    eraseStatementsAnnotations annotated = eraseStatementsAnnotations raw →
    StatementsWellTyped program entry.context entry.variables labels
      annotated nextContext nextVariables →
    coreStatements annotated unwritten = some remaining →
    ScopesAgree entry →
    ScopesAgree {entry with lowering := after} ∧
    BodyTransfer program params factory
      (fun scope unwritten => ScopedStoresAgree scope factory unwritten)
      entry.source entry.source unwritten remaining compiled.command annotated ∧
    ∀ remaining (Q : Assertion), Imperative.Logic.Hoare.PostWF annotated
      (Lift (ScopedStoresAgree entry.source factory remaining) Q)

private theorem branch_transfer
    {program : Core.Program} {params : InitEnvWFParams} {factory : Lambda.Factory Core.CoreLParams}
    {range guardRange : SourceRange} {annotations} {expression : Boole.Expr}
    {thenBlock : BooleDDM.Block SourceRange} {elseBlock : BooleDDM.Else SourceRange}
    {entry final : CompilerScopes} {compiled : Compiled} {readOnly labels : List String}
    {raw annotated : Core.Statements} {unwritten remaining : List Core.CoreIdent}
    (built : stmt (.if_statement range annotations (.condDet guardRange expression)
      thenBlock elseBlock) readOnly entry.source = .ok (compiled, final.source))
    (lowered : lowerStatementChunk (.if_statement range annotations (.condDet guardRange expression)
      thenBlock elseBlock) entry.lowering = .ok (raw, final.lowering))
    (erased : eraseStatementsAnnotations annotated = eraseStatementsAnnotations raw)
    (typed : StatementsWellTyped program entry.context entry.variables labels
      annotated final.context final.variables)
    (gate : coreStatements annotated unwritten = some remaining)
    (aligned : ScopesAgree entry)
    (supported : SupportedCondition expression)
    (addBuiltin : factory["Int.Add"]? = some (Lambda.intAddFunc (T := Core.CoreLParams)).func)
    (geBuiltin : factory["Int.Ge"]? = some (Lambda.intGeFunc (T := Core.CoreLParams)).func)
    (thenTransfer : BranchArmTransfer program params factory labels
      (block thenBlock readOnly) (toCoreBlock thenBlock))
    (elseTransfer : BranchArmTransfer program params factory labels
      (compileElse elseBlock readOnly) (lowerElse elseBlock)) :
    ScopesAgree final ∧ BodyTransfer program params factory
      (fun scope unwritten => ScopedStoresAgree scope factory unwritten)
      entry.source final.source unwritten remaining compiled.command annotated := by
  obtain ⟨guard, yes, no, builtGuard, builtYes, builtNo, sourceScope, sourceBody⟩ :=
    compiled_if_det built
  obtain ⟨yesRaw, noRaw, rawGuard, afterYes, afterNo, rawMD, loweredYes, loweredNo, loweredGuard, rfl⟩ :=
    lowered_if_det lowered
  cases annotated with
  | nil => simp [eraseStatementsAnnotations] at erased
  | cons first tail =>
    cases tail with
    | cons next rest => simp [eraseStatementsAnnotations] at erased
    | nil =>
      have firstEq := (List.cons.inj erased).1
      cases first <;> simp [eraseStatementAnnotations] at firstEq
      case ite cond yesCore noCore md =>
        cases cond <;> simp [ExprOrNondet.map] at firstEq
        case det coreGuard =>
          obtain ⟨guardEq, yesEq, noEq, _⟩ := firstEq
          have typing : ∃ yesContext noContext yesVariables noVariables,
              ExprWellTyped entry.context entry.variables coreGuard .bool ∧
              StatementsWellTyped program entry.context entry.variables labels
                yesCore yesContext yesVariables ∧
              StatementsWellTyped program entry.context entry.variables labels
                noCore noContext noVariables ∧
              final.context = entry.context := by
            generalize final.context = C at typed ⊢
            cases typed with
            | cons _ _ _ _ _ _ _ _ _ head tail =>
              cases head with
              | ite_det =>
                rename_i guardTyped yesTyped noTyped equivalent
                cases tail
                exact ⟨_, _, _, _, guardTyped, yesTyped, noTyped, rfl⟩
          obtain ⟨_, _, _, _, guardTyped, yesTyped, noTyped, finalContext⟩ := typing
          have readable : ready unwritten coreGuard = true := by
            cases readRun : ready unwritten coreGuard with
            | false => simp [coreStatements, coreStatement, readRun] at gate
            | true => rfl
          simp only [coreStatements, coreStatement, readable, Bool.not_true, Bool.false_eq_true,
            ite_false, bind, Option.bind] at gate
          cases yesGate : coreStatements yesCore unwritten with
          | none => simp [yesGate] at gate
          | some yesRemaining =>
            simp only [yesGate] at gate
            cases noGate : coreStatements noCore unwritten with
            | none => simp [noGate] at gate
            | some noRemaining =>
              simp only [noGate] at gate
              have joined : remaining = (yesRemaining ++ noRemaining).eraseDups :=
                (Option.some.inj gate).symm
              obtain ⟨alignedYes, yesTriple, yesScope⟩ :=
                thenTransfer entry afterYes yes yesRaw yesCore unwritten yesRemaining _ _
                  builtYes loweredYes yesEq yesTyped yesGate aligned
              obtain ⟨alignedNo, noTriple, noScope⟩ :=
                elseTransfer {entry with lowering := afterYes} afterNo no noRaw noCore unwritten
                  noRemaining _ _ builtNo loweredNo noEq noTyped noGate alignedYes
              obtain ⟨lowerScope, guardAgrees⟩ :=
                condition_agrees (entry := {entry with lowering := afterNo}) supported alignedNo
                  addBuiltin geBuiltin builtGuard loweredGuard guardEq guardTyped readable
              refine ⟨?_, ?_⟩
              · constructor
                · rw [sourceScope, lowerScope]; exact alignedNo.names
                · rw [sourceScope, lowerScope]; exact alignedNo.binders
                · rw [sourceScope, lowerScope]; exact alignedNo.globals
                · rw [sourceScope, lowerScope]; exact alignedNo.modifies
                · rw [sourceScope]; exact aligned.distinct
                · rw [sourceScope]; exact aligned.validNames
                · rw [finalContext]; exact aligned.builtins
              · intro Q
                rw [sourceScope, sourceBody]
                apply Core.Logic.Hoare.ite program.findProcByString? params
                  _ _ (yesScope remaining (Q none)) (noScope remaining (Q none))
                · apply Core.Logic.Hoare.consequence program.findProcByString? params (yesTriple Q)
                  · rintro env ⟨⟨state, related, pre⟩, cond⟩
                    have evaluates := guard_of_eval (b := true)
                      (fun _ evaluated => ExprAgrees.bool guardAgrees related evaluated) pre cond
                    exact ⟨state, related, by simpa [Transformer.branch, test, Value.bool, evaluates] using pre⟩
                  · rintro env ⟨state, ⟨agrees, fits⟩, post⟩
                    refine ⟨state, ⟨agrees.weaken ?_, fits⟩, post⟩
                    intro id member
                    rw [joined, List.mem_eraseDups]
                    exact List.mem_append_left _ member
                · apply Core.Logic.Hoare.consequence program.findProcByString? params (noTriple Q)
                  · rintro env ⟨⟨state, related, pre⟩, cond⟩
                    have evaluates := guard_of_eval (b := false)
                      (fun _ evaluated => ExprAgrees.bool guardAgrees related evaluated) pre cond
                    exact ⟨state, related, by simpa [Transformer.branch, test, Value.bool, evaluates] using pre⟩
                  · rintro env ⟨state, ⟨agrees, fits⟩, post⟩
                    refine ⟨state, ⟨agrees.weaken ?_, fits⟩, post⟩
                    intro id member
                    rw [joined, List.mem_eraseDups]
                    exact List.mem_append_right _ member

end Strata.Boole.Hoare
