/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all StrataBoole.Boole.Hoare.Compatibility.Body
import all StrataBoole.Boole.Hoare.Compile
import all StrataBoole.Boole.Hoare.Compatibility.Expressions
import all StrataBoole.Boole.Semantics.Adequacy.SourceInterface
import all StrataBoole.Boole.Semantics.Adequacy.SourceFreshness
import all Strata.Languages.Core.CmdType
import all Strata.DL.Lambda.LExpr
import all StrataBoole.Boole.Semantics.Adequacy.AssignmentOrigin
import all StrataBoole.Boole.Interp
import all Strata.Languages.Core.Statement
import all Strata.DL.Imperative.Cmd
import all StrataBoole.Boole.Hoare.Rules
import all StrataBoole.Boole.Hoare.Compatibility.Fragment
import all StrataBoole.Boole.Hoare.Compatibility.Transfer
import StrataBoole.Boole.Semantics.Adequacy.ExecutionLowering
import StrataBoole.Boole.Semantics.Adequacy.ExecutionScopes
import all StrataBoole.Boole.Semantics.Adequacy.Execution
import all StrataBoole.Boole.Semantics.Adequacy.ExecutionInvariant
import all Strata.DL.Imperative.Logic.HoareTemplate
import all StrataBoole.Verify

namespace Strata.Boole.Hoare

open StrataDDM Core.TypeSpec Core.Logic Imperative

private theorem assumption_transfer
    {program : Core.Program} {params : InitEnvWFParams} {factory : Lambda.Factory Core.CoreLParams}
    {range : SourceRange} {annotations : Ann (Option (BooleDDM.MetadataAnn SourceRange)) SourceRange}
    {label : Ann (Option (BooleDDM.Label SourceRange)) SourceRange} {expression : Boole.Expr}
    {entry final : CompilerScopes} {compiled : Compiled} {readOnly labels : List String}
    {raw annotated : Core.Statements} {unwritten remaining : List Core.CoreIdent}
    (built : stmt (.assume range annotations label expression) readOnly entry.source =
      .ok (compiled, final.source))
    (lowered : lowerStatementChunk (.assume range annotations label expression) entry.lowering =
      .ok (raw, final.lowering))
    (erased : eraseStatementsAnnotations annotated = eraseStatementsAnnotations raw)
    (typed : StatementsWellTyped program entry.context entry.variables labels
      annotated final.context final.variables)
    (gate : coreStatements annotated unwritten = some remaining)
    (aligned : ScopesAgree entry)
    (condition : ∀ value (exprEntry exprExit : TranslateState) rawExpr target,
      expr expression {} entry.source = .ok (value, entry.source) →
      toCoreExpr expression exprEntry = .ok (rawExpr, exprExit) →
      target.eraseTypes = rawExpr.eraseTypes →
      ExprWellTyped entry.context entry.variables target .bool →
      ready unwritten target = true →
      ScopesAgree {entry with lowering := exprEntry} →
      exprExit = exprEntry ∧
        ExprAgrees (ScopedStoresAgree entry.source factory unwritten) value.eval target) :
    ScopesAgree final ∧ BodyTransfer program params factory
      (fun scope unwritten => ScopedStoresAgree scope factory unwritten)
      entry.source final.source unwritten remaining compiled.command annotated := by
  rw [stmt.eq_def] at built
  obtain ⟨guard, sourceMid, compiledGuard, done⟩ := split_run built
  unfold boolean at compiledGuard
  obtain ⟨value, sourceExpressionExit, sourceRun, expect⟩ := split_run compiledGuard
  have sourceEntryEq := expr_readOnly _ _ _ _ _ sourceRun
  subst sourceExpressionExit
  unfold TypedExpr.expect at expect
  split at expect
  rotate_left
  · contradiction
  obtain ⟨guardEq, sourceMidEq⟩ := Prod.mk.inj (Except.ok.inj expect)
  subst guard
  subst sourceMid
  have sourceScope : final.source = entry.source := (congrArg Prod.snd (Except.ok.inj done)).symm
  have sourceBody : compiled.command = Transformer.assumption value.eval :=
    (congrArg (fun result : Compiled × Scope => result.1.command) (Except.ok.inj done)).symm
  simp only [lowerStatementChunk] at lowered
  rw [toCoreStmt] at lowered
  simp only [toCoreMetaData, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
    StateT.get, pure, StateT.pure, Except.pure] at lowered
  cases named : defaultLabel range "assume" label.val entry.lowering with
  | error => simp [named] at lowered
  | ok pair =>
    obtain ⟨targetLabel, middle⟩ := pair
    simp only [named] at lowered
    cases rawRun : toCoreExpr expression middle with
    | error => simp [rawRun] at lowered
    | ok pair =>
      obtain ⟨rawExpr, rawEnd⟩ := pair
      simp only [rawRun] at lowered
      obtain ⟨rfl, rawEndEq⟩ := Prod.mk.inj (Except.ok.inj lowered)
      have onlyCounter : middle = {entry.lowering with labelCounter := middle.labelCounter} := by
        cases labelValue : label.val with
        | none =>
          simp only [defaultLabel, labelValue, bind, StateT.bind, Except.bind, get, getThe,
            MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet,
            StateT.modifyGet, pure, StateT.pure, Except.pure] at named
          obtain ⟨_, rfl⟩ := Prod.mk.inj (Except.ok.inj named)
          rfl
        | some labelAst =>
          cases labelAst
          simp only [defaultLabel, labelValue, pure, StateT.pure, Except.pure] at named
          obtain ⟨_, rfl⟩ := Prod.mk.inj (Except.ok.inj named)
          rfl
      have middleAligned : ScopesAgree {entry with lowering := middle} := by
        rw [onlyCounter]
        exact ⟨aligned.names, aligned.binders, aligned.globals, aligned.modifies,
          aligned.distinct, aligned.validNames, aligned.builtins⟩
      cases annotated with
      | nil => simp [eraseStatementsAnnotations] at erased
      | cons head tail =>
        cases tail with
        | cons next rest => simp [eraseStatementsAnnotations] at erased
        | nil =>
          have headEq := (List.cons.inj erased).1
          cases head <;> simp [eraseStatementAnnotations] at headEq
          case cmd cmd =>
            cases cmd <;> simp [Core.Command.eraseTypes] at headEq
            case cmd primitive =>
              cases primitive <;> simp at headEq
              case assume coreLabel target md =>
                obtain ⟨_, exprEq, _⟩ := headEq
                have gateResult : ready unwritten target = true ∧ remaining = unwritten := by
                  by_cases readOK : ready unwritten target = true <;>
                    simp [coreStatements, coreStatement, readOK, bind, Option.bind] at gate
                  exact ⟨readOK, gate.symm⟩
                have targetTyped : ExprWellTyped entry.context entry.variables target .bool := by
                  cases typed
                  rename_i first _
                  cases first
                  rename_i extended
                  cases extended
                  rename_i primitive
                  cases primitive
                  assumption
                obtain ⟨rawScope, actual⟩ :=
                  condition value middle rawEnd rawExpr target sourceRun rawRun exprEq targetTyped
                    gateResult.1 middleAligned
                have same : final.lowering = {entry.lowering with labelCounter := final.lowering.labelCounter} := by
                  rw [← rawEndEq, rawScope]
                  exact onlyCounter
                have finalContext : final.context = entry.context := by
                  generalize final.context = C at typed ⊢
                  cases typed with
                  | cons _ _ _ _ _ _ _ _ _ first second =>
                    cases first
                    cases second
                    rfl
                refine ⟨?_, ?_⟩
                · constructor
                  · rw [sourceScope, same]; exact aligned.names
                  · rw [sourceScope, same]; exact aligned.binders
                  · rw [sourceScope, same]; exact aligned.globals
                  · rw [sourceScope, same]; exact aligned.modifies
                  · rw [sourceScope]; exact aligned.distinct
                  · rw [sourceScope]; exact aligned.validNames
                  · rw [finalContext]; exact aligned.builtins
                · intro Q
                  rw [sourceScope, sourceBody, gateResult.2]
                  have triple := transfer_assume (π := program.findProcByString?) (params := params)
                    (factory := factory) (entry := ScopedStoresAgree entry.source factory unwritten)
                    coreLabel value.eval target md (Q none)
                    (fun _ _ related => related.1.factory_eq)
                    (fun _ _ related _ evaluated => ExprAgrees.bool actual related evaluated)
                  simpa only [Transformer.assumption, Core.Statement.assume] using triple

end Strata.Boole.Hoare
