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

private def RawReadOnly (action : TranslateM α) : Prop :=
  ∀ entry value final, action entry = .ok (value, final) → final = entry

private theorem rawReadOnly_pure (value : α) : RawReadOnly (pure value) :=
  fun _ _ _ ran => (congrArg Prod.snd (Except.ok.inj ran)).symm

private theorem rawReadOnly_bind {action : TranslateM α} {next : α → TranslateM β}
    (first : RawReadOnly action) (rest : ∀ value, RawReadOnly (next value)) :
    RawReadOnly (action >>= next) := by
  intro entry value final ran
  obtain ⟨midValue, middle, firstRan, restRan⟩ := split_run ran
  exact (rest midValue _ _ _ restRan).trans (first _ _ _ firstRan)

private theorem rawReadOnly_mapM {items : List α} {action : α → TranslateM β}
    (preserves : ∀ item ∈ items, RawReadOnly (action item)) :
    RawReadOnly (items.mapM action) := by
  induction items with
  | nil => exact rawReadOnly_pure []
  | cons head tail ih =>
    rw [List.mapM_cons]
    exact rawReadOnly_bind (preserves _ List.mem_cons_self) fun value =>
      rawReadOnly_bind (ih (fun item member => preserves item (List.mem_cons_of_mem _ member)))
        fun values => rawReadOnly_pure (value :: values)

private theorem rawReadOnly_throw (range : SourceRange) (message : String) :
    RawReadOnly (throwAt range message : TranslateM α) := by
  intro _ _ _ ran
  simp [throwAt, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
    throw, throwThe, MonadExceptOf.throw, StateT.lift, pure, Except.pure] at ran

private theorem rawReadOnly_getFVarName (range : SourceRange) (index : Nat) :
    RawReadOnly (getFVarName range index) := by
  intro entry value final ran
  cases found : entry.gctx.nameOf? index <;>
    simp_all [getFVarName, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.pure, throwAt, throw, throwThe,
      MonadExceptOf.throw, StateT.lift]

private theorem rawReadOnly_getTypeBVarName (range : SourceRange) (index : Nat) :
    RawReadOnly (getTypeBVarName range index) := by
  intro entry value final ran
  by_cases bound : index < entry.tyBVars.size
  · cases found : entry.tyBVars[entry.tyBVars.size - index - 1]? <;>
      simp_all [getTypeBVarName, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, Except.pure, throwAt, throw, throwThe,
        MonadExceptOf.throw, StateT.lift]
  · simp_all [getTypeBVarName, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, Except.pure, throwAt, throw, throwThe, MonadExceptOf.throw, StateT.lift]

private theorem rawReadOnly_monoType (t : Boole.Type) : RawReadOnly (toCoreMonoType t) := by
  fun_induction toCoreMonoType t
  all_goals try exact rawReadOnly_pure _
  case case1 =>
    exact rawReadOnly_bind (rawReadOnly_getTypeBVarName _ _) fun _ => rawReadOnly_pure _
  case case3 range index args ih =>
    have nested : RawReadOnly (args.mapM toCoreMonoType) := by
      rw [Array.mapM_eq_mapM_toList]
      have listed : RawReadOnly (args.toList.mapM toCoreMonoType) :=
        rawReadOnly_mapM (fun t ht => ih t (by simpa using ht))
      rw [← bind_pure_comp]
      exact rawReadOnly_bind listed fun _ => rawReadOnly_pure _
    exact rawReadOnly_bind (rawReadOnly_getFVarName range index) fun _ =>
      rawReadOnly_bind nested fun _ => rawReadOnly_pure _
  case case4 _ _ _ first second =>
    exact rawReadOnly_bind first fun _ => rawReadOnly_bind second fun _ => rawReadOnly_pure _
  case case14 _ _ _ first second =>
    exact rawReadOnly_bind first fun _ => rawReadOnly_bind second fun _ => rawReadOnly_pure _
  case case15 _ _ inner =>
    exact rawReadOnly_bind inner fun _ => rawReadOnly_pure _
  case case17 => exact rawReadOnly_throw _ _

private theorem rawReadOnly_type (ty : Boole.Type) : RawReadOnly (toCoreType ty) :=
  rawReadOnly_bind (rawReadOnly_monoType ty) fun _ => rawReadOnly_pure _

set_option linter.unusedSimpArgs false in
/-- Transfer the actual deterministic initializer after proving agreement on its RHS. -/
private theorem initializer_transfer
    {program : Core.Program} {params : InitEnvWFParams} {factory : Lambda.Factory Core.CoreLParams}
    {range : SourceRange} {annotations : Ann (Option (BooleDDM.MetadataAnn SourceRange)) SourceRange}
    {ty : Boole.Type} {name : Ann String SourceRange} {expression : Boole.Expr}
    {entry final : CompilerScopes} {compiled : Compiled} {readOnly labels : List String}
    {raw annotated : Core.Statements} {unwritten remaining : List Core.CoreIdent}
    (built : stmt (.initStatement range annotations ty name expression) readOnly entry.source =
      .ok (compiled, final.source))
    (lowered : lowerStatementChunk (.initStatement range annotations ty name expression) entry.lowering =
      .ok (raw, final.lowering))
    (erased : eraseStatementsAnnotations annotated = eraseStatementsAnnotations raw)
    (typed : StatementsWellTyped program entry.context entry.variables labels
      annotated final.context final.variables)
    (gate : coreStatements annotated unwritten = some remaining)
    (aligned : ScopesAgree entry)
    (rhs : ∀ value rhsExit rawExpr target monotype,
      expr expression {} entry.source = .ok (value, entry.source) →
      toCoreExpr expression entry.lowering = .ok (rawExpr, rhsExit) →
      target.eraseTypes = rawExpr.eraseTypes →
      ExprWellTyped entry.context entry.variables target monotype →
      ready unwritten target = true →
      rhsExit = entry.lowering ∧
        ExprAgrees (ScopedStoresAgree entry.source factory unwritten) value.eval target) :
    ScopesAgree final ∧ BodyTransfer program params factory
      (fun scope unwritten => ScopedStoresAgree scope factory unwritten)
      entry.source final.source unwritten remaining compiled.command annotated := by
  rw [stmt.eq_def] at built
  obtain ⟨value, sourceMid, sourceRhs, rest⟩ := split_run built
  have same := expr_readOnly _ _ _ _ _ sourceRhs
  subst sourceMid
  obtain ⟨binding, sourceEnd, added, initialized⟩ := split_run rest
  have namesBefore : ValidNames (entry.source.globals ++ entry.source.locals) := by
    refine ⟨?_, fun b hb => aligned.validNames b (by simpa [List.mem_append, or_comm] using hb)⟩
    exact (List.Perm.nodup_iff (List.Perm.map _ List.perm_append_comm)).mp aligned.distinct
  obtain ⟨bindingName, extended, namesAfter⟩ := addLocal_names namesBefore added
  obtain ⟨eval, evalEnd, expected, done⟩ := split_run initialized
  unfold TypedExpr.expect at expected
  split at expected
  rotate_left
  · contradiction
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj expected)
  have sourceScope : final.source = {entry.source with locals := entry.source.locals ++ [binding]} :=
    (congrArg Prod.snd (Except.ok.inj done)).symm.trans extended
  have sourceBody : compiled.command = Transformer.step (Transformer.initState binding value.eval) :=
    (congrArg (fun result : Compiled × Scope => result.1.command) (Except.ok.inj done)).symm
  have finalNames : ValidNames (final.source.globals ++ final.source.locals) := by
    rw [sourceScope, ← extended]
    exact namesAfter
  simp only [lowerStatementChunk] at lowered
  rw [toCoreStmt] at lowered
  simp only [toCoreMetaData, bind, StateT.bind, Except.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure] at lowered
  cases rawRun : toCoreExpr expression entry.lowering with
  | error => simp [rawRun] at lowered
  | ok pair =>
    obtain ⟨rawExpr, rhsExit⟩ := pair
    simp only [rawRun, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.pure, Except.pure] at lowered
    let withBinder := { rhsExit with bvars := rhsExit.bvars.push (.fvar () (mkIdent name.val) none) }
    cases typeRun : toCoreType ty withBinder with
    | error =>
      change toCoreType ty { rhsExit with bvars := rhsExit.bvars.push (.fvar () (mkIdent name.val) none) } = _ at typeRun
      simp [typeRun] at lowered
    | ok pair =>
      obtain ⟨rawType, rawExit⟩ := pair
      have same := rawReadOnly_type ty _ _ _ typeRun
      change toCoreType ty { rhsExit with bvars := rhsExit.bvars.push (.fvar () (mkIdent name.val) none) } = _ at typeRun
      simp only [typeRun] at lowered
      obtain ⟨rfl, loweringEnd⟩ := Prod.mk.inj (Except.ok.inj lowered)
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
              case init id targetTy init md =>
                cases init <;> simp [Imperative.ExprOrNondet.map] at headEq
                case det target =>
                  obtain ⟨rfl, _, exprEq, _⟩ := headEq
                  have gateResult : ready unwritten target = true ∧ remaining = unwritten := by
                    by_cases ok : ready unwritten target = true <;>
                      simp [coreStatements, coreStatement, ok, bind, Option.bind] at gate
                    exact ⟨ok, gate.symm⟩
                  cases typed with
                  | cons _ _ _ _ _ _ _ _ _ first second =>
                    cases first with
                    | cmd _ _ _ _ _ extendedTyped =>
                      cases extendedTyped with
                      | cmd _ _ primitiveTyped =>
                        cases primitiveTyped with
                        | init_det =>
                          have finalContext : final.context = entry.context := by
                            generalize final.context = C at second ⊢
                            cases second
                            rfl
                          obtain ⟨stable, agrees⟩ := rhs value rhsExit rawExpr target _
                            sourceRhs rawRun exprEq (by assumption) gateResult.1
                          have rawScope : final.lowering = {entry.lowering with
                              bvars := entry.lowering.bvars.push (.fvar () (mkIdent name.val) none) } := by
                            rw [← loweringEnd, same]
                            simp [withBinder, stable]
                          refine ⟨?_, ?_⟩
                          · constructor
                            · rw [sourceScope, rawScope]; exact aligned.names
                            · rw [sourceScope, rawScope]
                              change entry.lowering.bvars.push (.fvar () (mkIdent name.val) none) = _
                              rw [aligned.binders]
                              simp only [← List.push_toArray, Array.map_push, bindingName, mkIdent]
                            · rw [sourceScope, rawScope]; exact aligned.globals
                            · rw [sourceScope, rawScope]; exact aligned.modifies
                            · exact (List.Perm.nodup_iff (List.Perm.map _ List.perm_append_comm)).mp finalNames.1
                            · intro b hb
                              exact finalNames.2 b (by simpa [List.mem_append, or_comm] using hb)
                            · rw [finalContext]; exact aligned.builtins
                          · intro Q
                            rw [sourceBody, sourceScope, gateResult.2]
                            have triple := transfer_scalar_init (π := program.findProcByString?)
                              (params := params) unwritten entry.source binding value.eval target
                              targetTy md (Q none) agrees
                            simp only [bindingName, Core.Statement.init] at triple
                            apply Core.Logic.Hoare.consequence program.findProcByString? params triple
                            · exact fun _ h => h
                            · rintro env ⟨state, related, holds⟩
                              exact ⟨state, ⟨related.1.weaken (fun id hd => (List.mem_filter.mp hd).1), related.2⟩,
                                holds⟩

end Strata.Boole.Hoare
