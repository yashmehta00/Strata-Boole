/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all StrataBoole.Boole.Hoare.Compatibility.Body
import all StrataBoole.Boole.Hoare.Compatibility.Expressions
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
import Strata.Languages.Core.IntEvalProps

namespace Strata.Boole.Hoare

open StrataDDM Core.TypeSpec Core.Logic Imperative

private theorem lowerIntGe_parts
    {range typeRange : SourceRange} {left right : Boole.Expr}
    {entry final : TranslateState} {raw : Core.Expression.Expr}
    (lowered : toCoreExpr (.ge range (.int typeRange) left right) entry =
      .ok (raw, final)) :
    ∃ middle leftRaw rightRaw, toCoreExpr left entry = .ok (leftRaw, middle) ∧
      toCoreExpr right middle = .ok (rightRaw, final) ∧
      raw = .app () (.app () (.op () ⟨"Int.Ge", ()⟩ none) leftRaw) rightRaw := by
  rw [toCoreExpr.eq_def] at lowered
  simp only [toCoreQuantExpr?, bind, StateT.bind, Except.bind] at lowered
  cases leftRun : toCoreExpr left entry with
  | error e => simp [leftRun] at lowered
  | ok p =>
    rcases p with ⟨leftRaw', middle⟩
    simp only [leftRun] at lowered
    cases rightRun : toCoreExpr right middle with
    | error e => simp [rightRun] at lowered
    | ok q =>
      rcases q with ⟨rightRaw', after⟩
      simp only [rightRun, toCoreTypedBin, mkCoreApp, Lambda.LExpr.mkApp,
        pure, StateT.pure, Except.pure] at lowered
      have pairEq := Except.ok.inj lowered
      have stateEq := congrArg Prod.snd pairEq
      cases stateEq
      have rawEq : (.app () (.app () (.op () ⟨"Int.Ge", ()⟩ none) leftRaw') rightRaw' :
          Core.Expression.Expr) = raw := congrArg Prod.fst pairEq
      exact ⟨middle, leftRaw', rightRaw', rfl, rightRun, rawEq.symm⟩


private theorem compiled_int_ge
    {range typeRange : SourceRange} {left right : Boole.Expr}
    {context : ReadContext} {scope after : Scope} {value : TypedExpr}
    (built : expr (.ge range (.int typeRange) left right) context scope =
      .ok (value, after)) :
    ∃ lhs rhs, expr left context scope = .ok (lhs, scope) ∧
      expr right context scope = .ok (rhs, scope) ∧
      lhs.sort = .int ∧ rhs.sort = .int ∧
      value.sort = .bool ∧ value.eval = binary .ge lhs.eval rhs.eval := by
  rw [expr.eq_def] at built
  obtain ⟨sort, next, sorted, rest⟩ := split_run built
  have nextEq := sourceSort_readOnly _ _ _ _ sorted
  subst next
  have sortEq : sort = .int := by
    rw [sourceSort] at sorted
    simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
      get, getThe, MonadStateOf.get, StateT.get] at sorted
    split at sorted
    · obtain ⟨_, _, fail, _⟩ := split_run sorted
      contradiction
    · exact (congrArg Prod.fst (Except.ok.inj sorted)).symm
  subst sort
  change ((expr left context >>= fun lhs => expr right context >>= fun rhs =>
    typedBinary range .ge .bool .int lhs rhs) scope) = .ok (value, after) at rest
  obtain ⟨lhs, mid, first, rest⟩ := split_run rest
  have midEq := expr_readOnly _ _ _ _ _ first
  subst mid
  obtain ⟨rhs, mid, second, rest⟩ := split_run rest
  have midEq := expr_readOnly _ _ _ _ _ second
  subst mid
  unfold typedBinary at rest
  obtain ⟨a, mid, matchesLeft, rest⟩ := split_run rest
  obtain ⟨b, last, matchesRight, done⟩ := split_run rest
  unfold TypedExpr.expect at matchesLeft matchesRight
  split at matchesLeft
  · rename_i lhsSort
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj matchesLeft)
    split at matchesRight
    · rename_i rhsSort
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj matchesRight)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj done)
      exact ⟨lhs, rhs, first, second, beq_iff_eq.mp lhsSort, beq_iff_eq.mp rhsSort, rfl, rfl⟩
    · contradiction
  · contradiction

private theorem typed_intGe_origin {context : Core.Expression.TyContext}
    {scopes : Core.TypeSpec.TypeScopes} {annotated left right : Core.Expression.Expr}
    {ty : Lambda.LMonoTy}
    (typed : Core.TypeSpec.ExprWellTyped context scopes annotated ty)
    (signature : context.functions["Int.Ge"]? = some (Lambda.intGeFunc (T := Core.CoreLParams)).func)
    (erased : annotated.eraseTypes =
      (.app () (.app () (.op () ⟨"Int.Ge", ()⟩ none) left) right : Core.Expression.Expr).eraseTypes) :
    ∃ a b, annotated = .app () (.app () Core.intGeOp a) b ∧
      a.eraseTypes = left.eraseTypes ∧ b.eraseTypes = right.eraseTypes := by
  cases annotated <;> simp [Lambda.LExpr.eraseTypes] at erased
  case app md fn b =>
    cases md
    obtain ⟨fnSame, bSame⟩ := erased
    have appTyped := typed.1
    have ⟨domainB, fnTyped⟩ : ∃ domainB, Lambda.LExpr.HasTypeA [] fn (.arrow domainB ty) := by
      cases appTyped with | app f _ => exact ⟨_, f⟩
    cases fn <;> simp [Lambda.LExpr.eraseTypes] at fnSame
    case app md inner a =>
      cases md
      obtain ⟨innerSame, aSame⟩ := fnSame
      have ⟨domainA, innerTyped⟩ :
          ∃ domainA, Lambda.LExpr.HasTypeA [] inner (.arrow domainA (.arrow domainB ty)) := by
        cases fnTyped with | app f _ => exact ⟨_, f⟩
      cases inner <;> simp [Lambda.LExpr.eraseTypes] at innerSame
      case op md id annotation =>
        cases md
        subst id
        have annotationEq : annotation = some (.arrow domainA (.arrow domainB ty)) := by
          cases innerTyped
          rfl
        rw [annotationEq] at typed
        have same := operatorAnnotation_eq (id := ⟨"Int.Ge", ()⟩)
          (annotation := .arrow domainA (.arrow domainB ty)) typed.2.2
          (by simp [Lambda.LExpr.opAnnots]) signature
          (declared := Lambda.LMonoTy.arrow .int (.arrow .int .bool)) (by rfl) (by rfl)
        rw [annotationEq, same]
        exact ⟨a, b, rfl, aSame, bSame⟩

private theorem typed_int_ge_operands
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    {lhs rhs : Core.Expression.Expr} {ty : Lambda.LMonoTy}
    (typed : Core.TypeSpec.ExprWellTyped context scopes
      (.app () (.app () Core.intGeOp lhs) rhs) ty) :
    Core.TypeSpec.ExprWellTyped context scopes lhs .int ∧
      Core.TypeSpec.ExprWellTyped context scopes rhs .int := by
  have types : Lambda.LExpr.HasTypeA [] lhs .int ∧ Lambda.LExpr.HasTypeA [] rhs .int := by
    have derivation := typed.1
    cases derivation with
    | app fn argument =>
      cases fn with
      | app operator left =>
        cases operator
        exact ⟨left, argument⟩
  refine ⟨⟨types.1, ?_, ?_⟩, typed_app_argument typed types.2⟩
  · intro ann present
    apply typed.2.1
    simp [Lambda.LExpr.binderAnnotations, present]
  · constructor
    · intro x ann present
      apply typed.2.2.fvarsDeclared
      simp [Lambda.LExpr.freeVars, present]
    · intro op ty present
      apply typed.2.2.opsInstantiate
      simp [Lambda.LExpr.opAnnots, present]
    · intro op present
      apply typed.2.2.opsKnown
      simp [Lambda.LExpr.getOps, present]

private def BoolObservation (rel : State → Env Core.Expression → Prop)
    (source : Expression) (target : Core.Expression.Expr) : Prop :=
  ∀ state env, rel state env →
    ∃ b : Bool, source state = .ok (.bool b) ∧
      Core.Expression.eval env.factory env.store target = some (.ofBool env.factory.model.tcInterp b)

private theorem BoolObservation.agrees
    {rel : State → Env Core.Expression → Prop} {source : Expression} {target : Core.Expression.Expr}
    (evaluates : BoolObservation rel source target) : ExprAgrees rel source target := by
  intro state env value related success
  obtain ⟨_, computed, agrees⟩ := evaluates state env related
  obtain rfl := Except.ok.inj (success.symm.trans computed)
  exact ⟨_, rfl, agrees⟩

private theorem integer_ge_observation
    {entry : CompilerScopes} {after : TranslateState} {factory unwritten}
    {range typeRange : SourceRange} {left right : Boole.Expr}
    {value : TypedExpr} {raw target : Core.Expression.Expr} {ty : Lambda.LMonoTy}
    (leftSupported : IntegerSum left) (rightSupported : IntegerSum right)
    (aligned : ScopesAgree entry)
    (addBuiltin : factory["Int.Add"]? = some (Lambda.intAddFunc (T := Core.CoreLParams)).func)
    (geBuiltin : factory["Int.Ge"]? = some (Lambda.intGeFunc (T := Core.CoreLParams)).func)
    (built : expr (.ge range (.int typeRange) left right) {} entry.source =
      .ok (value, entry.source))
    (lowered : toCoreExpr (.ge range (.int typeRange) left right) entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (typed : ExprWellTyped entry.context entry.variables target ty)
    (readable : ready unwritten target = true) :
    after = entry.lowering ∧
      BoolObservation (ScopedStoresAgree entry.source factory unwritten) value.eval target := by
  obtain ⟨lhs, rhs, lhsBuilt, rhsBuilt, lhsSort, rhsSort, _, compiled⟩ := compiled_int_ge built
  obtain ⟨middle, leftRaw, rightRaw, leftLowered, rightLowered, rfl⟩ := lowerIntGe_parts lowered
  obtain ⟨leftTarget, rightTarget, rfl, leftErased, rightErased⟩ :=
    typed_intGe_origin typed
      (aligned.builtins (Lambda.intGeFunc (T := Core.CoreLParams)).func Core.coreFactory_intGe) erased
  have reads : ready unwritten leftTarget = true ∧ ready unwritten rightTarget = true := by
    simp [ready, Core.CmdType.freeVars, Lambda.LExpr.freeVars, Core.intGeOp,
      List.all_append] at readable ⊢
    exact readable.2
  obtain ⟨leftTyped, rightTyped⟩ := typed_int_ge_operands typed
  obtain ⟨rfl, leftEval⟩ := integer_sum_agrees leftSupported aligned addBuiltin
    lhsBuilt leftLowered leftErased leftTyped reads.1 lhsSort
  obtain ⟨same, rightEval⟩ := integer_sum_agrees rightSupported aligned addBuiltin
    rhsBuilt rightLowered rightErased rightTyped reads.2 rhsSort
  refine ⟨same, ?_⟩
  intro state env related
  obtain ⟨a, leftSource, leftCore⟩ := leftEval state env related
  obtain ⟨b, rightSource, rightCore⟩ := rightEval state env related
  have computed : value.eval state = .ok (.bool (decide (a ≥ b))) := by
    rw [compiled]
    simp only [binary, leftSource, rightSource, Except.bind]
    exact binaryValue_int .ge a b
  have lookup : env.factory.factory["Int.Ge"]? = some (Lambda.intGeFunc (T := Core.CoreLParams)).func := by
    rw [related.1.factory_eq]
    exact geBuiltin
  exact ⟨_, computed, Core.eval_intGe lookup leftCore rightCore⟩

private theorem integer_ge_agrees
    {entry : CompilerScopes} {after : TranslateState} {factory unwritten}
    {range typeRange : SourceRange} {left right : Boole.Expr}
    {value : TypedExpr} {raw target : Core.Expression.Expr} {ty : Lambda.LMonoTy}
    (leftSupported : IntegerSum left) (rightSupported : IntegerSum right)
    (aligned : ScopesAgree entry)
    (addBuiltin : factory["Int.Add"]? = some (Lambda.intAddFunc (T := Core.CoreLParams)).func)
    (geBuiltin : factory["Int.Ge"]? = some (Lambda.intGeFunc (T := Core.CoreLParams)).func)
    (built : expr (.ge range (.int typeRange) left right) {} entry.source =
      .ok (value, entry.source))
    (lowered : toCoreExpr (.ge range (.int typeRange) left right) entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (typed : ExprWellTyped entry.context entry.variables target ty)
    (readable : ready unwritten target = true) :
    after = entry.lowering ∧
      ExprAgrees (ScopedStoresAgree entry.source factory unwritten) value.eval target := by
  obtain ⟨stable, evaluates⟩ := integer_ge_observation leftSupported rightSupported aligned addBuiltin geBuiltin
    built lowered erased typed readable
  exact ⟨stable, evaluates.agrees⟩

private theorem lowerIntEq_parts
    {range typeRange : SourceRange} {left right : Boole.Expr}
    {entry final : TranslateState} {raw : Core.Expression.Expr}
    (lowered : toCoreExpr (.equal range (.int typeRange) left right) entry =
      .ok (raw, final)) :
    ∃ middle leftRaw rightRaw, toCoreExpr left entry = .ok (leftRaw, middle) ∧
      toCoreExpr right middle = .ok (rightRaw, final) ∧
      raw = .eq () leftRaw rightRaw := by
  rw [toCoreExpr.eq_def] at lowered
  simp only [toCoreQuantExpr?, bind, StateT.bind, Except.bind] at lowered
  cases leftRun : toCoreExpr left entry with
  | error e => simp [leftRun] at lowered
  | ok p =>
    rcases p with ⟨leftRaw', middle⟩
    simp only [leftRun] at lowered
    cases rightRun : toCoreExpr right middle with
    | error e => simp [rightRun] at lowered
    | ok q =>
      rcases q with ⟨rightRaw', after⟩
      simp only [rightRun,
        pure, StateT.pure, Except.pure] at lowered
      have pairEq := Except.ok.inj lowered
      have stateEq := congrArg Prod.snd pairEq
      cases stateEq
      have rawEq : (.eq () leftRaw' rightRaw' :
          Core.Expression.Expr) = raw := congrArg Prod.fst pairEq
      exact ⟨middle, leftRaw', rightRaw', rfl, rightRun, rawEq.symm⟩


private theorem compiled_int_eq
    {range typeRange : SourceRange} {left right : Boole.Expr}
    {context : ReadContext} {scope after : Scope} {value : TypedExpr}
    (built : expr (.equal range (.int typeRange) left right) context scope =
      .ok (value, after)) :
    ∃ lhs rhs, expr left context scope = .ok (lhs, scope) ∧
      expr right context scope = .ok (rhs, scope) ∧
      lhs.sort = .int ∧ rhs.sort = .int ∧
      value.sort = .bool ∧ value.eval = binary .eq lhs.eval rhs.eval := by
  rw [expr.eq_def] at built
  obtain ⟨sort, next, sorted, rest⟩ := split_run built
  have nextEq := sourceSort_readOnly _ _ _ _ sorted
  subst next
  have sortEq : sort = .int := by
    rw [sourceSort] at sorted
    simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
      get, getThe, MonadStateOf.get, StateT.get] at sorted
    split at sorted
    · obtain ⟨_, _, fail, _⟩ := split_run sorted
      contradiction
    · exact (congrArg Prod.fst (Except.ok.inj sorted)).symm
  subst sort
  change ((expr left context >>= fun lhs => expr right context >>= fun rhs =>
    typedBinary range .eq .bool .int lhs rhs) scope) = .ok (value, after) at rest
  obtain ⟨lhs, mid, first, rest⟩ := split_run rest
  have midEq := expr_readOnly _ _ _ _ _ first
  subst mid
  obtain ⟨rhs, mid, second, rest⟩ := split_run rest
  have midEq := expr_readOnly _ _ _ _ _ second
  subst mid
  unfold typedBinary at rest
  obtain ⟨a, mid, matchesLeft, rest⟩ := split_run rest
  obtain ⟨b, last, matchesRight, done⟩ := split_run rest
  unfold TypedExpr.expect at matchesLeft matchesRight
  split at matchesLeft
  · rename_i lhsSort
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj matchesLeft)
    split at matchesRight
    · rename_i rhsSort
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj matchesRight)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj done)
      exact ⟨lhs, rhs, first, second, beq_iff_eq.mp lhsSort, beq_iff_eq.mp rhsSort, rfl, rfl⟩
    · contradiction
  · contradiction

private theorem integer_eq_observation
    {entry : CompilerScopes} {after : TranslateState} {factory unwritten}
    {range typeRange : SourceRange} {left right : Boole.Expr}
    {value : TypedExpr} {raw target : Core.Expression.Expr} {ty : Lambda.LMonoTy}
    (leftSupported : IntegerSum left) (rightSupported : IntegerSum right)
    (aligned : ScopesAgree entry)
    (addBuiltin : factory["Int.Add"]? = some (Lambda.intAddFunc (T := Core.CoreLParams)).func)
    (built : expr (.equal range (.int typeRange) left right) {} entry.source =
      .ok (value, entry.source))
    (lowered : toCoreExpr (.equal range (.int typeRange) left right) entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (typed : ExprWellTyped entry.context entry.variables target ty)
    (readable : ready unwritten target = true) :
    after = entry.lowering ∧
      BoolObservation (ScopedStoresAgree entry.source factory unwritten) value.eval target := by
  obtain ⟨lhs, rhs, lhsBuilt, rhsBuilt, lhsSort, rhsSort, _, compiled⟩ := compiled_int_eq built
  obtain ⟨middle, leftRaw, rightRaw, leftLowered, rightLowered, rfl⟩ := lowerIntEq_parts lowered
  obtain ⟨leftTarget, rightTarget, rfl, leftErased, rightErased⟩ := erase_eq_inv erased
  have reads : ready unwritten leftTarget = true ∧ ready unwritten rightTarget = true := by
    simp [ready, Core.CmdType.freeVars, Lambda.LExpr.freeVars, List.all_append] at readable ⊢
    exact readable
  obtain ⟨_, leftTyped, rightTyped⟩ := typed_eq_operands typed
  obtain ⟨rfl, leftEval⟩ := integer_sum_agrees leftSupported aligned addBuiltin
    lhsBuilt leftLowered leftErased leftTyped reads.1 lhsSort
  obtain ⟨same, rightEval⟩ := integer_sum_agrees rightSupported aligned addBuiltin
    rhsBuilt rightLowered rightErased rightTyped reads.2 rhsSort
  refine ⟨same, ?_⟩
  intro state env related
  obtain ⟨a, leftSource, leftCore⟩ := leftEval state env related
  obtain ⟨b, rightSource, rightCore⟩ := rightEval state env related
  have computed : value.eval state = .ok (.bool (a == b)) := by
    rw [compiled]
    simp only [binary, leftSource, rightSource, Except.bind]
    exact binaryValue_int .eq a b
  by_cases same : a = b
  · subst b
    refine ⟨true, ?_, Core.eval_eq_true env.factory leftCore rightCore⟩
    simpa only [beq_self_eq_true] using computed
  · refine ⟨false, ?_, Core.eval_eq_false env.factory leftCore rightCore rfl
      (fun equal => same (Lambda.SemValue.ofInt_injective equal))⟩
    simpa only [beq_eq_false_iff_ne.mpr same] using computed

private theorem integer_eq_agrees
    {entry : CompilerScopes} {after : TranslateState} {factory unwritten}
    {range typeRange : SourceRange} {left right : Boole.Expr}
    {value : TypedExpr} {raw target : Core.Expression.Expr} {ty : Lambda.LMonoTy}
    (leftSupported : IntegerSum left) (rightSupported : IntegerSum right)
    (aligned : ScopesAgree entry)
    (addBuiltin : factory["Int.Add"]? = some (Lambda.intAddFunc (T := Core.CoreLParams)).func)
    (built : expr (.equal range (.int typeRange) left right) {} entry.source =
      .ok (value, entry.source))
    (lowered : toCoreExpr (.equal range (.int typeRange) left right) entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (typed : ExprWellTyped entry.context entry.variables target ty)
    (readable : ready unwritten target = true) :
    after = entry.lowering ∧
      ExprAgrees (ScopedStoresAgree entry.source factory unwritten) value.eval target := by
  obtain ⟨stable, evaluates⟩ := integer_eq_observation leftSupported rightSupported aligned addBuiltin
    built lowered erased typed readable
  exact ⟨stable, evaluates.agrees⟩

private theorem scalar_leaf_agrees
    {entry : CompilerScopes} {after : TranslateState} {factory unwritten}
    {expression : Boole.Expr} {value : TypedExpr} {raw target : Core.Expression.Expr}
    (leaf : isScalarLeaf expression) (aligned : ScopesAgree entry)
    (built : expr expression {} entry.source = .ok (value, entry.source))
    (lowered : toCoreExpr expression entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (readable : ready unwritten target = true) :
    after = entry.lowering ∧
      ExprAgrees (ScopedStoresAgree entry.source factory unwritten) value.eval target ∧
      ∀ state, StateFits entry.source state →
        ∃ result, result.sort = value.sort ∧ value.eval state = .ok result := by
  by_cases literal : isScalarLiteral expression
  · obtain ⟨result, sort, evaluated, agrees⟩ := literal_agrees literal built
      ⟨_, lowered⟩ erased (ScopedStoresAgree entry.source factory unwritten)
    exact ⟨literal_lowering_unchanged literal lowered, agrees,
      fun state _ => ⟨result, sort.symm, evaluated state⟩⟩
  · cases expression <;> try solve | exact False.elim (literal leaf)
    case bvar => exact bound_rhs_agrees aligned built lowered erased readable
    case fvar => exact global_rhs_agrees aligned built lowered erased readable
private inductive SupportedCondition : Boole.Expr → Prop where
  | leaf {expression} : isScalarLeaf expression → SupportedCondition expression
  | ge (range typeRange : SourceRange) {left right} :
      IntegerSum left → IntegerSum right → SupportedCondition (.ge range (.int typeRange) left right)
  | eq (range typeRange : SourceRange) {left right} :
      IntegerSum left → IntegerSum right → SupportedCondition (.equal range (.int typeRange) left right)

private theorem condition_agrees
    {entry : CompilerScopes} {after : TranslateState} {factory unwritten}
    {expression : Boole.Expr} {value : TypedExpr} {raw target : Core.Expression.Expr}
    {ty : Lambda.LMonoTy}
    (supported : SupportedCondition expression) (aligned : ScopesAgree entry)
    (addBuiltin : factory["Int.Add"]? = some (Lambda.intAddFunc (T := Core.CoreLParams)).func)
    (geBuiltin : factory["Int.Ge"]? = some (Lambda.intGeFunc (T := Core.CoreLParams)).func)
    (built : expr expression {} entry.source = .ok (value, entry.source))
    (lowered : toCoreExpr expression entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (typed : ExprWellTyped entry.context entry.variables target ty)
    (readable : ready unwritten target = true) :
    after = entry.lowering ∧
      ExprAgrees (ScopedStoresAgree entry.source factory unwritten) value.eval target := by
  cases supported with
  | leaf leaf =>
    obtain ⟨stable, agrees, _⟩ := scalar_leaf_agrees leaf aligned built lowered erased readable
    exact ⟨stable, agrees⟩
  | ge _ _ lhs rhs =>
    exact integer_ge_agrees lhs rhs aligned addBuiltin geBuiltin built lowered erased typed readable
  | eq _ _ lhs rhs =>
    exact integer_eq_agrees lhs rhs aligned addBuiltin built lowered erased typed readable

private theorem condition_observation
    {entry : CompilerScopes} {after : TranslateState} {factory unwritten}
    {expression : Boole.Expr} {value : TypedExpr} {raw target : Core.Expression.Expr}
    {ty : Lambda.LMonoTy}
    (supported : SupportedCondition expression) (aligned : ScopesAgree entry)
    (addBuiltin : factory["Int.Add"]? = some (Lambda.intAddFunc (T := Core.CoreLParams)).func)
    (geBuiltin : factory["Int.Ge"]? = some (Lambda.intGeFunc (T := Core.CoreLParams)).func)
    (built : expr expression {} entry.source = .ok (value, entry.source))
    (lowered : toCoreExpr expression entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (typed : ExprWellTyped entry.context entry.variables target ty)
    (readable : ready unwritten target = true) (boolean : value.sort = .bool) :
    after = entry.lowering ∧
      BoolObservation (ScopedStoresAgree entry.source factory unwritten) value.eval target := by
  cases supported with
  | leaf leaf =>
    obtain ⟨stable, agrees, total⟩ := scalar_leaf_agrees leaf aligned built lowered erased readable
    refine ⟨stable, ?_⟩
    intro state env related
    obtain ⟨⟨sort, data⟩, same, computed⟩ := total state related.2
    have sortEq : sort = .bool := same.trans boolean
    subst sort
    exact ⟨data, computed, ExprAgrees.bool agrees related computed⟩
  | ge _ _ lhs rhs =>
    exact integer_ge_observation lhs rhs aligned addBuiltin geBuiltin built lowered erased typed readable
  | eq _ _ lhs rhs =>
    exact integer_eq_observation lhs rhs aligned addBuiltin built lowered erased typed readable

private theorem assertion_transfer
    {program : Core.Program} {params : InitEnvWFParams} {factory : Lambda.Factory Core.CoreLParams}
    {range : SourceRange} {annotations : Ann (Option (BooleDDM.MetadataAnn SourceRange)) SourceRange}
    {label : Ann (Option (BooleDDM.Label SourceRange)) SourceRange} {expression : Boole.Expr}
    {entry final : CompilerScopes} {compiled : Compiled} {readOnly labels : List String}
    {raw annotated : Core.Statements} {unwritten remaining : List Core.CoreIdent}
    (built : stmt (.assert range annotations label expression) readOnly entry.source =
      .ok (compiled, final.source))
    (lowered : lowerStatementChunk (.assert range annotations label expression) entry.lowering =
      .ok (raw, final.lowering))
    (erased : eraseStatementsAnnotations annotated = eraseStatementsAnnotations raw)
    (typed : StatementsWellTyped program entry.context entry.variables labels
      annotated final.context final.variables)
    (gate : coreStatements annotated unwritten = some remaining)
    (aligned : ScopesAgree entry)
    (condition : ∀ middle rawEnd value rawExpr target,
      ScopesAgree {entry with lowering := middle} →
      expr expression {} entry.source = .ok (value, entry.source) →
      toCoreExpr expression middle = .ok (rawExpr, rawEnd) →
      target.eraseTypes = rawExpr.eraseTypes →
      ExprWellTyped entry.context entry.variables target .bool →
      ready unwritten target = true →
      rawEnd = middle ∧
        ExprAgrees (ScopedStoresAgree entry.source factory unwritten) value.eval target) :
    ScopesAgree final ∧ BodyTransfer program params factory
      (fun scope unwritten => ScopedStoresAgree scope factory unwritten)
      entry.source final.source unwritten remaining compiled.command annotated := by
  rw [stmt.eq_def] at built
  by_cases hasMetadata : annotations.val.isSome = true
  · simp only [hasMetadata, ite_true] at built
    obtain ⟨_, _, rejected, _⟩ := split_run built
    contradiction
  simp only [ite_eq_right hasMetadata] at built
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
  have sourceBody : compiled.command = Transformer.assertion (sourceLabel range label.val) value.eval :=
    (congrArg (fun result : Compiled × Scope => result.1.command) (Except.ok.inj done)).symm
  simp only [lowerStatementChunk] at lowered
  rw [toCoreStmt] at lowered
  simp only [toCoreMetaData, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
    StateT.get, pure, StateT.pure, Except.pure] at lowered
  cases named : defaultLabel range "assert" label.val entry.lowering with
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
      have alignedMiddle : ScopesAgree {entry with lowering := middle} := by
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
              case assert coreLabel target md =>
                obtain ⟨_, exprEq, _⟩ := headEq
                have accepted : ready unwritten target = true ∧ remaining = unwritten := by
                  by_cases readOK : ready unwritten target = true <;>
                    simp [coreStatements, coreStatement, readOK, bind, Option.bind] at gate
                  exact ⟨readOK, gate.symm⟩
                have typing : ExprWellTyped entry.context entry.variables target .bool ∧
                    final.context = entry.context := by
                  generalize final.context = C at typed ⊢
                  cases typed with
                  | cons _ _ _ _ _ _ _ _ _ first second =>
                    cases first with
                    | cmd _ _ _ _ _ ext =>
                      cases ext with
                      | cmd _ _ c =>
                        cases c with
                        | assert _ _ _ _ wellTyped _ =>
                          cases second
                          exact ⟨wellTyped, rfl⟩
                obtain ⟨rawStable, actual⟩ := condition _ _ _ _ _ alignedMiddle sourceRun rawRun
                  exprEq typing.1 accepted.1
                have same : final.lowering = {entry.lowering with labelCounter := final.lowering.labelCounter} := by
                  rw [← rawEndEq, rawStable]
                  exact onlyCounter
                refine ⟨?_, ?_⟩
                · constructor
                  · rw [sourceScope, same]; exact aligned.names
                  · rw [sourceScope, same]; exact aligned.binders
                  · rw [sourceScope, same]; exact aligned.globals
                  · rw [sourceScope, same]; exact aligned.modifies
                  · rw [sourceScope]; exact aligned.distinct
                  · rw [sourceScope]; exact aligned.validNames
                  · rw [typing.2]; exact aligned.builtins
                · intro Q
                  rw [sourceScope, sourceBody, accepted.2]
                  have triple := transfer_assert (π := program.findProcByString?) (params := params)
                    (factory := factory) (entry := ScopedStoresAgree entry.source factory unwritten)
                    (sourceLabel range label.val) coreLabel value.eval target md (Q none)
                    (fun _ _ related => related.1.factory_eq) (by
                      intro state env related holds
                      apply ExprAgrees.bool actual related
                      change (match value.eval state with
                        | .ok (.bool b) => if b then True else False
                        | _ => False) at holds
                      split at holds
                      · rename_i b evaluated
                        cases b
                        · contradiction
                        · exact evaluated
                      · contradiction)
                  simpa only [Transformer.assertion, Core.Statement.assert] using triple

end Strata.Boole.Hoare
