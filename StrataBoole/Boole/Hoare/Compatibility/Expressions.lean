/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all StrataBoole.Boole.Hoare.Compile
import all StrataBoole.Boole.Hoare.Compatibility.Entry
import all StrataBoole.Boole.Hoare.Compatibility.Fragment
import all Strata.Languages.Core.CmdType
import all StrataBoole.Boole.Semantics.Adequacy.ExpressionExecution
import all StrataBoole.Boole.Interp
import all StrataBoole.Boole.Runtime
import StrataBoole.Boole.Semantics.Adequacy.Lowering
import all StrataBoole.Boole.Semantics.Adequacy.SourceInterface
import all StrataBoole.Verify
import all Strata.DL.Lambda.LExpr
import all StrataBoole.Boole.Semantics.Adequacy.ExpressionExecution
import Strata.Languages.Core.IntEvalProps

namespace Strata.Boole.Hoare

open StrataDDM Imperative

private theorem expect_readOnly (e : TypedExpr) (sort : ValueType) (range : SourceRange) :
    ReadOnly (e.expect sort range) := by
  unfold TypedExpr.expect
  split
  · exact readOnly_pure _
  · exact readOnly_reject _ _

private theorem read_readOnly (range : SourceRange) (context : ReadContext)
    (slot : Variable) (binding : Binding) : ReadOnly (read range context slot binding) := by
  unfold read
  cases slot
  all_goals
    repeat' first
      | exact readOnly_pure _
      | exact readOnly_reject _ _
      | exact readOnly_get
      | apply ReadOnly.bind
      | dsimp only
      | split
      | intro

private theorem typedBinary_readOnly (range : SourceRange) (op : BinaryOp)
    (output input : ValueType) (a b : TypedExpr) :
    ReadOnly (typedBinary range op output input a b) := by
  unfold typedBinary
  exact ReadOnly.bind (expect_readOnly _ _ _) fun _ =>
    ReadOnly.bind (expect_readOnly _ _ _) fun _ => readOnly_pure _

/-- A successful integer-add lowering is exactly two operand lowerings,
followed by the Core `Int.Add` application.  The intermediate translation
state is retained because the legacy lowerer threads it through operands. -/
private theorem lowerIntAdd_parts
    {range typeRange : SourceRange} {left right : Boole.Expr}
    {entry final : TranslateState} {raw : Core.Expression.Expr}
    (lowered : toCoreExpr (.add_expr range (.int typeRange) left right) entry =
      .ok (raw, final)) :
    ∃ middle leftRaw rightRaw, toCoreExpr left entry = .ok (leftRaw, middle) ∧
      toCoreExpr right middle = .ok (rightRaw, final) ∧
      raw = .app () (.app () (.op () ⟨"Int.Add", ()⟩ none) leftRaw) rightRaw := by
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
      have rawEq : (.app () (.app () (.op () ⟨"Int.Add", ()⟩ none) leftRaw') rightRaw' :
          Core.Expression.Expr) = raw := congrArg Prod.fst pairEq
      exact ⟨middle, leftRaw', rightRaw', rfl, rightRun, rawEq.symm⟩


set_option maxHeartbeats 1000000 in
/-- Expression checking reads the lexical scope. Only statement declarations
extend the scope of the enclosing statement list. -/
private theorem expr_readOnly (e : Boole.Expr) (context : ReadContext) :
    ReadOnly (expr e context) := by
  cases e <;> rw [expr.eq_def]
  all_goals
    repeat' first
      | exact readOnly_pure _
      | exact readOnly_reject _ _
      | exact readOnly_get
      | exact sourceSort_readOnly _
      | exact expect_readOnly _ _ _
      | exact read_readOnly _ _ _ _
      | exact typedBinary_readOnly _ _ _ _ _ _
      | exact expr_readOnly _ _
      | apply ReadOnly.bind
      | dsimp only
      | split
      | intro
termination_by sizeOf e
decreasing_by all_goals simp_all <;> omega

private theorem compiled_int_add
    {range typeRange : SourceRange} {left right : Boole.Expr}
    {context : ReadContext} {scope after : Scope} {value : TypedExpr}
    (built : expr (.add_expr range (.int typeRange) left right) context scope =
      .ok (value, after)) :
    ∃ lhs rhs, expr left context scope = .ok (lhs, scope) ∧
      expr right context scope = .ok (rhs, scope) ∧
      lhs.sort = .int ∧ rhs.sort = .int ∧
      value.sort = .int ∧ value.eval = binary .add lhs.eval rhs.eval := by
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
    typedBinary range .add .int .int lhs rhs) scope) = .ok (value, after) at rest
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

private theorem typed_int_add_operands
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    {lhs rhs : Core.Expression.Expr} {ty : Lambda.LMonoTy}
    (typed : Core.TypeSpec.ExprWellTyped context scopes
      (.app () (.app () Core.coreIntAddOpExpr lhs) rhs) ty) :
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

/-- Integer addition combines the operand proofs in the Core entry's own model. -/
private theorem int_add_agrees
    {range typeRange : SourceRange} {left right : Boole.Expr}
    {readContext : ReadContext} {scope : Scope} {entry final : TranslateState}
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    {value : TypedExpr} {raw target : Core.Expression.Expr} {ty : Lambda.LMonoTy}
    {factory : Lambda.Factory Core.CoreLParams} {unwritten : List Core.CoreIdent}
    (built : expr (.add_expr range (.int typeRange) left right) readContext scope =
      .ok (value, scope))
    (lowered : toCoreExpr (.add_expr range (.int typeRange) left right) entry =
      .ok (raw, final))
    (erased : target.eraseTypes = raw.eraseTypes)
    (typed : Core.TypeSpec.ExprWellTyped context scopes target ty)
    (readable : ready unwritten target = true)
    (signature : context.functions["Int.Add"]? = some (Lambda.intAddFunc (T := Core.CoreLParams)).func)
    (ambient : factory["Int.Add"]? = some (Lambda.intAddFunc (T := Core.CoreLParams)).func)
    (operands : ∀ lhs rhs middle leftRaw rightRaw leftTarget rightTarget,
      expr left readContext scope = .ok (lhs, scope) →
      expr right readContext scope = .ok (rhs, scope) →
      lhs.sort = .int → rhs.sort = .int →
      toCoreExpr left entry = .ok (leftRaw, middle) →
      toCoreExpr right middle = .ok (rightRaw, final) →
      leftTarget.eraseTypes = leftRaw.eraseTypes → rightTarget.eraseTypes = rightRaw.eraseTypes →
      Core.TypeSpec.ExprWellTyped context scopes leftTarget .int →
      Core.TypeSpec.ExprWellTyped context scopes rightTarget .int →
      ready unwritten leftTarget = true → ready unwritten rightTarget = true →
      final = entry ∧ ∀ state env, ScopedStoresAgree scope factory unwritten state env →
        ∃ a b : Int,
          lhs.eval state = .ok (.int a) ∧ rhs.eval state = .ok (.int b) ∧
          Core.Expression.eval env.factory env.store leftTarget =
            some (.ofInt env.factory.model.tcInterp a) ∧
          Core.Expression.eval env.factory env.store rightTarget =
            some (.ofInt env.factory.model.tcInterp b)) :
    final = entry ∧ ∀ state env, ScopedStoresAgree scope factory unwritten state env →
      ∃ n : Int, value.eval state = .ok (.int n) ∧
        Core.Expression.eval env.factory env.store target =
          some (.ofInt env.factory.model.tcInterp n) := by
  obtain ⟨lhs, rhs, lhsBuilt, rhsBuilt, lhsSort, rhsSort, _, compiled⟩ := compiled_int_add built
  obtain ⟨middle, leftRaw, rightRaw, leftLowered, rightLowered, rfl⟩ := lowerIntAdd_parts lowered
  obtain ⟨leftTarget, rightTarget, rfl, leftErased, rightErased⟩ :=
    typed_intAdd_origin typed signature erased
  have reads : ready unwritten leftTarget = true ∧ ready unwritten rightTarget = true := by
    simp [ready, Core.CmdType.freeVars, Lambda.LExpr.freeVars, Core.coreIntAddOpExpr,
      List.all_append] at readable ⊢
    exact readable.2
  obtain ⟨leftTyped, rightTyped⟩ := typed_int_add_operands typed
  have ⟨same, evaluateOperands⟩ := operands _ _ _ _ _ _ _ lhsBuilt rhsBuilt lhsSort rhsSort
    leftLowered rightLowered leftErased rightErased leftTyped rightTyped reads.1 reads.2
  refine ⟨same, ?_⟩
  intro state env related
  obtain ⟨a, b, leftSource, rightSource, leftCore, rightCore⟩ := evaluateOperands state env related
  have computed : value.eval state = .ok (.int (a + b)) := by
    rw [compiled]
    simp only [binary, leftSource, rightSource, Except.bind]
    exact binaryValue_int .add a b
  have lookup : env.factory.factory["Int.Add"]? = some (Lambda.intAddFunc (T := Core.CoreLParams)).func := by
    rw [related.1.factory_eq]
    exact ambient
  exact ⟨a + b, computed, Core.eval_intAdd lookup leftCore rightCore⟩

private def isScalarLiteral : Boole.Expr → Prop
  | .natToInt .. | .btrue .. | .bfalse .. => True
  | _ => False

/-- A literal's two compiler runs and erasure determine its value. -/
private theorem literal_agrees
    {expression : Boole.Expr} (scalar : isScalarLiteral expression)
    {readContext : ReadContext} {scope final : Scope} {entry : TranslateState}
    {source : TypedExpr} {raw annotated : Core.Expression.Expr}
    (compiled : expr expression readContext scope = .ok (source, final))
    (lowered : ExpressionWasLowered expression entry raw)
    (erased : annotated.eraseTypes = raw.eraseTypes)
    (related : State → Env Core.Expression → Prop) :
    ∃ value, source.sort = value.sort ∧ (∀ state, source.eval state = .ok value) ∧
      ExprAgrees related source.eval annotated := by
  obtain ⟨_, lowered⟩ := lowered
  cases expression
  all_goals try solve | exact False.elim scalar
  all_goals
    rw [expr.eq_def] at compiled
    rw [toCoreExpr.eq_def] at lowered
    simp only [toCoreQuantExpr?, pure, StateT.pure, Except.pure] at compiled lowered
    obtain rfl := (congrArg Prod.fst (Except.ok.inj compiled)).symm
    obtain rfl := (congrArg Prod.fst (Except.ok.inj lowered)).symm
    cases annotated <;> simp [Lambda.LExpr.eraseTypes] at erased
    obtain rfl := erased
    exact ⟨_, rfl, fun _ => rfl, by first
      | exact ExprAgrees.intLiteral related _
      | exact ExprAgrees.boolLiteral related _⟩

private theorem literal_lowering_unchanged
    {expression : Boole.Expr} (scalar : isScalarLiteral expression)
    {entry final : TranslateState} {raw : Core.Expression.Expr}
    (lowered : toCoreExpr expression entry = .ok (raw, final)) : final = entry := by
  cases expression
  all_goals try solve | exact False.elim scalar
  all_goals
    rw [toCoreExpr.eq_def] at lowered
    simp only [toCoreQuantExpr?, pure, StateT.pure, Except.pure] at lowered
    exact (congrArg Prod.snd (Except.ok.inj lowered)).symm

/-- A bound variable has the same lexical slot on both sides of lowering.
The result is total on that scope once the slot is readable. -/
private theorem local_read_agrees
    {range : SourceRange} {index : Nat} {binding : Binding}
    {readContext : ReadContext} {scope final : Scope} {entry : TranslateState}
    {source : TypedExpr} {raw annotated : Core.Expression.Expr} {factory unwritten}
    (encoded : entry.bvars = scope.locals.toArray.map
      (fun b => (.fvar () ⟨b.name, ()⟩ none : Core.Expression.Expr)))
    (found : scope.locals.reverse[index]? = some binding)
    (unique : findBinding binding.name scope.locals = some binding)
    (written : coreIdent (.local binding.name) ∉ unwritten)
    (compiled : expr (.bvar range index) readContext scope = .ok (source, final))
    (lowered : ExpressionWasLowered (.bvar range index) entry raw)
    (erased : annotated.eraseTypes = raw.eraseTypes) :
    source.sort = binding.sort ∧
      (∀ state, StateFits scope state →
        ∃ value, value.sort = source.sort ∧ source.eval state = .ok value) ∧
      ExprAgrees (ScopedStoresAgree scope factory unwritten) source.eval annotated := by
  have localOld : Expression.old (model := .builtins) (Expression.read (.local binding.name)) =
      Expression.read (.local binding.name) := rfl
  rw [expr.eq_def] at compiled
  by_cases unavailable : binding.name ∈ readContext.requiresOutputs.getD []
  · simp [found, read, unavailable, reject, throw, throwThe, MonadExceptOf.throw,
      bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, StateT.lift, Except.pure] at compiled
  · simp [found, read, unavailable, localOld, bind, StateT.bind, Except.bind,
      get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure] at compiled
    obtain ⟨rfl, _⟩ := compiled
    have expected :=
      (lowerLocalRead (checkingInterpretation (fun _ => true)) scope entry range index
        binding encoded found).2
    obtain rfl := lowered.unique expected
    cases annotated <;> simp [Lambda.LExpr.eraseTypes] at erased
    case fvar md id annotation =>
      cases md
      obtain rfl := erased
      refine ⟨rfl, ?_, ?_⟩
      · intro state fits
        obtain ⟨value, lookup, sort⟩ := fits.lookup_local unique
        exact ⟨value, sort, by simp [Expression.read, State.lookup, lookup]⟩
      · intro state env value ⟨agrees, _⟩ evaluated
        exact ExprAgrees.read (.local binding.name) written annotation state env value agrees evaluated

/-- An ordinary global read resolves through the common name context and
the legacy table that registered the global. -/
private theorem global_read_agrees
    {range : SourceRange} {index : Nat} {name : String} {binding : Binding}
    {readContext : ReadContext} {scope final : Scope} {entry : TranslateState}
    {source : TypedExpr} {raw annotated : Core.Expression.Expr} {factory unwritten}
    (current : readContext.old = false)
    (sameNames : scope.names = entry.gctx)
    (resolved : scope.names.nameOf? index = some name)
    (found : findBinding name scope.globals = some binding)
    (registered : entry.globalVarTypes.contains name = true)
    (written : coreIdent (.global name) ∉ unwritten)
    (compiled : expr (.fvar range index) readContext scope = .ok (source, final))
    (lowered : ExpressionWasLowered (.fvar range index) entry raw)
    (erased : annotated.eraseTypes = raw.eraseTypes) :
    source.sort = binding.sort ∧
      (∀ state, StateFits scope state →
        ∃ value, value.sort = source.sort ∧ source.eval state = .ok value) ∧
      ExprAgrees (ScopedStoresAgree scope factory unwritten) source.eval annotated := by
  rw [expr.eq_def] at compiled
  simp [resolved, found, read, current, bind, StateT.bind, Except.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure] at compiled
  obtain ⟨rfl, _⟩ := compiled
  have expected :=
    (lowerGlobalRead (checkingInterpretation (fun _ => true)) scope entry range index name binding
      sameNames resolved found registered).2
  obtain rfl := lowered.unique expected
  cases annotated <;> simp [Lambda.LExpr.eraseTypes] at erased
  case fvar md id annotation =>
    cases md
    obtain rfl := erased
    refine ⟨rfl, ?_, ?_⟩
    · intro state fits
      obtain ⟨value, lookup, sort⟩ := fits.lookup_global found
      exact ⟨value, sort, by simp [Expression.read, State.lookup, lookup]⟩
    · intro state env value ⟨agrees, _⟩ evaluated
      exact ExprAgrees.read (.global name) written annotation state env value agrees evaluated

end Strata.Boole.Hoare
