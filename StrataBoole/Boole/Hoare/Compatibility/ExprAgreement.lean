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
import all Strata.Languages.Core.InstWellFormedSemanticsEval
import all StrataBoole.Boole.Hoare.Compatibility.Condition
public import StrataBoole.Boole.Hoare.Compatibility.Syntax
import StrataBoole.Boole.Hoare.Compatibility.ScalarEval
import Strata.DL.Lambda.LExprDenoteEvalProps
import Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.Denote.LExprDenote

namespace Strata.Boole.Hoare

open StrataDDM Core.TypeSpec Core.Logic Imperative

/-- Agreement of a compiled expression with its checked lowering, with source sort soundness. -/
private def Agrees (scope : Scope) (factory : Lambda.Factory Core.CoreLParams)
    (unwritten : List Core.CoreIdent) (value : TypedExpr) (target : Core.Expression.Expr) : Prop :=
  ∀ state env result, ScopedStoresAgree scope factory unwritten state env →
    value.eval state = .ok result →
    result.sort = value.sort ∧
    ∃ v, coreValueIn? env.factory.model.tcInterp result = some v ∧
      Core.Expression.eval env.factory env.store target = some v

/-- A total source evaluation of the right sort, plus payload agreement, is agreement. -/
private theorem Agrees.of_total
    {scope : Scope} {factory : Lambda.Factory Core.CoreLParams} {unwritten : List Core.CoreIdent}
    {value : TypedExpr} {target : Core.Expression.Expr}
    (total : ∀ state, StateFits scope state →
      ∃ result, result.sort = value.sort ∧ value.eval state = .ok result)
    (payload : ExprAgrees (ScopedStoresAgree scope factory unwritten) value.eval target) :
    Agrees scope factory unwritten value target := by
  intro state env result related evaluated
  obtain ⟨expected, expectedSort, computed⟩ := total state related.2
  have same : result = expected := Except.ok.inj (evaluated.symm.trans computed)
  subst same
  exact ⟨expectedSort, payload state env result related evaluated⟩

/-- A constant whose Core form is the same literal agrees in every store. -/
private theorem const_agrees
    {scope : Scope} {factory : Lambda.Factory Core.CoreLParams} {unwritten : List Core.CoreIdent}
    {value : TypedExpr} {target : Core.Expression.Expr} {payload : Value} {c : Lambda.LConst}
    (evalConst : ∀ state, value.eval state = .ok payload)
    (sortConst : value.sort = payload.sort)
    (rawShape : target = .const () c)
    (represented : ∀ tc, coreValueIn? tc payload = some (Lambda.SemValue.ofConst tc c)) :
    Agrees scope factory unwritten value target := by
  intro state env result related evaluated
  have resultEq : result = payload := Except.ok.inj (evaluated.symm.trans (evalConst state))
  subst resultEq
  refine ⟨sortConst.symm, _, represented _, ?_⟩
  simpa [rawShape] using Core.eval_const env.factory env.store c

private theorem value_of_sort_int {v : Value} (h : v.sort = .int) : ∃ n : Int, v = .int n := by
  obtain ⟨s, data⟩ := v
  subst h
  exact ⟨data, rfl⟩

private theorem value_of_sort_bool {v : Value} (h : v.sort = .bool) : ∃ b : Bool, v = .bool b := by
  obtain ⟨s, data⟩ := v
  subst h
  exact ⟨data, rfl⟩

private theorem compiled_not
    {range : SourceRange} {operand : Boole.Expr} {context : ReadContext} {scope : Scope}
    {value : TypedExpr}
    (built : expr (.not range operand) context scope = .ok (value, scope)) :
    ∃ inner, expr operand context scope = .ok (inner, scope) ∧ inner.sort = .bool ∧
      value.sort = .bool ∧ value.eval = Expression.unary .not inner.eval := by
  rw [expr.eq_def] at built
  obtain ⟨inner, mid, ran, rest⟩ := split_run built
  have midEq := expr_readOnly _ _ _ _ _ ran
  subst mid
  obtain ⟨ev, last, expected, done⟩ := split_run rest
  unfold TypedExpr.expect at expected
  split at expected
  · rename_i same
    cases congrArg Prod.fst (Except.ok.inj expected)
    cases congrArg Prod.snd (Except.ok.inj expected)
    cases congrArg Prod.fst (Except.ok.inj done)
    cases congrArg Prod.snd (Except.ok.inj done)
    exact ⟨inner, ran, beq_iff_eq.mp same, rfl, rfl⟩
  · contradiction

private theorem lower_not
    {range : SourceRange} {operand : Boole.Expr} {entry : TranslateState}
    {raw : Core.Expression.Expr} {final : TranslateState}
    (lowered : toCoreExpr (.not range operand) entry = .ok (raw, final)) :
    ∃ innerRaw, toCoreExpr operand entry = .ok (innerRaw, final) ∧
      raw = .app () Core.boolNotOp innerRaw := by
  rw [toCoreExpr.eq_def] at lowered
  simp only [toCoreQuantExpr?, bind, StateT.bind, Except.bind] at lowered
  cases ran : toCoreExpr operand entry with
  | error e => simp [ran] at lowered
  | ok pair =>
    obtain ⟨innerRaw, middle⟩ := pair
    simp only [ran, pure, StateT.pure, Except.pure] at lowered
    have pairEq := Except.ok.inj lowered
    cases congrArg Prod.snd pairEq
    exact ⟨innerRaw, rfl, (congrArg Prod.fst pairEq).symm⟩

private theorem unary_not_bool {state : State} {e : Expression} {b : Bool}
    (h : e state = .ok (.bool b)) :
    Expression.unary .not e state = .ok (.bool (!b)) := by
  unfold Expression.unary
  rw [h]
  simp only [bind, Except.bind, pure, Except.pure]
  rfl

private inductive IntBin where
  | add | sub | mul | le | lt | ge | gt

namespace IntBin

def bop : IntBin → BinaryOp
  | .add => .add | .sub => .sub | .mul => .mul
  | .le => .le | .lt => .lt | .ge => .ge | .gt => .gt

def resultSort : IntBin → ValueType
  | .add | .sub | .mul => .int
  | .le | .lt | .ge | .gt => .bool

def coreName : IntBin → String
  | .add => "Int.Add" | .sub => "Int.Sub" | .mul => "Int.Mul"
  | .le => "Int.Le" | .lt => "Int.Lt" | .ge => "Int.Ge" | .gt => "Int.Gt"

def atInt (op : IntBin) (r tr : SourceRange) (a b : Boole.Expr) : Boole.Expr :=
  match op with
  | .add => .add_expr r (.int tr) a b | .sub => .sub_expr r (.int tr) a b
  | .mul => .mul_expr r (.int tr) a b | .le => .le r (.int tr) a b
  | .lt => .lt r (.int tr) a b | .ge => .ge r (.int tr) a b | .gt => .gt r (.int tr) a b

def atBool (op : IntBin) (r tr : SourceRange) (a b : Boole.Expr) : Boole.Expr :=
  match op with
  | .add => .add_expr r (.bool tr) a b | .sub => .sub_expr r (.bool tr) a b
  | .mul => .mul_expr r (.bool tr) a b | .le => .le r (.bool tr) a b
  | .lt => .lt r (.bool tr) a b | .ge => .ge r (.bool tr) a b | .gt => .gt r (.bool tr) a b

def func : IntBin → Lambda.LFunc Core.CoreLParams
  | .add => (Lambda.intAddFunc (T := Core.CoreLParams)).func
  | .sub => (Lambda.intSubFunc (T := Core.CoreLParams)).func
  | .mul => (Lambda.intMulFunc (T := Core.CoreLParams)).func
  | .le => (Lambda.intLeFunc (T := Core.CoreLParams)).func
  | .lt => (Lambda.intLtFunc (T := Core.CoreLParams)).func
  | .ge => (Lambda.intGeFunc (T := Core.CoreLParams)).func
  | .gt => (Lambda.intGtFunc (T := Core.CoreLParams)).func

def opExpr : IntBin → Core.Expression.Expr
  | .add => Core.intAddOp | .sub => Core.intSubOp | .mul => Core.intMulOp
  | .le => Core.intLeOp | .lt => Core.intLtOp | .ge => Core.intGeOp | .gt => Core.intGtOp

def declared : IntBin → Lambda.LMonoTy
  | .add | .sub | .mul => .arrow .int (.arrow .int .int)
  | .le | .lt | .ge | .gt => .arrow .int (.arrow .int .bool)

def combine : IntBin → Int → Int → Value
  | .add => fun a b => .int (a + b) | .sub => fun a b => .int (a - b)
  | .mul => fun a b => .int (a * b) | .lt => fun a b => .bool (decide (a < b))
  | .le => fun a b => .bool (decide (a ≤ b)) | .gt => fun a b => .bool (decide (b < a))
  | .ge => fun a b => .bool (decide (b ≤ a))

theorem nameEq (op : IntBin) : op.func.name.name = op.coreName := by cases op <;> rfl

theorem shape (op : IntBin) :
    op.func.type = .ok (.forAll [] op.declared) ∧ op.declared.freeVars = [] ∧
      op.opExpr = .op () ⟨op.coreName, ()⟩ (some op.declared) := by
  cases op <;> exact ⟨rfl, rfl, rfl⟩

theorem inFactory (op : IntBin) : Core.Factory[op.coreName]? = some op.func := by
  cases op
  · exact Core.coreFactory_intAdd
  · exact Core.coreFactory_intSub
  · exact Core.coreFactory_intMul
  · exact Core.coreFactory_intLe
  · exact Core.coreFactory_intLt
  · exact Core.coreFactory_intGe
  · exact Core.coreFactory_intGt

theorem binaryValue_eq (op : IntBin) (a b : Int) :
    binaryValue op.bop ⟨.int, a⟩ ⟨.int, b⟩ = .ok (op.combine a b) := by
  cases op <;> exact binaryValue_int _ a b

theorem combine_sort (op : IntBin) (a b : Int) : (op.combine a b).sort = op.resultSort := by
  cases op <;> rfl

end IntBin

private theorem sourceSort_literal
    {range : SourceRange} {scope next : Scope} {sort : ValueType} {ty : Boole.Type}
    (sorted : sourceSort ty scope = .ok (sort, next))
    (ground : ty = .int range ∨ ty = .bool range) :
    next = scope ∧ (ty = .int range → sort = .int) ∧ (ty = .bool range → sort = .bool) := by
  have nextEq := sourceSort_readOnly _ _ _ _ sorted
  refine ⟨nextEq, ?_, ?_⟩
  · intro isInt
    subst isInt
    rw [sourceSort] at sorted
    simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
      get, getThe, MonadStateOf.get, StateT.get] at sorted
    split at sorted
    · obtain ⟨_, _, fail, _⟩ := split_run sorted
      contradiction
    · exact (congrArg Prod.fst (Except.ok.inj sorted)).symm
  · intro isBool
    subst isBool
    rw [sourceSort] at sorted
    simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
      get, getThe, MonadStateOf.get, StateT.get] at sorted
    split at sorted
    · obtain ⟨_, _, fail, _⟩ := split_run sorted
      contradiction
    · exact (congrArg Prod.fst (Except.ok.inj sorted)).symm

private theorem typed_binary_parts
    {range : SourceRange} {op : BinaryOp} {result operand : ValueType}
    {left right : Boole.Expr} {context : ReadContext} {scope : Scope} {value : TypedExpr}
    (rest : ((expr left context >>= fun lhs => expr right context >>= fun rhs =>
        typedBinary range op result operand lhs rhs) scope) = .ok (value, scope)) :
    ∃ lhs rhs, expr left context scope = .ok (lhs, scope) ∧
      expr right context scope = .ok (rhs, scope) ∧
      lhs.sort = operand ∧ rhs.sort = operand ∧
      value.sort = result ∧ value.eval = binary op lhs.eval rhs.eval := by
  obtain ⟨lhs, mid, first, rest⟩ := split_run rest
  cases expr_readOnly _ _ _ _ _ first
  obtain ⟨rhs, mid, second, rest⟩ := split_run rest
  cases expr_readOnly _ _ _ _ _ second
  unfold typedBinary at rest
  obtain ⟨_, _, matchesLeft, rest⟩ := split_run rest
  obtain ⟨_, _, matchesRight, done⟩ := split_run rest
  unfold TypedExpr.expect at matchesLeft matchesRight
  split at matchesLeft
  · rename_i lhsSort
    cases congrArg Prod.fst (Except.ok.inj matchesLeft)
    cases congrArg Prod.snd (Except.ok.inj matchesLeft)
    split at matchesRight
    · rename_i rhsSort
      cases congrArg Prod.fst (Except.ok.inj matchesRight)
      cases congrArg Prod.snd (Except.ok.inj matchesRight)
      cases congrArg Prod.fst (Except.ok.inj done)
      cases congrArg Prod.snd (Except.ok.inj done)
      exact ⟨lhs, rhs, first, second, beq_iff_eq.mp lhsSort, beq_iff_eq.mp rhsSort, rfl, rfl⟩
    · contradiction
  · contradiction

private theorem compiled_int_bin (op : IntBin)
    {range tr : SourceRange} {left right : Boole.Expr} {context : ReadContext}
    {scope : Scope} {value : TypedExpr}
    (built : expr (op.atInt range tr left right) context scope = .ok (value, scope)) :
    ∃ lhs rhs, expr left context scope = .ok (lhs, scope) ∧
      expr right context scope = .ok (rhs, scope) ∧
      lhs.sort = .int ∧ rhs.sort = .int ∧
      value.sort = op.resultSort ∧ value.eval = binary op.bop lhs.eval rhs.eval := by
  cases op <;> dsimp only [IntBin.atInt, IntBin.bop, IntBin.resultSort] at built ⊢
  case add => exact compiled_int_add built
  case sub =>
    rw [expr.eq_def] at built
    obtain ⟨sort, next, sorted, rest⟩ := split_run built
    have nextEq := sourceSort_readOnly _ _ _ _ sorted
    cases nextEq
    have sortEq : sort = .int := by
      rw [sourceSort] at sorted
      simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
        get, getThe, MonadStateOf.get, StateT.get] at sorted
      split at sorted
      · obtain ⟨_, _, fail, _⟩ := split_run sorted
        contradiction
      · exact (congrArg Prod.fst (Except.ok.inj sorted)).symm
    cases sortEq
    change ((expr left context >>= fun lhs => expr right context >>= fun rhs =>
      typedBinary range .sub .int .int lhs rhs) scope) = .ok (value, scope) at rest
    exact typed_binary_parts rest
  case mul =>
    rw [expr.eq_def] at built
    obtain ⟨sort, next, sorted, rest⟩ := split_run built
    have nextEq := sourceSort_readOnly _ _ _ _ sorted
    cases nextEq
    have sortEq : sort = .int := by
      rw [sourceSort] at sorted
      simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
        get, getThe, MonadStateOf.get, StateT.get] at sorted
      split at sorted
      · obtain ⟨_, _, fail, _⟩ := split_run sorted
        contradiction
      · exact (congrArg Prod.fst (Except.ok.inj sorted)).symm
    cases sortEq
    change ((expr left context >>= fun lhs => expr right context >>= fun rhs =>
      typedBinary range .mul .int .int lhs rhs) scope) = .ok (value, scope) at rest
    exact typed_binary_parts rest
  case le =>
    rw [expr.eq_def] at built
    obtain ⟨sort, next, sorted, rest⟩ := split_run built
    have nextEq := sourceSort_readOnly _ _ _ _ sorted
    cases nextEq
    have sortEq : sort = .int := by
      rw [sourceSort] at sorted
      simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
        get, getThe, MonadStateOf.get, StateT.get] at sorted
      split at sorted
      · obtain ⟨_, _, fail, _⟩ := split_run sorted
        contradiction
      · exact (congrArg Prod.fst (Except.ok.inj sorted)).symm
    cases sortEq
    change ((expr left context >>= fun lhs => expr right context >>= fun rhs =>
      typedBinary range .le .bool .int lhs rhs) scope) = .ok (value, scope) at rest
    exact typed_binary_parts rest
  case lt =>
    rw [expr.eq_def] at built
    obtain ⟨sort, next, sorted, rest⟩ := split_run built
    have nextEq := sourceSort_readOnly _ _ _ _ sorted
    cases nextEq
    have sortEq : sort = .int := by
      rw [sourceSort] at sorted
      simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
        get, getThe, MonadStateOf.get, StateT.get] at sorted
      split at sorted
      · obtain ⟨_, _, fail, _⟩ := split_run sorted
        contradiction
      · exact (congrArg Prod.fst (Except.ok.inj sorted)).symm
    cases sortEq
    change ((expr left context >>= fun lhs => expr right context >>= fun rhs =>
      typedBinary range .lt .bool .int lhs rhs) scope) = .ok (value, scope) at rest
    exact typed_binary_parts rest
  case ge => exact compiled_int_ge built
  case gt =>
    rw [expr.eq_def] at built
    obtain ⟨sort, next, sorted, rest⟩ := split_run built
    have nextEq := sourceSort_readOnly _ _ _ _ sorted
    cases nextEq
    have sortEq : sort = .int := by
      rw [sourceSort] at sorted
      simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
        get, getThe, MonadStateOf.get, StateT.get] at sorted
      split at sorted
      · obtain ⟨_, _, fail, _⟩ := split_run sorted
        contradiction
      · exact (congrArg Prod.fst (Except.ok.inj sorted)).symm
    cases sortEq
    change ((expr left context >>= fun lhs => expr right context >>= fun rhs =>
      typedBinary range .gt .bool .int lhs rhs) scope) = .ok (value, scope) at rest
    exact typed_binary_parts rest

private theorem lower_int_bin (op : IntBin)
    {range tr : SourceRange} {left right : Boole.Expr} {entry : TranslateState}
    {raw : Core.Expression.Expr} {final : TranslateState}
    (lowered : toCoreExpr (op.atInt range tr left right) entry = .ok (raw, final)) :
    ∃ middle leftRaw rightRaw, toCoreExpr left entry = .ok (leftRaw, middle) ∧
      toCoreExpr right middle = .ok (rightRaw, final) ∧
      raw = .app () (.app () (.op () ⟨op.coreName, ()⟩ none) leftRaw) rightRaw := by
  cases op <;>
    (unfold IntBin.atInt at lowered
     rw [toCoreExpr.eq_def] at lowered
     simp only [toCoreQuantExpr?, bind, StateT.bind, Except.bind] at lowered
     cases leftRun : toCoreExpr left entry with
     | error e => simp [leftRun] at lowered
     | ok p =>
       obtain ⟨leftRaw', middle⟩ := p
       simp only [leftRun] at lowered
       cases rightRun : toCoreExpr right middle with
       | error e => simp [rightRun] at lowered
       | ok q =>
         obtain ⟨rightRaw', afterState⟩ := q
         simp only [rightRun, toCoreTypedBin, mkCoreApp, Lambda.LExpr.mkApp,
           pure, StateT.pure, Except.pure] at lowered
         have pairEq := Except.ok.inj lowered
         cases congrArg Prod.snd pairEq
         exact ⟨middle, leftRaw', rightRaw', rfl, rightRun,
           (congrArg Prod.fst pairEq).symm⟩)

private theorem typed_bin_origin
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    {annotated left right : Core.Expression.Expr} {ty declared : Lambda.LMonoTy}
    {name : String} {fn : Lambda.LFunc Core.CoreLParams} {op : Core.Expression.Expr}
    (opShape : op = .op () ⟨name, ()⟩ (some declared))
    (typed : ExprWellTyped context scopes annotated ty)
    (signature : context.functions[name]? = some fn)
    (scheme : fn.type = .ok (.forAll [] declared))
    (closed : declared.freeVars = [])
    (erased : annotated.eraseTypes =
      (.app () (.app () (.op () ⟨name, ()⟩ none) left) right : Core.Expression.Expr).eraseTypes) :
    ∃ a b, annotated = .app () (.app () op a) b ∧
      a.eraseTypes = left.eraseTypes ∧ b.eraseTypes = right.eraseTypes := by
  cases annotated <;> simp [Lambda.LExpr.eraseTypes] at erased
  case app md fnExpr b =>
    cases md
    obtain ⟨fnSame, bSame⟩ := erased
    have appTyped := typed.1
    have ⟨domainB, fnTyped⟩ : ∃ domainB, Lambda.LExpr.HasTypeA [] fnExpr (.arrow domainB ty) := by
      cases appTyped with | app f _ => exact ⟨_, f⟩
    cases fnExpr <;> simp [Lambda.LExpr.eraseTypes] at fnSame
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
        have same := operatorAnnotation_eq (id := ⟨name, ()⟩)
          (annotation := .arrow domainA (.arrow domainB ty)) typed.2.2
          (by simp [Lambda.LExpr.opAnnots]) signature
          (declared := declared) scheme closed
        rw [annotationEq, same, ← opShape]
        exact ⟨a, b, rfl, aSame, bSame⟩

private theorem typed_same_domains
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    {lhs rhs : Core.Expression.Expr} {domain result ty : Lambda.LMonoTy} {id : Core.CoreIdent}
    (typed : ExprWellTyped context scopes
      (.app () (.app () (.op () id (some (.arrow domain (.arrow domain result)))) lhs) rhs) ty) :
    ExprWellTyped context scopes lhs domain ∧ ExprWellTyped context scopes rhs domain := by
  have types : Lambda.LExpr.HasTypeA [] lhs domain ∧ Lambda.LExpr.HasTypeA [] rhs domain := by
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
    · intro op ann present
      apply typed.2.2.opsInstantiate
      simp [Lambda.LExpr.opAnnots, present]
    · intro op present
      apply typed.2.2.opsKnown
      simp [Lambda.LExpr.getOps, present]

private abbrev SubAgrees (entry : CompilerScopes) (context : ReadContext)
    (factory : Lambda.Factory Core.CoreLParams) (unwritten : List Core.CoreIdent)
    (operand : Boole.Expr) : Prop :=
  ∀ {after : TranslateState} {value : TypedExpr} {raw target : Core.Expression.Expr}
    {ty : Lambda.LMonoTy},
    expr operand context entry.source = .ok (value, entry.source) →
    toCoreExpr operand entry.lowering = .ok (raw, after) →
    target.eraseTypes = raw.eraseTypes →
    ExprWellTyped entry.context entry.variables target ty →
    ready unwritten target = true →
    after = entry.lowering ∧ Agrees entry.source factory unwritten value target

private theorem int_bin_agrees (op : IntBin)
    {entry : CompilerScopes} {after : TranslateState}
    {factory : Lambda.Factory Core.CoreLParams} {unwritten : List Core.CoreIdent}
    {context : ReadContext} {range tr : SourceRange} {left right : Boole.Expr}
    {value : TypedExpr} {raw target : Core.Expression.Expr} {ty : Lambda.LMonoTy}
    (aligned : ScopesAgree entry)
    (ambient : ∀ fn : Lambda.LFunc Core.CoreLParams,
      Core.Factory[fn.name.name]? = some fn → factory[fn.name.name]? = some fn)
    (built : expr (op.atInt range tr left right) context entry.source = .ok (value, entry.source))
    (lowered : toCoreExpr (op.atInt range tr left right) entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (typed : ExprWellTyped entry.context entry.variables target ty)
    (readable : ready unwritten target = true)
    (leftIH : SubAgrees entry context factory unwritten left)
    (rightIH : SubAgrees entry context factory unwritten right) :
    after = entry.lowering ∧ Agrees entry.source factory unwritten value target := by
  obtain ⟨lhs, rhs, lhsBuilt, rhsBuilt, lhsSort, rhsSort, valueSort, compiled⟩ :=
    compiled_int_bin op built
  obtain ⟨middle, leftRaw, rightRaw, leftLowered, rightLowered, rfl⟩ := lower_int_bin op lowered
  have signature : entry.context.functions[op.coreName]? = some op.func := by
    simpa [op.nameEq] using aligned.builtins op.func (op.nameEq.symm ▸ op.inFactory)
  obtain ⟨scheme, closed, opShape⟩ := op.shape
  obtain ⟨leftTarget, rightTarget, rfl, leftErased, rightErased⟩ :=
    typed_bin_origin opShape typed signature scheme closed erased
  have ann : ∃ cod, op.declared = .arrow .int (.arrow .int cod) := by
    cases op <;> exact ⟨_, rfl⟩
  obtain ⟨cod, ann⟩ := ann
  have ⟨leftTyped, rightTyped⟩ := typed_same_domains (ann ▸ opShape ▸ typed)
  have reads : ready unwritten leftTarget = true ∧ ready unwritten rightTarget = true := by
    simp [ready, Core.CmdType.freeVars, Lambda.LExpr.freeVars, List.map_append, List.all_append,
      IntBin.opExpr] at readable ⊢
    exact readable.2
  obtain ⟨rfl, leftAgrees⟩ := leftIH lhsBuilt leftLowered leftErased leftTyped reads.1
  obtain ⟨rfl, rightAgrees⟩ := rightIH rhsBuilt rightLowered rightErased rightTyped reads.2
  refine ⟨rfl, ?_⟩
  intro state env result related evaluated
  rw [compiled] at evaluated
  cases ranL : lhs.eval state with
  | error e => simp [binary, ranL, Except.bind] at evaluated
  | ok lv =>
    cases ranR : rhs.eval state with
    | error e => simp [binary, ranL, ranR, Except.bind] at evaluated
    | ok rv =>
      obtain ⟨sortL, _, encL, coreL⟩ := leftAgrees state env lv related ranL
      obtain ⟨sortR, _, encR, coreR⟩ := rightAgrees state env rv related ranR
      obtain ⟨a, rfl⟩ := value_of_sort_int (sortL.trans lhsSort)
      obtain ⟨b, rfl⟩ := value_of_sort_int (sortR.trans rhsSort)
      simp [binary, ranL, ranR, Except.bind] at evaluated
      obtain rfl := Except.ok.inj (evaluated.symm.trans (op.binaryValue_eq a b))
      obtain rfl := Option.some.inj encL
      obtain rfl := Option.some.inj encR
      have lookup : env.factory.factory[op.coreName]? = some op.func := by
        rw [related.1.factory_eq]
        simpa [op.nameEq] using ambient op.func (op.nameEq.symm ▸ op.inFactory)
      refine ⟨(op.combine_sort a b).trans valueSort.symm, ?_⟩
      cases op
      · exact ⟨_, rfl, Core.eval_intAdd lookup coreL coreR⟩
      · exact ⟨_, rfl, Core.eval_intSub lookup coreL coreR⟩
      · exact ⟨_, rfl, Core.eval_intMul lookup coreL coreR⟩
      · exact ⟨_, rfl, Core.eval_intLe lookup coreL coreR⟩
      · exact ⟨_, rfl, Core.eval_intLt lookup coreL coreR⟩
      · exact ⟨_, rfl, Core.eval_intGe lookup coreL coreR⟩
      · exact ⟨_, rfl, Core.eval_intGt lookup coreL coreR⟩

private theorem int_bin_rejects_bool (op : IntBin)
    {range tr : SourceRange} {left right : Boole.Expr} {context : ReadContext}
    {scope : Scope} {value : TypedExpr}
    (built : expr (op.atBool range tr left right) context scope = .ok (value, scope)) : False := by
  cases op <;>
    (dsimp only [IntBin.atBool] at built
     rw [expr.eq_def] at built
     obtain ⟨sort, next, sorted, rest⟩ := split_run built
     obtain ⟨nextEq, _, isBool⟩ := sourceSort_literal sorted (.inr rfl)
     cases nextEq
     have sortEq : sort = .bool := isBool rfl
     cases sortEq
     simp [numeric] at rest
     cases rest)

private inductive BoolBin where
  | and | or | implies | equiv

namespace BoolBin

def bop : BoolBin → BinaryOp
  | .and => .and | .or => .or | .implies => .implies | .equiv => .iff

def coreName : BoolBin → String
  | .and => "Bool.And" | .or => "Bool.Or" | .implies => "Bool.Implies" | .equiv => "Bool.Equiv"

def expr : BoolBin → SourceRange → Boole.Expr → Boole.Expr → Boole.Expr
  | .and => .and | .or => .or | .implies => .implies | .equiv => .equiv

def func : BoolBin → Lambda.LFunc Core.CoreLParams
  | .and => (Lambda.boolAndFunc (T := Core.CoreLParams)).func
  | .or => (Lambda.boolOrFunc (T := Core.CoreLParams)).func
  | .implies => (Lambda.boolImpliesFunc (T := Core.CoreLParams)).func
  | .equiv => (Lambda.boolEquivFunc (T := Core.CoreLParams)).func

def opExpr : BoolBin → Core.Expression.Expr
  | .and => Core.boolAndOp | .or => Core.boolOrOp
  | .implies => Core.boolImpliesOp | .equiv => Core.boolEquivOp

def combine : BoolBin → Bool → Bool → Bool
  | .and => fun a b => a && b | .or => fun a b => a || b
  | .implies => fun a b => !a || b | .equiv => fun a b => a == b

theorem nameEq (op : BoolBin) : op.func.name.name = op.coreName := by cases op <;> rfl

theorem shape (op : BoolBin) :
    op.func.type = .ok (.forAll [] (.arrow .bool (.arrow .bool .bool))) ∧
      op.opExpr = .op () ⟨op.coreName, ()⟩ (some (.arrow .bool (.arrow .bool .bool))) := by
  cases op <;> exact ⟨rfl, rfl⟩

theorem inFactory (op : BoolBin) : Core.Factory[op.coreName]? = some op.func := by
  cases op
  · exact Core.coreFactory_get?_of_mem (wf := Lambda.boolAndFunc (T := Core.CoreLParams)) (by
      refine Array.mem_map.mpr ⟨Lambda.boolAndFunc (T := Core.CoreLParams), ?_, rfl⟩
      rw [Array.mem_def]; unfold Core.WFFactoryArray
      simp only [Array.toList_appendList]
      repeat (first | exact List.Mem.head _ | apply List.Mem.tail))
  · exact Core.coreFactory_get?_of_mem (wf := Lambda.boolOrFunc (T := Core.CoreLParams)) (by
      refine Array.mem_map.mpr ⟨Lambda.boolOrFunc (T := Core.CoreLParams), ?_, rfl⟩
      rw [Array.mem_def]; unfold Core.WFFactoryArray
      simp only [Array.toList_appendList]
      repeat (first | exact List.Mem.head _ | apply List.Mem.tail))
  · exact Core.coreFactory_get?_of_mem (wf := Lambda.boolImpliesFunc (T := Core.CoreLParams)) (by
      refine Array.mem_map.mpr ⟨Lambda.boolImpliesFunc (T := Core.CoreLParams), ?_, rfl⟩
      rw [Array.mem_def]; unfold Core.WFFactoryArray
      simp only [Array.toList_appendList]
      repeat (first | exact List.Mem.head _ | apply List.Mem.tail))
  · exact Core.coreFactory_get?_of_mem (wf := Lambda.boolEquivFunc (T := Core.CoreLParams)) (by
      refine Array.mem_map.mpr ⟨Lambda.boolEquivFunc (T := Core.CoreLParams), ?_, rfl⟩
      rw [Array.mem_def]; unfold Core.WFFactoryArray
      simp only [Array.toList_appendList]
      repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

end BoolBin

private theorem compiled_bool_bin (op : BoolBin)
    {range : SourceRange} {left right : Boole.Expr} {context : ReadContext}
    {scope : Scope} {value : TypedExpr}
    (built : expr (op.expr range left right) context scope = .ok (value, scope)) :
    ∃ lhs rhs, expr left context scope = .ok (lhs, scope) ∧
      expr right context scope = .ok (rhs, scope) ∧
      lhs.sort = .bool ∧ rhs.sort = .bool ∧
      value.sort = .bool ∧ value.eval = binary op.bop lhs.eval rhs.eval := by
  cases op <;> dsimp only [BoolBin.expr, BoolBin.bop] at built ⊢
  case and =>
    rw [expr.eq_def] at built
    change ((expr left context >>= fun lhs => expr right context >>= fun rhs =>
      typedBinary range .and .bool .bool lhs rhs) scope) = .ok (value, scope) at built
    exact typed_binary_parts built
  case or =>
    rw [expr.eq_def] at built
    change ((expr left context >>= fun lhs => expr right context >>= fun rhs =>
      typedBinary range .or .bool .bool lhs rhs) scope) = .ok (value, scope) at built
    exact typed_binary_parts built
  case implies =>
    rw [expr.eq_def] at built
    change ((expr left context >>= fun lhs => expr right context >>= fun rhs =>
      typedBinary range .implies .bool .bool lhs rhs) scope) = .ok (value, scope) at built
    exact typed_binary_parts built
  case equiv =>
    rw [expr.eq_def] at built
    change ((expr left context >>= fun lhs => expr right context >>= fun rhs =>
      typedBinary range .iff .bool .bool lhs rhs) scope) = .ok (value, scope) at built
    exact typed_binary_parts built

private theorem lower_bool_bin (op : BoolBin)
    {range : SourceRange} {left right : Boole.Expr} {entry : TranslateState}
    {raw : Core.Expression.Expr} {final : TranslateState}
    (lowered : toCoreExpr (op.expr range left right) entry = .ok (raw, final)) :
    ∃ middle leftRaw rightRaw, toCoreExpr left entry = .ok (leftRaw, middle) ∧
      toCoreExpr right middle = .ok (rightRaw, final) ∧
      raw = .app () (.app () op.opExpr leftRaw) rightRaw := by
  cases op <;>
    (dsimp only [BoolBin.expr, BoolBin.opExpr] at lowered ⊢
     rw [toCoreExpr.eq_def] at lowered
     simp only [toCoreQuantExpr?, bind, StateT.bind, Except.bind] at lowered
     cases leftRun : toCoreExpr left entry with
     | error e => simp [leftRun] at lowered
     | ok p =>
       obtain ⟨leftRaw', middle⟩ := p
       simp only [leftRun] at lowered
       cases rightRun : toCoreExpr right middle with
       | error e => simp [rightRun] at lowered
       | ok q =>
         obtain ⟨rightRaw', _⟩ := q
         simp only [rightRun, mkCoreApp, Lambda.LExpr.mkApp, pure, StateT.pure,
           Except.pure] at lowered
         have pairEq := Except.ok.inj lowered
         cases congrArg Prod.snd pairEq
         exact ⟨middle, leftRaw', rightRaw', rfl, rightRun,
           (congrArg Prod.fst pairEq).symm⟩)

private theorem bool_bin_agrees (op : BoolBin)
    {entry : CompilerScopes} {after : TranslateState}
    {factory : Lambda.Factory Core.CoreLParams} {unwritten : List Core.CoreIdent}
    {context : ReadContext} {range : SourceRange} {left right : Boole.Expr}
    {value : TypedExpr} {raw target : Core.Expression.Expr} {ty : Lambda.LMonoTy}
    (aligned : ScopesAgree entry)
    (ambient : ∀ fn : Lambda.LFunc Core.CoreLParams,
      Core.Factory[fn.name.name]? = some fn → factory[fn.name.name]? = some fn)
    (built : expr (op.expr range left right) context entry.source = .ok (value, entry.source))
    (lowered : toCoreExpr (op.expr range left right) entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (typed : ExprWellTyped entry.context entry.variables target ty)
    (readable : ready unwritten target = true)
    (leftIH : SubAgrees entry context factory unwritten left)
    (rightIH : SubAgrees entry context factory unwritten right) :
    after = entry.lowering ∧ Agrees entry.source factory unwritten value target := by
  obtain ⟨lhs, rhs, lhsBuilt, rhsBuilt, lhsSort, rhsSort, valueSort, compiled⟩ :=
    compiled_bool_bin op built
  obtain ⟨_, leftRaw, rightRaw, leftLowered, rightLowered, rfl⟩ := lower_bool_bin op lowered
  have signature : entry.context.functions[op.coreName]? = some op.func := by
    simpa [op.nameEq] using aligned.builtins op.func (by
      simpa [op.nameEq] using op.inFactory)
  obtain ⟨scheme, opShape⟩ := op.shape
  have erasedRaw : target.eraseTypes =
      (.app () (.app () (.op () ⟨op.coreName, ()⟩ none) leftRaw) rightRaw :
        Core.Expression.Expr).eraseTypes := by
    rw [opShape] at erased
    simpa [Lambda.LExpr.eraseTypes] using erased
  obtain ⟨leftTarget, rightTarget, rfl, leftErased, rightErased⟩ :=
    typed_bin_origin opShape typed signature scheme (by rfl) erasedRaw
  have ⟨leftTyped, rightTyped⟩ := typed_same_domains (opShape ▸ typed)
  have reads : ready unwritten leftTarget = true ∧ ready unwritten rightTarget = true := by
    simp [ready, Core.CmdType.freeVars, Lambda.LExpr.freeVars, List.map_append, List.all_append,
      BoolBin.opExpr] at readable ⊢
    exact readable.2
  obtain ⟨rfl, leftAgrees⟩ := leftIH lhsBuilt leftLowered leftErased leftTyped reads.1
  obtain ⟨rfl, rightAgrees⟩ := rightIH rhsBuilt rightLowered rightErased rightTyped reads.2
  refine ⟨rfl, ?_⟩
  intro state env result related evaluated
  rw [compiled] at evaluated
  cases ranL : lhs.eval state with
  | error e => simp [binary, ranL, Except.bind] at evaluated
  | ok lv =>
    cases ranR : rhs.eval state with
    | error e => simp [binary, ranL, ranR, Except.bind] at evaluated
    | ok rv =>
      obtain ⟨sortL, _, encL, coreL⟩ := leftAgrees state env lv related ranL
      obtain ⟨sortR, _, encR, coreR⟩ := rightAgrees state env rv related ranR
      obtain ⟨a, rfl⟩ := value_of_sort_bool (sortL.trans lhsSort)
      obtain ⟨b, rfl⟩ := value_of_sort_bool (sortR.trans rhsSort)
      simp [binary, ranL, ranR, Except.bind] at evaluated
      have values : binaryValue op.bop (.bool a) (.bool b) = .ok (.bool (op.combine a b)) := by
        cases op <;> exact binaryValue_bool _ a b
      obtain rfl := Except.ok.inj (evaluated.symm.trans values)
      obtain rfl := Option.some.inj encL
      obtain rfl := Option.some.inj encR
      have lookup : env.factory.factory[op.coreName]? = some op.func := by
        rw [related.1.factory_eq]
        simpa [op.nameEq] using ambient op.func (by simpa [op.nameEq] using op.inFactory)
      refine ⟨valueSort.symm, ?_⟩
      cases op
      · exact ⟨_, rfl, eval_boolAnd lookup coreL coreR⟩
      · exact ⟨_, rfl, eval_boolOr lookup coreL coreR⟩
      · exact ⟨_, rfl, eval_boolImplies lookup coreL coreR⟩
      · exact ⟨_, rfl, eval_boolEquiv lookup coreL coreR⟩

private theorem compiled_bool_eq
    {range tr : SourceRange} {left right : Boole.Expr} {context : ReadContext}
    {scope : Scope} {value : TypedExpr}
    (built : expr (.equal range (.bool tr) left right) context scope = .ok (value, scope)) :
    ∃ lhs rhs, expr left context scope = .ok (lhs, scope) ∧
      expr right context scope = .ok (rhs, scope) ∧
      lhs.sort = .bool ∧ rhs.sort = .bool ∧
      value.sort = .bool ∧ value.eval = binary .eq lhs.eval rhs.eval := by
  rw [expr.eq_def] at built
  obtain ⟨sort, next, sorted, rest⟩ := split_run built
  obtain ⟨nextEq, _, isBool⟩ := sourceSort_literal sorted (.inr rfl)
  cases nextEq
  have sortEq : sort = .bool := isBool rfl
  cases sortEq
  change ((expr left context >>= fun lhs => expr right context >>= fun rhs =>
    typedBinary range .eq .bool .bool lhs rhs) scope) = .ok (value, scope) at rest
  exact typed_binary_parts rest

private theorem lower_bool_eq
    {range tr : SourceRange} {left right : Boole.Expr} {entry : TranslateState}
    {raw : Core.Expression.Expr} {final : TranslateState}
    (lowered : toCoreExpr (.equal range (.bool tr) left right) entry = .ok (raw, final)) :
    ∃ middle leftRaw rightRaw, toCoreExpr left entry = .ok (leftRaw, middle) ∧
      toCoreExpr right middle = .ok (rightRaw, final) ∧
      raw = .eq () leftRaw rightRaw := by
  rw [toCoreExpr.eq_def] at lowered
  simp only [toCoreQuantExpr?, bind, StateT.bind, Except.bind] at lowered
  cases leftRun : toCoreExpr left entry with
  | error e => simp [leftRun] at lowered
  | ok p =>
    obtain ⟨leftRaw', middle⟩ := p
    simp only [leftRun] at lowered
    cases rightRun : toCoreExpr right middle with
    | error e => simp [rightRun] at lowered
    | ok q =>
      obtain ⟨rightRaw', _⟩ := q
      simp only [rightRun, pure, StateT.pure, Except.pure] at lowered
      have pairEq := Except.ok.inj lowered
      cases congrArg Prod.snd pairEq
      exact ⟨middle, leftRaw', rightRaw', rfl, rightRun, (congrArg Prod.fst pairEq).symm⟩

private theorem int_eq_agrees
    {entry : CompilerScopes} {after : TranslateState}
    {factory : Lambda.Factory Core.CoreLParams} {unwritten : List Core.CoreIdent}
    {context : ReadContext} {range tr : SourceRange} {left right : Boole.Expr}
    {value : TypedExpr} {raw target : Core.Expression.Expr} {mono : Lambda.LMonoTy}
    (built : expr (.equal range (.int tr) left right) context entry.source =
      .ok (value, entry.source))
    (lowered : toCoreExpr (.equal range (.int tr) left right) entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (typed : ExprWellTyped entry.context entry.variables target mono)
    (readable : ready unwritten target = true)
    (leftIH : SubAgrees entry context factory unwritten left)
    (rightIH : SubAgrees entry context factory unwritten right) :
    after = entry.lowering ∧ Agrees entry.source factory unwritten value target := by
  obtain ⟨lhs, rhs, lhsBuilt, rhsBuilt, lhsSort, rhsSort, valueSort, compiled⟩ :=
    compiled_int_eq built
  obtain ⟨_, leftRaw, rightRaw, leftLowered, rightLowered, rfl⟩ := lowerIntEq_parts lowered
  obtain ⟨leftTarget, rightTarget, rfl, leftErased, rightErased⟩ := erase_eq_inv erased
  have reads : ready unwritten leftTarget = true ∧ ready unwritten rightTarget = true := by
    simp [ready, Core.CmdType.freeVars, Lambda.LExpr.freeVars, List.all_append] at readable ⊢
    exact readable
  obtain ⟨_, leftTyped, rightTyped⟩ := typed_eq_operands typed
  obtain ⟨rfl, leftAgrees⟩ := leftIH lhsBuilt leftLowered leftErased leftTyped reads.1
  obtain ⟨rfl, rightAgrees⟩ := rightIH rhsBuilt rightLowered rightErased rightTyped reads.2
  refine ⟨rfl, ?_⟩
  intro state env result related evaluated
  rw [compiled] at evaluated
  cases ranL : lhs.eval state with
  | error e => simp [binary, ranL, Except.bind] at evaluated
  | ok lv =>
    cases ranR : rhs.eval state with
    | error e => simp [binary, ranL, ranR, Except.bind] at evaluated
    | ok rv =>
      obtain ⟨sortL, _, encL, coreL⟩ := leftAgrees state env lv related ranL
      obtain ⟨sortR, _, encR, coreR⟩ := rightAgrees state env rv related ranR
      obtain ⟨a, rfl⟩ := value_of_sort_int (sortL.trans lhsSort)
      obtain ⟨b, rfl⟩ := value_of_sort_int (sortR.trans rhsSort)
      simp [binary, ranL, ranR, Except.bind] at evaluated
      obtain rfl := Except.ok.inj (evaluated.symm.trans (binaryValue_int .eq a b))
      obtain rfl := Option.some.inj encL
      obtain rfl := Option.some.inj encR
      by_cases same : a = b
      · subst b
        simp only [beq_self_eq_true]
        exact ⟨valueSort.symm, _, rfl, Core.eval_eq_true env.factory coreL coreR⟩
      · simp only [beq_eq_false_iff_ne.mpr same]
        exact ⟨valueSort.symm, _, rfl, Core.eval_eq_false env.factory coreL coreR rfl
          (fun equal => same (Lambda.SemValue.ofInt_injective equal))⟩

private theorem bool_eq_agrees
    {entry : CompilerScopes} {after : TranslateState}
    {factory : Lambda.Factory Core.CoreLParams} {unwritten : List Core.CoreIdent}
    {context : ReadContext} {range tr : SourceRange} {left right : Boole.Expr}
    {value : TypedExpr} {raw target : Core.Expression.Expr} {mono : Lambda.LMonoTy}
    (built : expr (.equal range (.bool tr) left right) context entry.source =
      .ok (value, entry.source))
    (lowered : toCoreExpr (.equal range (.bool tr) left right) entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (typed : ExprWellTyped entry.context entry.variables target mono)
    (readable : ready unwritten target = true)
    (leftIH : SubAgrees entry context factory unwritten left)
    (rightIH : SubAgrees entry context factory unwritten right) :
    after = entry.lowering ∧ Agrees entry.source factory unwritten value target := by
  obtain ⟨lhs, rhs, lhsBuilt, rhsBuilt, lhsSort, rhsSort, valueSort, compiled⟩ :=
    compiled_bool_eq built
  obtain ⟨_, leftRaw, rightRaw, leftLowered, rightLowered, rfl⟩ := lower_bool_eq lowered
  obtain ⟨leftTarget, rightTarget, rfl, leftErased, rightErased⟩ := erase_eq_inv erased
  have reads : ready unwritten leftTarget = true ∧ ready unwritten rightTarget = true := by
    simp [ready, Core.CmdType.freeVars, Lambda.LExpr.freeVars, List.all_append] at readable ⊢
    exact readable
  obtain ⟨_, leftTyped, rightTyped⟩ := typed_eq_operands typed
  obtain ⟨rfl, leftAgrees⟩ := leftIH lhsBuilt leftLowered leftErased leftTyped reads.1
  obtain ⟨rfl, rightAgrees⟩ := rightIH rhsBuilt rightLowered rightErased rightTyped reads.2
  refine ⟨rfl, ?_⟩
  intro state env result related evaluated
  rw [compiled] at evaluated
  cases ranL : lhs.eval state with
  | error e => simp [binary, ranL, Except.bind] at evaluated
  | ok lv =>
    cases ranR : rhs.eval state with
    | error e => simp [binary, ranL, ranR, Except.bind] at evaluated
    | ok rv =>
      obtain ⟨sortL, _, encL, coreL⟩ := leftAgrees state env lv related ranL
      obtain ⟨sortR, _, encR, coreR⟩ := rightAgrees state env rv related ranR
      obtain ⟨a, rfl⟩ := value_of_sort_bool (sortL.trans lhsSort)
      obtain ⟨b, rfl⟩ := value_of_sort_bool (sortR.trans rhsSort)
      simp [binary, ranL, ranR, Except.bind] at evaluated
      obtain rfl := Except.ok.inj (evaluated.symm.trans (binaryValue_bool .eq a b))
      obtain rfl := Option.some.inj encL
      obtain rfl := Option.some.inj encR
      by_cases same : a = b
      · subst b
        simp only [beq_self_eq_true]
        exact ⟨valueSort.symm, _, rfl, Core.eval_eq_true env.factory coreL coreR⟩
      · simp only [beq_eq_false_iff_ne.mpr same]
        exact ⟨valueSort.symm, _, rfl, Core.eval_eq_false env.factory coreL coreR rfl
          (fun equal => same (Lambda.SemValue.ofBool_injective equal))⟩

private theorem compiled_int_ne
    {range tr : SourceRange} {left right : Boole.Expr} {context : ReadContext}
    {scope : Scope} {value : TypedExpr}
    (built : expr (.not_equal range (.int tr) left right) context scope = .ok (value, scope)) :
    ∃ lhs rhs, expr left context scope = .ok (lhs, scope) ∧
      expr right context scope = .ok (rhs, scope) ∧
      lhs.sort = .int ∧ rhs.sort = .int ∧
      value.sort = .bool ∧ value.eval = binary .ne lhs.eval rhs.eval := by
  rw [expr.eq_def] at built
  obtain ⟨sort, next, sorted, rest⟩ := split_run built
  obtain ⟨nextEq, isInt, _⟩ := sourceSort_literal sorted (.inl rfl)
  cases nextEq
  have sortEq : sort = .int := isInt rfl
  cases sortEq
  change ((expr left context >>= fun lhs => expr right context >>= fun rhs =>
    typedBinary range .ne .bool .int lhs rhs) scope) = .ok (value, scope) at rest
  exact typed_binary_parts rest

private theorem compiled_bool_ne
    {range tr : SourceRange} {left right : Boole.Expr} {context : ReadContext}
    {scope : Scope} {value : TypedExpr}
    (built : expr (.not_equal range (.bool tr) left right) context scope = .ok (value, scope)) :
    ∃ lhs rhs, expr left context scope = .ok (lhs, scope) ∧
      expr right context scope = .ok (rhs, scope) ∧
      lhs.sort = .bool ∧ rhs.sort = .bool ∧
      value.sort = .bool ∧ value.eval = binary .ne lhs.eval rhs.eval := by
  rw [expr.eq_def] at built
  obtain ⟨sort, next, sorted, rest⟩ := split_run built
  obtain ⟨nextEq, _, isBool⟩ := sourceSort_literal sorted (.inr rfl)
  cases nextEq
  have sortEq : sort = .bool := isBool rfl
  cases sortEq
  change ((expr left context >>= fun lhs => expr right context >>= fun rhs =>
    typedBinary range .ne .bool .bool lhs rhs) scope) = .ok (value, scope) at rest
  exact typed_binary_parts rest

private theorem lower_ne
    {range : SourceRange} {left right : Boole.Expr} {ty : Boole.Type}
    {entry : TranslateState} {raw : Core.Expression.Expr} {final : TranslateState}
    (lowered : toCoreExpr (.not_equal range ty left right) entry = .ok (raw, final)) :
    ∃ middle leftRaw rightRaw, toCoreExpr left entry = .ok (leftRaw, middle) ∧
      toCoreExpr right middle = .ok (rightRaw, final) ∧
      raw = .app () Core.boolNotOp (.eq () leftRaw rightRaw) := by
  rw [toCoreExpr.eq_def] at lowered
  simp only [toCoreQuantExpr?, bind, StateT.bind, Except.bind] at lowered
  cases leftRun : toCoreExpr left entry with
  | error e => simp [leftRun] at lowered
  | ok p =>
    obtain ⟨leftRaw', middle⟩ := p
    simp only [leftRun] at lowered
    cases rightRun : toCoreExpr right middle with
    | error e => simp [rightRun] at lowered
    | ok q =>
      obtain ⟨rightRaw', _⟩ := q
      simp only [rightRun, pure, StateT.pure, Except.pure] at lowered
      have pairEq := Except.ok.inj lowered
      cases congrArg Prod.snd pairEq
      exact ⟨middle, leftRaw', rightRaw', rfl, rightRun, (congrArg Prod.fst pairEq).symm⟩

private theorem int_ne_agrees
    {entry : CompilerScopes} {after : TranslateState}
    {factory : Lambda.Factory Core.CoreLParams} {unwritten : List Core.CoreIdent}
    {context : ReadContext} {range tr : SourceRange} {left right : Boole.Expr}
    {value : TypedExpr} {raw target : Core.Expression.Expr} {mono : Lambda.LMonoTy}
    (aligned : ScopesAgree entry)
    (ambient : ∀ fn : Lambda.LFunc Core.CoreLParams,
      Core.Factory[fn.name.name]? = some fn → factory[fn.name.name]? = some fn)
    (built : expr (.not_equal range (.int tr) left right) context entry.source =
      .ok (value, entry.source))
    (lowered : toCoreExpr (.not_equal range (.int tr) left right) entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (typed : ExprWellTyped entry.context entry.variables target mono)
    (readable : ready unwritten target = true)
    (leftIH : SubAgrees entry context factory unwritten left)
    (rightIH : SubAgrees entry context factory unwritten right) :
    after = entry.lowering ∧ Agrees entry.source factory unwritten value target := by
  obtain ⟨lhs, rhs, lhsBuilt, rhsBuilt, lhsSort, rhsSort, valueSort, compiled⟩ :=
    compiled_int_ne built
  obtain ⟨_, leftRaw, rightRaw, leftLowered, rightLowered, rfl⟩ := lower_ne lowered
  obtain ⟨argument, rfl, argErased, argTyped⟩ := typed_boolNot_origin typed
    (aligned.builtins (Lambda.boolNotFunc (T := Core.CoreLParams)).func Core.coreFactory_boolNot)
    erased
  obtain ⟨leftTarget, rightTarget, rfl, leftErased, rightErased⟩ := erase_eq_inv argErased
  obtain ⟨_, leftTyped, rightTyped⟩ := typed_eq_operands argTyped
  have reads : ready unwritten leftTarget = true ∧ ready unwritten rightTarget = true := by
    simp [ready, Core.CmdType.freeVars, Lambda.LExpr.freeVars, Core.boolNotOp,
      List.all_append] at readable ⊢
    exact readable.2
  obtain ⟨rfl, leftAgrees⟩ := leftIH lhsBuilt leftLowered leftErased leftTyped reads.1
  obtain ⟨rfl, rightAgrees⟩ := rightIH rhsBuilt rightLowered rightErased rightTyped reads.2
  refine ⟨rfl, ?_⟩
  intro state env result related evaluated
  rw [compiled] at evaluated
  cases ranL : lhs.eval state with
  | error e => simp [binary, ranL, Except.bind] at evaluated
  | ok lv =>
    cases ranR : rhs.eval state with
    | error e => simp [binary, ranL, ranR, Except.bind] at evaluated
    | ok rv =>
      obtain ⟨sortL, _, encL, coreL⟩ := leftAgrees state env lv related ranL
      obtain ⟨sortR, _, encR, coreR⟩ := rightAgrees state env rv related ranR
      obtain ⟨a, rfl⟩ := value_of_sort_int (sortL.trans lhsSort)
      obtain ⟨b, rfl⟩ := value_of_sort_int (sortR.trans rhsSort)
      simp [binary, ranL, ranR, Except.bind] at evaluated
      obtain rfl := Except.ok.inj (evaluated.symm.trans (binaryValue_int .ne a b))
      obtain rfl := Option.some.inj encL
      obtain rfl := Option.some.inj encR
      have lookup : env.factory.factory["Bool.Not"]? =
          some (Lambda.boolNotFunc (T := Core.CoreLParams)).func := by
        rw [related.1.factory_eq]
        exact ambient (Lambda.boolNotFunc (T := Core.CoreLParams)).func Core.coreFactory_boolNot
      by_cases same : a = b
      · subst b
        simp only [beq_self_eq_true, Bool.not_true]
        exact ⟨valueSort.symm, _, rfl,
          eval_boolNot lookup (Core.eval_eq_true env.factory coreL coreR)⟩
      · simp only [beq_eq_false_iff_ne.mpr same, Bool.not_false]
        exact ⟨valueSort.symm, _, rfl, eval_boolNot lookup
          (Core.eval_eq_false env.factory coreL coreR rfl
            (fun equal => same (Lambda.SemValue.ofInt_injective equal)))⟩

private theorem bool_ne_agrees
    {entry : CompilerScopes} {after : TranslateState}
    {factory : Lambda.Factory Core.CoreLParams} {unwritten : List Core.CoreIdent}
    {context : ReadContext} {range tr : SourceRange} {left right : Boole.Expr}
    {value : TypedExpr} {raw target : Core.Expression.Expr} {mono : Lambda.LMonoTy}
    (aligned : ScopesAgree entry)
    (ambient : ∀ fn : Lambda.LFunc Core.CoreLParams,
      Core.Factory[fn.name.name]? = some fn → factory[fn.name.name]? = some fn)
    (built : expr (.not_equal range (.bool tr) left right) context entry.source =
      .ok (value, entry.source))
    (lowered : toCoreExpr (.not_equal range (.bool tr) left right) entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (typed : ExprWellTyped entry.context entry.variables target mono)
    (readable : ready unwritten target = true)
    (leftIH : SubAgrees entry context factory unwritten left)
    (rightIH : SubAgrees entry context factory unwritten right) :
    after = entry.lowering ∧ Agrees entry.source factory unwritten value target := by
  obtain ⟨lhs, rhs, lhsBuilt, rhsBuilt, lhsSort, rhsSort, valueSort, compiled⟩ :=
    compiled_bool_ne built
  obtain ⟨_, leftRaw, rightRaw, leftLowered, rightLowered, rfl⟩ := lower_ne lowered
  obtain ⟨argument, rfl, argErased, argTyped⟩ := typed_boolNot_origin typed
    (aligned.builtins (Lambda.boolNotFunc (T := Core.CoreLParams)).func Core.coreFactory_boolNot)
    erased
  obtain ⟨leftTarget, rightTarget, rfl, leftErased, rightErased⟩ := erase_eq_inv argErased
  obtain ⟨_, leftTyped, rightTyped⟩ := typed_eq_operands argTyped
  have reads : ready unwritten leftTarget = true ∧ ready unwritten rightTarget = true := by
    simp [ready, Core.CmdType.freeVars, Lambda.LExpr.freeVars, Core.boolNotOp,
      List.all_append] at readable ⊢
    exact readable.2
  obtain ⟨rfl, leftAgrees⟩ := leftIH lhsBuilt leftLowered leftErased leftTyped reads.1
  obtain ⟨rfl, rightAgrees⟩ := rightIH rhsBuilt rightLowered rightErased rightTyped reads.2
  refine ⟨rfl, ?_⟩
  intro state env result related evaluated
  rw [compiled] at evaluated
  cases ranL : lhs.eval state with
  | error e => simp [binary, ranL, Except.bind] at evaluated
  | ok lv =>
    cases ranR : rhs.eval state with
    | error e => simp [binary, ranL, ranR, Except.bind] at evaluated
    | ok rv =>
      obtain ⟨sortL, _, encL, coreL⟩ := leftAgrees state env lv related ranL
      obtain ⟨sortR, _, encR, coreR⟩ := rightAgrees state env rv related ranR
      obtain ⟨a, rfl⟩ := value_of_sort_bool (sortL.trans lhsSort)
      obtain ⟨b, rfl⟩ := value_of_sort_bool (sortR.trans rhsSort)
      simp [binary, ranL, ranR, Except.bind] at evaluated
      obtain rfl := Except.ok.inj (evaluated.symm.trans (binaryValue_bool .ne a b))
      obtain rfl := Option.some.inj encL
      obtain rfl := Option.some.inj encR
      have lookup : env.factory.factory["Bool.Not"]? =
          some (Lambda.boolNotFunc (T := Core.CoreLParams)).func := by
        rw [related.1.factory_eq]
        exact ambient (Lambda.boolNotFunc (T := Core.CoreLParams)).func Core.coreFactory_boolNot
      by_cases same : a = b
      · subst b
        simp only [beq_self_eq_true, Bool.not_true]
        exact ⟨valueSort.symm, _, rfl,
          eval_boolNot lookup (Core.eval_eq_true env.factory coreL coreR)⟩
      · simp only [beq_eq_false_iff_ne.mpr same, Bool.not_false]
        exact ⟨valueSort.symm, _, rfl, eval_boolNot lookup
          (Core.eval_eq_false env.factory coreL coreR rfl
            (fun equal => same (Lambda.SemValue.ofBool_injective equal)))⟩

open Lambda in
private theorem denoteEval_app_op_int
    {M : ModeledFactory Core.CoreLParams} {σ : ValStore Core.CoreLParams}
    {m m' : Core.CoreLParams.Metadata} {o : Identifier Core.CoreLParams.IDMeta}
    {e : LExpr Core.CoreLParams.mono} {i' : Int} :
    (LExpr.app m (.op m' o (some (LMonoTy.arrow .int .int))) e).denoteEval M σ =
        some (SemValue.ofInt M.model.tcInterp i') ↔
      ∃ i, e.denoteEval M σ = some (SemValue.ofInt M.model.tcInterp i) ∧
        i' = (M.model.opInterp o.name (LSort.mkArrow .int [.int]) : Int → Int) i := by
  letI := M.model.allInhabited
  have hdef : σ.Defines M.model.tcInterp
      (LExpr.app m (.op m' o (some (LMonoTy.arrow .int .int))) e) ↔
      σ.Defines M.model.tcInterp e := by
    simp only [ValStore.Defines, LExpr.LExpr.getVars, List.nil_append]
  rw [LExpr.denoteEval_eq_ofInt_iff (T := Core.CoreLParams), hdef]
  constructor
  · rintro ⟨hd, h, hi⟩
    obtain ⟨aty, hfn, harg⟩ := HasTypeA.app_inv h
    have : aty = .int := by
      have := HasTypeA.op_inv hfn
      simp only [LMonoTy.arrow, LMonoTy.tcons.injEq, List.cons.injEq, and_true, true_and] at this
      exact this
    subst this
    refine ⟨_, (LExpr.denoteEval_eq_ofInt_iff (T := Core.CoreLParams)).mpr ⟨hd, harg, rfl⟩, ?_⟩
    rw [← hi]
    exact (Denotes_denote (Denotes.app (h := h) .nil (Denotes.op (h := hfn) .nil)
      (denote_Denotes M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp)
        M.tyVarVal .nil _ _ harg))).symm
  · rintro ⟨i, he, rfl⟩
    obtain ⟨hd, harg, hi⟩ := (LExpr.denoteEval_eq_ofInt_iff (T := Core.CoreLParams)).mp he
    have h : ((LExpr.app m (.op m' o (some (LMonoTy.arrow .int .int))) e).annotateFvars
        σ.ann).HasTypeA [] .int := .app .op harg
    refine ⟨hd, h, ?_⟩
    have hden := denote_Denotes M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp)
      M.tyVarVal .nil _ _ harg
    have hdenApp := Denotes_denote (Denotes.app (h := h) .nil (Denotes.op (h := .op) .nil) hden)
    rw [← hi]
    exact hdenApp.symm

private theorem coreFactory_intNeg :
    Core.Factory["Int.Neg"]? = some (Lambda.intNegFunc (T := Core.CoreLParams)).func :=
  Core.coreFactory_get?_of_mem (wf := Lambda.intNegFunc (T := Core.CoreLParams)) (by
    refine Array.mem_map.mpr ⟨Lambda.intNegFunc (T := Core.CoreLParams), ?_, rfl⟩
    rw [Array.mem_def]; unfold Core.WFFactoryArray
    simp only [Array.toList_appendList]
    repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

private theorem intNeg_opInterp
    {factory : Lambda.Factory Core.CoreLParams} (model : Lambda.Interp factory)
    (lookup : factory["Int.Neg"]? = some (Lambda.intNegFunc (T := Core.CoreLParams)).func)
    (a : Int) :
    (model.opInterp "Int.Neg" (Lambda.LSort.mkArrow .int [.int]) a : Int) = -a :=
  (Core.opInterp_of_concreteEval model lookup rfl (args := [.intConst () a])
    (res := .intConst () (-a)) rfl (fun _ => .int) (fun _ s =>
      @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s))
    (.cons .const .nil) .const).symm

private theorem eval_intNeg {factory : Core.Expression.Factory} {store : Core.CoreStore}
    {expr : Core.Expression.Expr} {a : Int}
    (lookup : factory.factory["Int.Neg"]? =
      some (Lambda.intNegFunc (T := Core.CoreLParams)).func)
    (eval : Core.Expression.eval factory store expr =
      some (Lambda.SemValue.ofInt factory.model.tcInterp a)) :
    Core.Expression.eval factory store (.app () Core.intNegOp expr) =
      some (Lambda.SemValue.ofInt factory.model.tcInterp (-a)) := by
  have shape : Core.intNegOp = .op () ⟨"Int.Neg", ()⟩ (some (.arrow .int .int)) := rfl
  rw [shape]
  exact (denoteEval_app_op_int (M := factory) (σ := store)).mpr
    ⟨a, eval, (intNeg_opInterp factory.model lookup a).symm⟩

private theorem unary_neg_int {state : State} {e : Expression} {n : Int}
    (h : e state = .ok (.int n)) :
    Expression.unary .neg e state = .ok (.int (-n)) := by
  unfold Expression.unary
  rw [h]
  simp only [bind, Except.bind, pure, Except.pure]
  rfl

private theorem compiled_int_neg
    {range tr : SourceRange} {operand : Boole.Expr} {context : ReadContext}
    {scope : Scope} {value : TypedExpr}
    (built : expr (.neg_expr range (.int tr) operand) context scope = .ok (value, scope)) :
    ∃ inner, expr operand context scope = .ok (inner, scope) ∧ inner.sort = .int ∧
      value.sort = .int ∧ value.eval = Expression.unary .neg inner.eval := by
  rw [expr.eq_def] at built
  obtain ⟨sort, next, sorted, rest⟩ := split_run built
  obtain ⟨nextEq, isInt, _⟩ := sourceSort_literal sorted (.inl rfl)
  cases nextEq
  have sortEq : sort = .int := isInt rfl
  cases sortEq
  change ((expr operand context >>= fun inner => inner.expect .int range >>= fun ev =>
    pure ⟨.int, Expression.unary .neg ev⟩) scope) = .ok (value, scope) at rest
  obtain ⟨inner, mid, ran, rest⟩ := split_run rest
  cases expr_readOnly _ _ _ _ _ ran
  obtain ⟨ev, last, expected, done⟩ := split_run rest
  unfold TypedExpr.expect at expected
  split at expected
  · rename_i same
    cases congrArg Prod.fst (Except.ok.inj expected)
    cases congrArg Prod.snd (Except.ok.inj expected)
    cases congrArg Prod.fst (Except.ok.inj done)
    cases congrArg Prod.snd (Except.ok.inj done)
    exact ⟨inner, ran, beq_iff_eq.mp same, rfl, rfl⟩
  · contradiction

private theorem neg_rejects_bool
    {range tr : SourceRange} {operand : Boole.Expr} {context : ReadContext}
    {scope : Scope} {value : TypedExpr}
    (built : expr (.neg_expr range (.bool tr) operand) context scope = .ok (value, scope)) :
    False := by
  rw [expr.eq_def] at built
  obtain ⟨sort, next, sorted, rest⟩ := split_run built
  obtain ⟨nextEq, _, isBool⟩ := sourceSort_literal sorted (.inr rfl)
  cases nextEq
  have sortEq : sort = .bool := isBool rfl
  cases sortEq
  simp [bind, StateT.bind, Except.bind, StateT.lift, Functor.map, Except.map, reject, throw,
    throwThe, MonadExceptOf.throw] at rest

private theorem lower_int_neg
    {range tr : SourceRange} {operand : Boole.Expr} {entry : TranslateState}
    {raw : Core.Expression.Expr} {final : TranslateState}
    (lowered : toCoreExpr (.neg_expr range (.int tr) operand) entry = .ok (raw, final)) :
    ∃ innerRaw, toCoreExpr operand entry = .ok (innerRaw, final) ∧
      raw = .app () (.op () ⟨"Int.Neg", ()⟩ none) innerRaw := by
  rw [toCoreExpr.eq_def] at lowered
  simp only [toCoreQuantExpr?, toCoreTypedUn, bind, StateT.bind, Except.bind] at lowered
  cases ran : toCoreExpr operand entry with
  | error e => simp [ran] at lowered
  | ok pair =>
    obtain ⟨innerRaw, middle⟩ := pair
    simp only [ran, pure, StateT.pure, Except.pure] at lowered
    have pairEq := Except.ok.inj lowered
    cases congrArg Prod.snd pairEq
    exact ⟨innerRaw, rfl, (congrArg Prod.fst pairEq).symm⟩

private theorem typed_intNeg_origin
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    {annotated operand : Core.Expression.Expr} {ty : Lambda.LMonoTy}
    (typed : Core.TypeSpec.ExprWellTyped context scopes annotated ty)
    (signature : context.functions["Int.Neg"]? =
      some (Lambda.intNegFunc (T := Core.CoreLParams)).func)
    (erased : annotated.eraseTypes =
      (.app () (.op () ⟨"Int.Neg", ()⟩ none) operand : Core.Expression.Expr).eraseTypes) :
    ∃ argument, annotated = .app () Core.intNegOp argument ∧
      argument.eraseTypes = operand.eraseTypes ∧
      Core.TypeSpec.ExprWellTyped context scopes argument .int := by
  have opErased : Core.intNegOp.eraseTypes =
      (.op () ⟨"Int.Neg", ()⟩ none : Core.Expression.Expr) := rfl
  cases annotated <;> simp [Lambda.LExpr.eraseTypes, opErased] at erased
  case app metadata fn argument =>
    cases metadata
    obtain ⟨same, argSame⟩ := erased
    have typedApp := typed.1
    have ⟨domain, fnType, argType⟩ : ∃ domain,
        Lambda.LExpr.HasTypeA [] fn (.arrow domain ty) ∧
          Lambda.LExpr.HasTypeA [] argument domain := by
      cases typedApp with
      | app f a => exact ⟨_, f, a⟩
    cases fn <;> simp [Lambda.LExpr.eraseTypes] at same
    case op opMetadata opId annotation =>
      cases opMetadata
      subst opId
      have fnAnn : annotation = some (.arrow domain ty) := by
        cases fnType
        rfl
      rw [fnAnn] at typed
      have annEq := operatorAnnotation_eq (id := ⟨"Int.Neg", ()⟩)
        (annotation := .arrow domain ty) typed.2.2
        (by simp [Lambda.LExpr.opAnnots]) signature
        (declared := Lambda.LMonoTy.arrow .int .int) (by rfl) (by rfl)
      have domainEq : domain = .int := by
        simp only [Lambda.LMonoTy.arrow, Lambda.LMonoTy.tcons.injEq,
          List.cons.injEq, true_and] at annEq
        exact annEq.1
      rw [fnAnn, annEq]
      exact ⟨argument, rfl, argSame, typed_app_argument typed (domainEq ▸ argType)⟩

private theorem int_neg_agrees
    {entry : CompilerScopes} {after : TranslateState}
    {factory : Lambda.Factory Core.CoreLParams} {unwritten : List Core.CoreIdent}
    {context : ReadContext} {range tr : SourceRange} {operand : Boole.Expr}
    {value : TypedExpr} {raw target : Core.Expression.Expr} {mono : Lambda.LMonoTy}
    (aligned : ScopesAgree entry)
    (ambient : ∀ fn : Lambda.LFunc Core.CoreLParams,
      Core.Factory[fn.name.name]? = some fn → factory[fn.name.name]? = some fn)
    (built : expr (.neg_expr range (.int tr) operand) context entry.source =
      .ok (value, entry.source))
    (lowered : toCoreExpr (.neg_expr range (.int tr) operand) entry.lowering =
      .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (typed : ExprWellTyped entry.context entry.variables target mono)
    (readable : ready unwritten target = true)
    (ih : SubAgrees entry context factory unwritten operand) :
    after = entry.lowering ∧ Agrees entry.source factory unwritten value target := by
  obtain ⟨inner, innerBuilt, innerSort, valueSort, compiled⟩ := compiled_int_neg built
  obtain ⟨innerRaw, innerLowered, rfl⟩ := lower_int_neg lowered
  obtain ⟨argument, rfl, argErased, argTyped⟩ := typed_intNeg_origin typed
    (aligned.builtins (Lambda.intNegFunc (T := Core.CoreLParams)).func coreFactory_intNeg) erased
  have argReady : ready unwritten argument = true := by
    simp [ready, Core.CmdType.freeVars, Lambda.LExpr.freeVars, Core.intNegOp,
      List.all_append] at readable ⊢
    exact readable.2
  obtain ⟨rfl, innerAgrees⟩ := ih innerBuilt innerLowered argErased argTyped argReady
  refine ⟨rfl, ?_⟩
  intro state env result related evaluated
  cases ran : inner.eval state with
  | error e =>
    rw [compiled] at evaluated
    simp [Expression.unary, ran, bind, Except.bind] at evaluated
  | ok lv =>
    obtain ⟨sortLv, _, encoded, core⟩ := innerAgrees state env lv related ran
    obtain ⟨n, rfl⟩ := value_of_sort_int (sortLv.trans innerSort)
    rw [compiled] at evaluated
    obtain rfl := Except.ok.inj (evaluated.symm.trans (unary_neg_int ran))
    have lookup : env.factory.factory["Int.Neg"]? =
        some (Lambda.intNegFunc (T := Core.CoreLParams)).func := by
      rw [related.1.factory_eq]
      exact ambient (Lambda.intNegFunc (T := Core.CoreLParams)).func coreFactory_intNeg
    obtain rfl := Option.some.inj encoded
    exact ⟨valueSort.symm, _, rfl, eval_intNeg lookup core⟩

private theorem bool_bin_step (op : BoolBin) (a b : Bool) :
    binaryValue op.bop ⟨.bool, a⟩ ⟨.bool, b⟩ = .ok (.bool (op.combine a b)) := by
  cases op <;> simp [BoolBin.bop, BoolBin.combine, binaryValue_bool]

private theorem local_total
    {context : ReadContext} {scope : Scope} {range : SourceRange} {index : Nat}
    {value : TypedExpr} {state : State}
    (distinct : (scope.locals.map Binding.name).Nodup)
    (built : expr (.bvar range index) context scope = .ok (value, scope))
    (fits : StateFits scope state) :
    ∃ result, result.sort = value.sort ∧ value.eval state = .ok result := by
  cases found : scope.locals.reverse[index]? with
  | none =>
    rw [expr.eq_def] at built
    simp [found, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
      reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, pure, Except.pure] at built
  | some binding =>
    by_cases unavailable : binding.name ∈ context.requiresOutputs.getD []
    · rw [expr.eq_def] at built
      simp [found, read, unavailable, reject, throw, throwThe, MonadExceptOf.throw,
        bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
        pure, StateT.lift, Except.pure] at built
    · have localOld : Expression.old (model := .builtins)
          (Expression.read (.local binding.name)) =
          Expression.read (.local binding.name) := rfl
      rw [expr.eq_def] at built
      simp [found, read, unavailable, localOld, bind, StateT.bind, Except.bind,
        get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure] at built
      obtain ⟨rfl, _⟩ := built
      have present := List.mem_reverse.mp (List.mem_of_getElem? found)
      obtain ⟨result, lookup, sort⟩ :=
        fits.lookup_local (find_local_by_name distinct present)
      exact ⟨result, sort, by simp [Expression.read, State.lookup, lookup]⟩

private theorem store_lookup_append (left right : Store) (name : String) :
    (left ++ right).lookup name =
      match left.lookup name with
      | some value => some value
      | none => right.lookup name := by
  simp only [Store.lookup]
  induction left with
  | nil => simp [List.findSome?]
  | cons head tail ih =>
    cases head with
    | mk key stored =>
      simp only [List.cons_append, List.findSome?, ih]
      split <;> rfl

private theorem global_total
    {context : ReadContext} {scope : Scope} {range : SourceRange} {index : Nat}
    {value : TypedExpr} {state : State}
    (distinct : (scope.globals.map Binding.name).Nodup)
    (built : expr (.fvar range index) context scope = .ok (value, scope))
    (fits : StateFits scope state) :
    ∃ result, result.sort = value.sort ∧ value.eval state = .ok result := by
  cases resolved : scope.names.nameOf? index with
  | none =>
    rw [expr.eq_def] at built
    simp [resolved, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
      reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, pure, Except.pure] at built
  | some name =>
    cases found : findBinding name scope.globals with
    | none =>
      rw [expr.eq_def] at built
      simp [resolved, found, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
        StateT.get, reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, pure,
        Except.pure] at built
    | some binding =>
      rw [expr.eq_def] at built
      have sameName := beq_iff_eq.mp
        (List.find?_some (p := fun item : Binding => item.name == name) found)
      have present := List.mem_of_find?_eq_some found
      have declared := find_local_by_name distinct present
      by_cases oldMode : context.old
      · simp [resolved, found, read, oldMode, bind, StateT.bind, Except.bind, get, getThe,
          MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure] at built
        split at built
        · simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, StateT.bind,
            Except.bind, Functor.map, Except.map] at built
        · simp [pure, StateT.pure, Except.pure] at built
          obtain ⟨rfl, _⟩ := built
          cases snap : state.snapshots.lookup name with
          | some saved =>
            have typed := fits.snapshots name
            rw [snap] at typed
            cases foundAt : scope.globals.find?
                (fun item => decide (item.name ∈ scope.modifies) && decide (item.name = name)) with
            | none => simp [foundAt] at typed
            | some item =>
              have itemSort : saved.sort = item.sort := by simpa [foundAt] using typed
              have selected := List.find?_some foundAt
              simp only [Bool.and_eq_true, decide_eq_true_eq] at selected
              have itemIsBinding : item = binding := by
                have foundItem := find_local_by_name distinct (List.mem_of_find?_eq_some foundAt)
                rw [selected.2] at foundItem
                exact Option.some.inj (foundItem.symm.trans found)
              exact ⟨saved, itemIsBinding ▸ itemSort, by simp [Expression.old, Expression.read,
                State.lookup, store_lookup_append, snap]⟩
          | none =>
            obtain ⟨result, lookup, sort⟩ := fits.lookup_global declared
            rw [sameName] at lookup
            exact ⟨result, sort, by simp [Expression.old, Expression.read, State.lookup,
              store_lookup_append, snap, lookup]⟩
      · simp [resolved, found, read, oldMode, bind, StateT.bind, Except.bind, get, getThe,
          MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure] at built
        obtain ⟨rfl, _⟩ := built
        obtain ⟨result, lookup, sort⟩ := fits.lookup_global declared
        rw [sameName] at lookup
        exact ⟨result, sort, by simp [Expression.read, State.lookup, lookup]⟩

private theorem finish_binary
    {op : BinaryOp} {lhs rhs value : TypedExpr} {state : State} {a b result : Value}
    (compiled : value.eval = binary op lhs.eval rhs.eval)
    (left : lhs.eval state = .ok a) (right : rhs.eval state = .ok b)
    (step : binaryValue op a b = .ok result) (sort : result.sort = value.sort) :
    ∃ r, r.sort = value.sort ∧ value.eval state = .ok r := by
  refine ⟨result, sort, ?_⟩
  rw [compiled]
  simp [binary, left, right, bind, Except.bind, step]

private theorem int_family_total (op : IntBin)
    {range tr : SourceRange} {left right : Boole.Expr} {context : ReadContext}
    {scope : Scope} {value : TypedExpr} {state : State}
    (built : expr (op.atInt range tr left right) context scope = .ok (value, scope))
    (leftTotal : ∀ {value : TypedExpr}, expr left context scope = .ok (value, scope) →
      ∃ result, result.sort = value.sort ∧ value.eval state = .ok result)
    (rightTotal : ∀ {value : TypedExpr}, expr right context scope = .ok (value, scope) →
      ∃ result, result.sort = value.sort ∧ value.eval state = .ok result) :
    ∃ result, result.sort = value.sort ∧ value.eval state = .ok result := by
  obtain ⟨lhs, rhs, leftBuilt, rightBuilt, leftSort, rightSort, valueSort, compiled⟩ :=
    compiled_int_bin op built
  obtain ⟨a, aSort, aEval⟩ := leftTotal leftBuilt
  obtain ⟨b, bSort, bEval⟩ := rightTotal rightBuilt
  obtain ⟨n, rfl⟩ := value_of_sort_int (aSort.trans leftSort)
  obtain ⟨m, rfl⟩ := value_of_sort_int (bSort.trans rightSort)
  exact finish_binary compiled aEval bEval (op.binaryValue_eq n m)
    ((op.combine_sort n m).trans valueSort.symm)

private theorem bool_family_total (op : BoolBin)
    {range : SourceRange} {left right : Boole.Expr} {context : ReadContext}
    {scope : Scope} {value : TypedExpr} {state : State}
    (built : expr (op.expr range left right) context scope = .ok (value, scope))
    (leftTotal : ∀ {value : TypedExpr}, expr left context scope = .ok (value, scope) →
      ∃ result, result.sort = value.sort ∧ value.eval state = .ok result)
    (rightTotal : ∀ {value : TypedExpr}, expr right context scope = .ok (value, scope) →
      ∃ result, result.sort = value.sort ∧ value.eval state = .ok result) :
    ∃ result, result.sort = value.sort ∧ value.eval state = .ok result := by
  obtain ⟨lhs, rhs, leftBuilt, rightBuilt, leftSort, rightSort, valueSort, compiled⟩ :=
    compiled_bool_bin op built
  obtain ⟨a, aSort, aEval⟩ := leftTotal leftBuilt
  obtain ⟨b, bSort, bEval⟩ := rightTotal rightBuilt
  obtain ⟨p, rfl⟩ := value_of_sort_bool (aSort.trans leftSort)
  obtain ⟨q, rfl⟩ := value_of_sort_bool (bSort.trans rightSort)
  exact finish_binary compiled aEval bEval (bool_bin_step op p q) valueSort.symm

private theorem int_eq_total
    {range tr : SourceRange} {left right : Boole.Expr} {context : ReadContext}
    {scope : Scope} {value : TypedExpr} {state : State}
    (built : expr (.equal range (.int tr) left right) context scope = .ok (value, scope))
    (leftTotal : ∀ {value : TypedExpr}, expr left context scope = .ok (value, scope) →
      ∃ result, result.sort = value.sort ∧ value.eval state = .ok result)
    (rightTotal : ∀ {value : TypedExpr}, expr right context scope = .ok (value, scope) →
      ∃ result, result.sort = value.sort ∧ value.eval state = .ok result) :
    ∃ result, result.sort = value.sort ∧ value.eval state = .ok result := by
  obtain ⟨lhs, rhs, leftBuilt, rightBuilt, leftSort, rightSort, valueSort, compiled⟩ :=
    compiled_int_eq built
  obtain ⟨a, aSort, aEval⟩ := leftTotal leftBuilt
  obtain ⟨b, bSort, bEval⟩ := rightTotal rightBuilt
  obtain ⟨n, rfl⟩ := value_of_sort_int (aSort.trans leftSort)
  obtain ⟨m, rfl⟩ := value_of_sort_int (bSort.trans rightSort)
  exact finish_binary compiled aEval bEval (binaryValue_int .eq n m) valueSort.symm

private theorem bool_eq_total
    {range tr : SourceRange} {left right : Boole.Expr} {context : ReadContext}
    {scope : Scope} {value : TypedExpr} {state : State}
    (built : expr (.equal range (.bool tr) left right) context scope = .ok (value, scope))
    (leftTotal : ∀ {value : TypedExpr}, expr left context scope = .ok (value, scope) →
      ∃ result, result.sort = value.sort ∧ value.eval state = .ok result)
    (rightTotal : ∀ {value : TypedExpr}, expr right context scope = .ok (value, scope) →
      ∃ result, result.sort = value.sort ∧ value.eval state = .ok result) :
    ∃ result, result.sort = value.sort ∧ value.eval state = .ok result := by
  obtain ⟨lhs, rhs, leftBuilt, rightBuilt, leftSort, rightSort, valueSort, compiled⟩ :=
    compiled_bool_eq built
  obtain ⟨a, aSort, aEval⟩ := leftTotal leftBuilt
  obtain ⟨b, bSort, bEval⟩ := rightTotal rightBuilt
  obtain ⟨p, rfl⟩ := value_of_sort_bool (aSort.trans leftSort)
  obtain ⟨q, rfl⟩ := value_of_sort_bool (bSort.trans rightSort)
  exact finish_binary compiled aEval bEval (binaryValue_bool .eq p q) valueSort.symm

private theorem int_ne_total
    {range tr : SourceRange} {left right : Boole.Expr} {context : ReadContext}
    {scope : Scope} {value : TypedExpr} {state : State}
    (built : expr (.not_equal range (.int tr) left right) context scope = .ok (value, scope))
    (leftTotal : ∀ {value : TypedExpr}, expr left context scope = .ok (value, scope) →
      ∃ result, result.sort = value.sort ∧ value.eval state = .ok result)
    (rightTotal : ∀ {value : TypedExpr}, expr right context scope = .ok (value, scope) →
      ∃ result, result.sort = value.sort ∧ value.eval state = .ok result) :
    ∃ result, result.sort = value.sort ∧ value.eval state = .ok result := by
  obtain ⟨lhs, rhs, leftBuilt, rightBuilt, leftSort, rightSort, valueSort, compiled⟩ :=
    compiled_int_ne built
  obtain ⟨a, aSort, aEval⟩ := leftTotal leftBuilt
  obtain ⟨b, bSort, bEval⟩ := rightTotal rightBuilt
  obtain ⟨n, rfl⟩ := value_of_sort_int (aSort.trans leftSort)
  obtain ⟨m, rfl⟩ := value_of_sort_int (bSort.trans rightSort)
  exact finish_binary compiled aEval bEval (binaryValue_int .ne n m) valueSort.symm

private theorem bool_ne_total
    {range tr : SourceRange} {left right : Boole.Expr} {context : ReadContext}
    {scope : Scope} {value : TypedExpr} {state : State}
    (built : expr (.not_equal range (.bool tr) left right) context scope = .ok (value, scope))
    (leftTotal : ∀ {value : TypedExpr}, expr left context scope = .ok (value, scope) →
      ∃ result, result.sort = value.sort ∧ value.eval state = .ok result)
    (rightTotal : ∀ {value : TypedExpr}, expr right context scope = .ok (value, scope) →
      ∃ result, result.sort = value.sort ∧ value.eval state = .ok result) :
    ∃ result, result.sort = value.sort ∧ value.eval state = .ok result := by
  obtain ⟨lhs, rhs, leftBuilt, rightBuilt, leftSort, rightSort, valueSort, compiled⟩ :=
    compiled_bool_ne built
  obtain ⟨a, aSort, aEval⟩ := leftTotal leftBuilt
  obtain ⟨b, bSort, bEval⟩ := rightTotal rightBuilt
  obtain ⟨p, rfl⟩ := value_of_sort_bool (aSort.trans leftSort)
  obtain ⟨q, rfl⟩ := value_of_sort_bool (bSort.trans rightSort)
  exact finish_binary compiled aEval bEval (binaryValue_bool .ne p q) valueSort.symm

private theorem compiled_old
    {range tr : SourceRange} {operand : Boole.Expr} {ty : Boole.Type} {context : ReadContext}
    {scope : Scope} {value : TypedExpr}
    (ground : ty = .int tr ∨ ty = .bool tr)
    (built : expr (.old range ty operand) context scope = .ok (value, scope)) :
    ∃ inner sort, expr operand { context with old := true } scope = .ok (inner, scope) ∧
      inner.sort = sort ∧ value.sort = sort ∧ value.eval = inner.eval := by
  rw [expr.eq_def] at built
  obtain ⟨sort, next, sorted, rest⟩ := split_run built
  obtain ⟨nextEq, isInt, isBool⟩ := sourceSort_literal sorted ground
  cases nextEq
  cases ground
  · next h =>
    cases h
    have sortEq : sort = .int := isInt rfl
    cases sortEq
    change ((expr operand { context with old := true } >>= fun inner =>
      inner.expect .int range >>= fun ev => pure ⟨.int, ev⟩) scope) = .ok (value, scope) at rest
    obtain ⟨inner, mid, ran, rest⟩ := split_run rest
    cases expr_readOnly _ _ _ _ _ ran
    obtain ⟨ev, _, expected, done⟩ := split_run rest
    unfold TypedExpr.expect at expected
    split at expected
    · rename_i same
      cases congrArg Prod.fst (Except.ok.inj expected)
      cases congrArg Prod.snd (Except.ok.inj expected)
      cases congrArg Prod.fst (Except.ok.inj done)
      cases congrArg Prod.snd (Except.ok.inj done)
      exact ⟨inner, .int, ran, beq_iff_eq.mp same, rfl, rfl⟩
    · contradiction
  · next h =>
    cases h
    have sortEq : sort = .bool := isBool rfl
    cases sortEq
    change ((expr operand { context with old := true } >>= fun inner =>
      inner.expect .bool range >>= fun ev => pure ⟨.bool, ev⟩) scope) = .ok (value, scope) at rest
    obtain ⟨inner, mid, ran, rest⟩ := split_run rest
    cases expr_readOnly _ _ _ _ _ ran
    obtain ⟨ev, _, expected, done⟩ := split_run rest
    unfold TypedExpr.expect at expected
    split at expected
    · rename_i same
      cases congrArg Prod.fst (Except.ok.inj expected)
      cases congrArg Prod.snd (Except.ok.inj expected)
      cases congrArg Prod.fst (Except.ok.inj done)
      cases congrArg Prod.snd (Except.ok.inj done)
      exact ⟨inner, .bool, ran, beq_iff_eq.mp same, rfl, rfl⟩
    · contradiction

private theorem compiled_conditional
    {range tr : SourceRange} {ty : Boole.Type} {guard yes no : Boole.Expr}
    {context : ReadContext} {scope : Scope} {value : TypedExpr}
    (ground : ty = .int tr ∨ ty = .bool tr)
    (built : expr (.if range ty guard yes no) context scope = .ok (value, scope)) :
    ∃ g y n sort, expr guard context scope = .ok (g, scope) ∧
      expr yes context scope = .ok (y, scope) ∧ expr no context scope = .ok (n, scope) ∧
      g.sort = .bool ∧ y.sort = sort ∧ n.sort = sort ∧ value.sort = sort ∧
      value.eval = Expression.conditional g.eval y.eval n.eval ∧
      (sort = .int ∨ sort = .bool) := by
  rw [expr.eq_def] at built
  obtain ⟨sort, next, sorted, rest⟩ := split_run built
  obtain ⟨nextEq, isInt, isBool⟩ := sourceSort_literal sorted ground
  cases nextEq
  cases ground
  · next h =>
    cases h
    have sortEq : sort = .int := isInt rfl
    cases sortEq
    change ((expr guard context >>= fun g => g.expect .bool range >>= fun gv =>
      expr yes context >>= fun y => y.expect .int range >>= fun yv =>
      expr no context >>= fun n => n.expect .int range >>= fun nv =>
      pure ⟨.int, Expression.conditional gv yv nv⟩) scope) = .ok (value, scope) at rest
    obtain ⟨g, _, gRun, rest⟩ := split_run rest
    cases expr_readOnly _ _ _ _ _ gRun
    obtain ⟨gv, _, gExpect, rest⟩ := split_run rest
    unfold TypedExpr.expect at gExpect
    split at gExpect
    · rename_i gSame
      cases congrArg Prod.fst (Except.ok.inj gExpect)
      cases congrArg Prod.snd (Except.ok.inj gExpect)
      obtain ⟨y, _, yRun, rest⟩ := split_run rest
      cases expr_readOnly _ _ _ _ _ yRun
      obtain ⟨yv, _, yExpect, rest⟩ := split_run rest
      unfold TypedExpr.expect at yExpect
      split at yExpect
      · rename_i ySame
        cases congrArg Prod.fst (Except.ok.inj yExpect)
        cases congrArg Prod.snd (Except.ok.inj yExpect)
        obtain ⟨n, _, nRun, rest⟩ := split_run rest
        cases expr_readOnly _ _ _ _ _ nRun
        obtain ⟨nv, _, nExpect, done⟩ := split_run rest
        unfold TypedExpr.expect at nExpect
        split at nExpect
        · rename_i nSame
          cases congrArg Prod.fst (Except.ok.inj nExpect)
          cases congrArg Prod.snd (Except.ok.inj nExpect)
          cases congrArg Prod.fst (Except.ok.inj done)
          cases congrArg Prod.snd (Except.ok.inj done)
          exact ⟨g, y, n, .int, gRun, yRun, nRun, beq_iff_eq.mp gSame,
            beq_iff_eq.mp ySame, beq_iff_eq.mp nSame, rfl, rfl, Or.inl rfl⟩
        · contradiction
      · contradiction
    · contradiction
  · next h =>
    cases h
    have sortEq : sort = .bool := isBool rfl
    cases sortEq
    change ((expr guard context >>= fun g => g.expect .bool range >>= fun gv =>
      expr yes context >>= fun y => y.expect .bool range >>= fun yv =>
      expr no context >>= fun n => n.expect .bool range >>= fun nv =>
      pure ⟨.bool, Expression.conditional gv yv nv⟩) scope) = .ok (value, scope) at rest
    obtain ⟨g, _, gRun, rest⟩ := split_run rest
    cases expr_readOnly _ _ _ _ _ gRun
    obtain ⟨gv, _, gExpect, rest⟩ := split_run rest
    unfold TypedExpr.expect at gExpect
    split at gExpect
    · rename_i gSame
      cases congrArg Prod.fst (Except.ok.inj gExpect)
      cases congrArg Prod.snd (Except.ok.inj gExpect)
      obtain ⟨y, _, yRun, rest⟩ := split_run rest
      cases expr_readOnly _ _ _ _ _ yRun
      obtain ⟨yv, _, yExpect, rest⟩ := split_run rest
      unfold TypedExpr.expect at yExpect
      split at yExpect
      · rename_i ySame
        cases congrArg Prod.fst (Except.ok.inj yExpect)
        cases congrArg Prod.snd (Except.ok.inj yExpect)
        obtain ⟨n, _, nRun, rest⟩ := split_run rest
        cases expr_readOnly _ _ _ _ _ nRun
        obtain ⟨nv, _, nExpect, done⟩ := split_run rest
        unfold TypedExpr.expect at nExpect
        split at nExpect
        · rename_i nSame
          cases congrArg Prod.fst (Except.ok.inj nExpect)
          cases congrArg Prod.snd (Except.ok.inj nExpect)
          cases congrArg Prod.fst (Except.ok.inj done)
          cases congrArg Prod.snd (Except.ok.inj done)
          exact ⟨g, y, n, .bool, gRun, yRun, nRun, beq_iff_eq.mp gSame,
            beq_iff_eq.mp ySame, beq_iff_eq.mp nSame, rfl, rfl, Or.inr rfl⟩
        · contradiction
      · contradiction
    · contradiction

private theorem conditional_select
    (guard yes no : Expression) (state : State) {p : Bool} {selected : Value}
    (g : guard state = .ok (.bool p))
    (ran : (if p then yes else no) state = .ok selected) :
    Expression.conditional guard yes no state = .ok selected := by
  unfold Expression.conditional
  rw [g]
  simp only [bind, Except.bind]
  cases p
  · split
    · next heq => cases heq
    · exact ran
    · next missed => exact (missed rfl).elim
  · split
    · exact ran
    · next heq => cases heq
    · next trueFailed _ => exact (trueFailed rfl).elim

private theorem bridge_total
    {context : ReadContext} {scope : Scope} {expression : Boole.Expr} {value : TypedExpr}
    {state : State}
    (distinct : ((scope.locals ++ scope.globals).map Binding.name).Nodup)
    (bridge : BridgeTyped expression)
    (built : expr expression context scope = .ok (value, scope))
    (fits : StateFits scope state) :
    ∃ result, result.sort = value.sort ∧ value.eval state = .ok result := by
  induction bridge generalizing value context
  case natToInt _ _ | btrue _ | bfalse _ | strLit _ _ | bv1Lit _ _ | bv8Lit _ _ | bv16Lit _ _
    | bv32Lit _ _ | bv64Lit _ _ | bv128Lit _ _ =>
    rw [expr.eq_def] at built
    simp only [pure, StateT.pure, Except.pure] at built
    cases congrArg Prod.snd (Except.ok.inj built)
    cases congrArg Prod.fst (Except.ok.inj built)
    exact ⟨_, rfl, rfl⟩
  case app _ _ _ =>
    rw [expr.eq_def] at built
    simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, Functor.map, Except.map] at built
  case bvar _ index =>
    exact local_total (List.nodup_append.mp (by simpa [List.map_append] using distinct)).1 built fits
  case fvar _ _ =>
    exact global_total (List.nodup_append.mp (by simpa [List.map_append] using distinct)).2.1
      built fits
  case not _ _ ih =>
    obtain ⟨inner, innerBuilt, innerSort, valueSort, compiled⟩ := compiled_not built
    obtain ⟨result, resultSort, ran⟩ := ih innerBuilt
    obtain ⟨b, rfl⟩ := value_of_sort_bool (resultSort.trans innerSort)
    exact ⟨.bool (!b), valueSort.symm, by rw [compiled]; exact unary_not_bool ran⟩
  case add _ _ _ _ iha ihb =>
    rename_i n1 n2 n3 n4 n5 n6 n7
    cases n2 <;> try simp [bridgeType] at *
    · exact False.elim (int_bin_rejects_bool .add built)
    · exact int_family_total .add built (fun h => iha h) (fun h => ihb h)
  case sub _ _ _ _ iha ihb =>
    rename_i n1 n2 n3 n4 n5 n6 n7
    cases n2 <;> try simp [bridgeType] at *
    · exact False.elim (int_bin_rejects_bool .sub built)
    · exact int_family_total .sub built (fun h => iha h) (fun h => ihb h)
  case mul _ _ _ _ iha ihb =>
    rename_i n1 n2 n3 n4 n5 n6 n7
    cases n2 <;> try simp [bridgeType] at *
    · exact False.elim (int_bin_rejects_bool .mul built)
    · exact int_family_total .mul built (fun h => iha h) (fun h => ihb h)
  case le _ _ _ _ iha ihb =>
    rename_i n1 n2 n3 n4 n5 n6 n7
    cases n2 <;> try simp [bridgeType] at *
    · exact False.elim (int_bin_rejects_bool .le built)
    · exact int_family_total .le built (fun h => iha h) (fun h => ihb h)
  case lt _ _ _ _ iha ihb =>
    rename_i n1 n2 n3 n4 n5 n6 n7
    cases n2 <;> try simp [bridgeType] at *
    · exact False.elim (int_bin_rejects_bool .lt built)
    · exact int_family_total .lt built (fun h => iha h) (fun h => ihb h)
  case ge _ _ _ _ iha ihb =>
    rename_i n1 n2 n3 n4 n5 n6 n7
    cases n2 <;> try simp [bridgeType] at *
    · exact False.elim (int_bin_rejects_bool .ge built)
    · exact int_family_total .ge built (fun h => iha h) (fun h => ihb h)
  case gt _ _ _ _ iha ihb =>
    rename_i n1 n2 n3 n4 n5 n6 n7
    cases n2 <;> try simp [bridgeType] at *
    · exact False.elim (int_bin_rejects_bool .gt built)
    · exact int_family_total .gt built (fun h => iha h) (fun h => ihb h)
  case and _ _ _ iha ihb => exact bool_family_total .and built (fun h => iha h) (fun h => ihb h)
  case or _ _ _ iha ihb => exact bool_family_total .or built (fun h => iha h) (fun h => ihb h)
  case implies _ _ _ iha ihb =>
    exact bool_family_total .implies built (fun h => iha h) (fun h => ihb h)
  case equiv _ _ _ iha ihb =>
    exact bool_family_total .equiv built (fun h => iha h) (fun h => ihb h)
  case equal _ _ _ _ iha ihb =>
    rename_i n1 n2 n3 n4 n5 n6 n7
    cases n2 <;> try simp [bridgeType] at *
    · exact bool_eq_total built (fun h => iha h) (fun h => ihb h)
    · exact int_eq_total built (fun h => iha h) (fun h => ihb h)
  case notEqual _ _ _ _ iha ihb =>
    rename_i n1 n2 n3 n4 n5 n6 n7
    cases n2 <;> try simp [bridgeType] at *
    · exact bool_ne_total built (fun h => iha h) (fun h => ihb h)
    · exact int_ne_total built (fun h => iha h) (fun h => ihb h)
  case neg _ _ _ ih =>
    rename_i n1 n2 n3 n4 n5
    cases n2 <;> try simp [bridgeType] at *
    · exact False.elim (neg_rejects_bool built)
    · obtain ⟨inner, innerBuilt, innerSort, valueSort, compiled⟩ := compiled_int_neg built
      obtain ⟨result, resultSort, ran⟩ := ih innerBuilt
      obtain ⟨n, rfl⟩ := value_of_sort_int (resultSort.trans innerSort)
      exact ⟨.int (-n), valueSort.symm, by rw [compiled]; exact unary_neg_int ran⟩
  case old _ _ _ ih =>
    rename_i n1 n2 n3 n4 n5
    cases n2 <;> try simp [bridgeType] at *
    · obtain ⟨inner, _, innerBuilt, innerSort, valueSort, compiled⟩ :=
        compiled_old (.inr rfl) built
      obtain ⟨result, resultSort, ran⟩ := ih innerBuilt
      exact ⟨result, resultSort.trans (innerSort.trans valueSort.symm), by rw [compiled]; exact ran⟩
    · obtain ⟨inner, _, innerBuilt, innerSort, valueSort, compiled⟩ :=
        compiled_old (.inl rfl) built
      obtain ⟨result, resultSort, ran⟩ := ih innerBuilt
      exact ⟨result, resultSort.trans (innerSort.trans valueSort.symm), by rw [compiled]; exact ran⟩
  case ite _ _ _ _ _ ihg ihy ihn =>
    rename_i n1 n2 n3 n4 n5 n6 n7 n8 n9
    cases n2 <;> try simp [bridgeType] at *
    · obtain ⟨g, y, n, _, gRun, yRun, nRun, gSort, ySort, nSort, valueSort, compiled, _⟩ :=
        compiled_conditional (.inr rfl) built
      obtain ⟨gv, gvSort, gEval⟩ := ihg gRun
      obtain ⟨p, rfl⟩ := value_of_sort_bool (gvSort.trans gSort)
      obtain ⟨yv, yvSort, yEval⟩ := ihy yRun
      obtain ⟨nv, nvSort, nEval⟩ := ihn nRun
      cases p
      · exact ⟨nv, nvSort.trans (nSort.trans valueSort.symm), by
          rw [compiled]; exact conditional_select g.eval y.eval n.eval state gEval nEval⟩
      · exact ⟨yv, yvSort.trans (ySort.trans valueSort.symm), by
          rw [compiled]; exact conditional_select g.eval y.eval n.eval state gEval yEval⟩
    · obtain ⟨g, y, n, _, gRun, yRun, nRun, gSort, ySort, nSort, valueSort, compiled, _⟩ :=
        compiled_conditional (.inl rfl) built
      obtain ⟨gv, gvSort, gEval⟩ := ihg gRun
      obtain ⟨p, rfl⟩ := value_of_sort_bool (gvSort.trans gSort)
      obtain ⟨yv, yvSort, yEval⟩ := ihy yRun
      obtain ⟨nv, nvSort, nEval⟩ := ihn nRun
      cases p
      · exact ⟨nv, nvSort.trans (nSort.trans valueSort.symm), by
          rw [compiled]; exact conditional_select g.eval y.eval n.eval state gEval nEval⟩
      · exact ⟨yv, yvSort.trans (ySort.trans valueSort.symm), by
          rw [compiled]; exact conditional_select g.eval y.eval n.eval state gEval yEval⟩

private theorem lower_ite
    {range : SourceRange} {bTy : Boole.Type} {guard yes no : Boole.Expr}
    {entry : TranslateState} {raw : Core.Expression.Expr} {final : TranslateState}
    (lowered : toCoreExpr (.if range bTy guard yes no) entry = .ok (raw, final)) :
    ∃ mid1 mid2 guardRaw yesRaw noRaw, toCoreExpr guard entry = .ok (guardRaw, mid1) ∧
      toCoreExpr yes mid1 = .ok (yesRaw, mid2) ∧
      toCoreExpr no mid2 = .ok (noRaw, final) ∧
      raw = .ite () guardRaw yesRaw noRaw := by
  rw [toCoreExpr.eq_def] at lowered
  simp only [toCoreQuantExpr?, bind, StateT.bind, Except.bind] at lowered
  cases guardRun : toCoreExpr guard entry with
  | error e => simp [guardRun] at lowered
  | ok p =>
    obtain ⟨guardRaw', mid1⟩ := p
    simp only [guardRun] at lowered
    cases yesRun : toCoreExpr yes mid1 with
    | error e => simp [yesRun] at lowered
    | ok q =>
      obtain ⟨yesRaw', mid2⟩ := q
      simp only [yesRun] at lowered
      cases noRun : toCoreExpr no mid2 with
      | error e => simp [noRun] at lowered
      | ok r =>
        obtain ⟨noRaw', _⟩ := r
        simp only [noRun, pure, StateT.pure, Except.pure] at lowered
        have pairEq := Except.ok.inj lowered
        cases congrArg Prod.snd pairEq
        exact ⟨mid1, mid2, guardRaw', yesRaw', noRaw', rfl, yesRun, noRun,
          (congrArg Prod.fst pairEq).symm⟩

private theorem erase_ite_inv {annotated guard yes no : Core.Expression.Expr}
    (erased : annotated.eraseTypes =
      (.ite () guard yes no : Core.Expression.Expr).eraseTypes) :
    ∃ a b c, annotated = .ite () a b c ∧ a.eraseTypes = guard.eraseTypes ∧
      b.eraseTypes = yes.eraseTypes ∧ c.eraseTypes = no.eraseTypes := by
  cases annotated <;> simp [Lambda.LExpr.eraseTypes] at erased
  case ite metadata a b c =>
    cases metadata
    exact ⟨a, b, c, rfl, erased⟩

private theorem typed_ite_operands
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    {guard yes no : Core.Expression.Expr} {ty : Lambda.LMonoTy}
    (typed : ExprWellTyped context scopes (.ite () guard yes no) ty) :
    ExprWellTyped context scopes guard .bool ∧ ExprWellTyped context scopes yes ty ∧
      ExprWellTyped context scopes no ty := by
  cases typed.1 with
  | ite guardTyped yesTyped noTyped =>
    refine ⟨⟨guardTyped, ?_, ?_⟩, ⟨yesTyped, ?_, ?_⟩, ⟨noTyped, ?_, ?_⟩⟩
    all_goals first
      | (intro ann present; apply typed.2.1; simp [Lambda.LExpr.binderAnnotations, present])
      | (constructor
         · intro ident ann present
           apply typed.2.2.fvarsDeclared
           simp [Lambda.LExpr.freeVars, present]
         · intro op ann present
           apply typed.2.2.opsInstantiate
           simp [Lambda.LExpr.opAnnots, present]
         · intro op present
           apply typed.2.2.opsKnown
           simp [Lambda.LExpr.getOps, present])

private theorem finish_ite
    {factory : Core.Expression.Factory} {store : Core.CoreStore}
    {guard yes no : Expression} {state : State}
    {guardExpr yesExpr noExpr : Core.Expression.Expr}
    {value : TypedExpr} {p : Bool} {yesValue noValue : Value}
    {yesCore noCore : Core.Expression.Val} {result : Value}
    (guardRan : guard state = .ok (.bool p))
    (yesRan : yes state = .ok yesValue)
    (noRan : no state = .ok noValue)
    (yesEncoded : coreValueIn? factory.model.tcInterp yesValue = some yesCore)
    (noEncoded : coreValueIn? factory.model.tcInterp noValue = some noCore)
    (guardCore : Core.Expression.eval factory store guardExpr =
      some (Lambda.SemValue.ofBool factory.model.tcInterp p))
    (yesEval : Core.Expression.eval factory store yesExpr = some yesCore)
    (noEval : Core.Expression.eval factory store noExpr = some noCore)
    (sameSort : yesCore.sort = noCore.sort)
    (compiled : value.eval = Expression.conditional guard yes no)
    (evaluated : value.eval state = .ok result)
    (yesSort : yesValue.sort = value.sort)
    (noSort : noValue.sort = value.sort) :
    result.sort = value.sort ∧
      ∃ v, coreValueIn? factory.model.tcInterp result = some v ∧
        Core.Expression.eval factory store (.ite () guardExpr yesExpr noExpr) = some v := by
  rw [compiled] at evaluated
  cases p
  · have selected := conditional_select guard yes no state guardRan noRan
    cases Except.ok.inj (evaluated.symm.trans selected)
    exact ⟨noSort, noCore, noEncoded, by
      simpa using Core.eval_ite factory guardCore yesEval noEval sameSort⟩
  · have selected := conditional_select guard yes no state guardRan yesRan
    cases Except.ok.inj (evaluated.symm.trans selected)
    exact ⟨yesSort, yesCore, yesEncoded, by
      simpa using Core.eval_ite factory guardCore yesEval noEval sameSort⟩

private theorem ite_agrees
    {entry : CompilerScopes} {after : TranslateState}
    {factory : Lambda.Factory Core.CoreLParams} {unwritten : List Core.CoreIdent}
    {context : ReadContext} {range tr : SourceRange} {bTy : Boole.Type}
    {guard yes no : Boole.Expr} {value : TypedExpr} {raw target : Core.Expression.Expr}
    {mono : Lambda.LMonoTy}
    (aligned : ScopesAgree entry)
    (ground : bTy = .int tr ∨ bTy = .bool tr)
    (guardBridge : BridgeTyped guard) (yesBridge : BridgeTyped yes) (noBridge : BridgeTyped no)
    (built : expr (.if range bTy guard yes no) context entry.source = .ok (value, entry.source))
    (lowered : toCoreExpr (.if range bTy guard yes no) entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (typed : ExprWellTyped entry.context entry.variables target mono)
    (readable : ready unwritten target = true)
    (guardIH : SubAgrees entry context factory unwritten guard)
    (yesIH : SubAgrees entry context factory unwritten yes)
    (noIH : SubAgrees entry context factory unwritten no) :
    after = entry.lowering ∧ Agrees entry.source factory unwritten value target := by
  obtain ⟨guardValue, yesValue, noValue, _, guardBuilt, yesBuilt, noBuilt, guardSort, yesSort,
      noSort, valueSort, compiled, which⟩ := compiled_conditional ground built
  obtain ⟨_, _, guardRaw, yesRaw, noRaw, guardLowered, yesLowered, noLowered, rfl⟩ :=
    lower_ite lowered
  obtain ⟨guardTarget, yesTarget, noTarget, rfl, guardErased, yesErased, noErased⟩ :=
    erase_ite_inv erased
  obtain ⟨guardTyped, yesTyped, noTyped⟩ := typed_ite_operands typed
  have reads : ready unwritten guardTarget = true ∧ ready unwritten yesTarget = true ∧
      ready unwritten noTarget = true := by
    simp [ready, Core.CmdType.freeVars, Lambda.LExpr.freeVars, List.all_append] at readable ⊢
    exact ⟨readable.1, readable.2.1, readable.2.2⟩
  obtain ⟨rfl, guardAgrees⟩ :=
    guardIH guardBuilt guardLowered guardErased guardTyped reads.1
  obtain ⟨rfl, yesAgrees⟩ := yesIH yesBuilt yesLowered yesErased yesTyped reads.2.1
  obtain ⟨rfl, noAgrees⟩ := noIH noBuilt noLowered noErased noTyped reads.2.2
  refine ⟨rfl, ?_⟩
  intro state env result related evaluated
  obtain ⟨guardResult, guardResultSort, guardRan⟩ :=
    bridge_total aligned.distinct guardBridge guardBuilt related.2
  obtain ⟨p, rfl⟩ := value_of_sort_bool (guardResultSort.trans guardSort)
  obtain ⟨_, _, guardEncoded, guardCore⟩ :=
    guardAgrees state env (.bool p) related guardRan
  obtain rfl := Option.some.inj guardEncoded
  obtain ⟨yesResult, _, yesRan⟩ := bridge_total aligned.distinct yesBridge yesBuilt related.2
  obtain ⟨yesSound, _, yesEncoded, yesCore⟩ := yesAgrees state env yesResult related yesRan
  obtain ⟨noResult, _, noRan⟩ := bridge_total aligned.distinct noBridge noBuilt related.2
  obtain ⟨noSound, _, noEncoded, noCore⟩ := noAgrees state env noResult related noRan
  cases which
  · next sortInt =>
    cases sortInt
    obtain ⟨_, rfl⟩ := value_of_sort_int (yesSound.trans yesSort)
    obtain ⟨_, rfl⟩ := value_of_sort_int (noSound.trans noSort)
    obtain rfl := Option.some.inj yesEncoded
    obtain rfl := Option.some.inj noEncoded
    exact finish_ite guardRan yesRan noRan rfl rfl guardCore yesCore noCore rfl compiled
      evaluated (yesSound.trans (yesSort.trans valueSort.symm))
      (noSound.trans (noSort.trans valueSort.symm))
  · next sortBool =>
    cases sortBool
    obtain ⟨_, rfl⟩ := value_of_sort_bool (yesSound.trans yesSort)
    obtain ⟨_, rfl⟩ := value_of_sort_bool (noSound.trans noSort)
    obtain rfl := Option.some.inj yesEncoded
    obtain rfl := Option.some.inj noEncoded
    exact finish_ite guardRan yesRan noRan rfl rfl guardCore yesCore noCore rfl compiled
      evaluated (yesSound.trans (yesSort.trans valueSort.symm))
      (noSound.trans (noSort.trans valueSort.symm))

private theorem expr_agrees
    {entry : CompilerScopes} {after : TranslateState}
    {factory : Lambda.Factory Core.CoreLParams} {unwritten : List Core.CoreIdent}
    {context : ReadContext}
    {expression : Boole.Expr} {value : TypedExpr} {raw target : Core.Expression.Expr}
    {ty : Lambda.LMonoTy}
    (bridge : BridgeTyped expression)
    (aligned : ScopesAgree entry)
    (ambient : ∀ fn : Lambda.LFunc Core.CoreLParams,
      Core.Factory[fn.name.name]? = some fn → factory[fn.name.name]? = some fn)
    (current : context.old = false)
    (built : expr expression context entry.source = .ok (value, entry.source))
    (lowered : toCoreExpr expression entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (typed : ExprWellTyped entry.context entry.variables target ty)
    (readable : ready unwritten target = true) :
    after = entry.lowering ∧ Agrees entry.source factory unwritten value target := by
  induction bridge generalizing after value raw target ty
  case natToInt r n =>
    rw [expr.eq_def] at built
    rw [toCoreExpr.eq_def] at lowered
    simp only [toCoreQuantExpr?, pure, StateT.pure, Except.pure] at built lowered
    have stable : after = entry.lowering := (congrArg Prod.snd (Except.ok.inj lowered)).symm
    have valueEq := (congrArg Prod.fst (Except.ok.inj built)).symm
    have rawEq := (congrArg Prod.fst (Except.ok.inj lowered)).symm
    subst valueEq rawEq
    cases target <;> simp [Lambda.LExpr.eraseTypes] at erased
    obtain rfl := erased
    refine ⟨stable, const_agrees (fun _ => rfl) rfl rfl (fun _ => rfl)⟩
  case btrue r =>
    rw [expr.eq_def] at built
    rw [toCoreExpr.eq_def] at lowered
    simp only [toCoreQuantExpr?, pure, StateT.pure, Except.pure] at built lowered
    have stable : after = entry.lowering := (congrArg Prod.snd (Except.ok.inj lowered)).symm
    have valueEq := (congrArg Prod.fst (Except.ok.inj built)).symm
    have rawEq := (congrArg Prod.fst (Except.ok.inj lowered)).symm
    subst valueEq rawEq
    cases target <;> simp [Lambda.LExpr.eraseTypes] at erased
    obtain rfl := erased
    refine ⟨stable, const_agrees (fun _ => rfl) rfl rfl (fun _ => rfl)⟩
  case bfalse r =>
    rw [expr.eq_def] at built
    rw [toCoreExpr.eq_def] at lowered
    simp only [toCoreQuantExpr?, pure, StateT.pure, Except.pure] at built lowered
    have stable : after = entry.lowering := (congrArg Prod.snd (Except.ok.inj lowered)).symm
    have valueEq := (congrArg Prod.fst (Except.ok.inj built)).symm
    have rawEq := (congrArg Prod.fst (Except.ok.inj lowered)).symm
    subst valueEq rawEq
    cases target <;> simp [Lambda.LExpr.eraseTypes] at erased
    obtain rfl := erased
    refine ⟨stable, const_agrees (fun _ => rfl) rfl rfl (fun _ => rfl)⟩
  case strLit r s =>
    rw [toCoreExpr.eq_def] at lowered
    simp [toCoreQuantExpr?, throw, throwThe, MonadExceptOf.throw, StateT.lift, Functor.map,
      Except.map] at lowered
  case app r f a =>
    rw [expr.eq_def] at built
    simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, Functor.map, Except.map] at built
  case bv1Lit r n =>
    rw [expr.eq_def] at built
    rw [toCoreExpr.eq_def] at lowered
    simp only [toCoreQuantExpr?, pure, StateT.pure, Except.pure] at built lowered
    have stable : after = entry.lowering := (congrArg Prod.snd (Except.ok.inj lowered)).symm
    have valueEq := (congrArg Prod.fst (Except.ok.inj built)).symm
    have rawEq := (congrArg Prod.fst (Except.ok.inj lowered)).symm
    subst valueEq rawEq
    cases target <;> simp [Lambda.LExpr.eraseTypes] at erased
    obtain rfl := erased
    refine ⟨stable, const_agrees (fun _ => rfl) rfl rfl (fun _ => rfl)⟩
  case bv8Lit r n =>
    rw [expr.eq_def] at built
    rw [toCoreExpr.eq_def] at lowered
    simp only [toCoreQuantExpr?, pure, StateT.pure, Except.pure] at built lowered
    have stable : after = entry.lowering := (congrArg Prod.snd (Except.ok.inj lowered)).symm
    have valueEq := (congrArg Prod.fst (Except.ok.inj built)).symm
    have rawEq := (congrArg Prod.fst (Except.ok.inj lowered)).symm
    subst valueEq rawEq
    cases target <;> simp [Lambda.LExpr.eraseTypes] at erased
    obtain rfl := erased
    refine ⟨stable, const_agrees (fun _ => rfl) rfl rfl (fun _ => rfl)⟩
  case bv16Lit r n =>
    rw [expr.eq_def] at built
    rw [toCoreExpr.eq_def] at lowered
    simp only [toCoreQuantExpr?, pure, StateT.pure, Except.pure] at built lowered
    have stable : after = entry.lowering := (congrArg Prod.snd (Except.ok.inj lowered)).symm
    have valueEq := (congrArg Prod.fst (Except.ok.inj built)).symm
    have rawEq := (congrArg Prod.fst (Except.ok.inj lowered)).symm
    subst valueEq rawEq
    cases target <;> simp [Lambda.LExpr.eraseTypes] at erased
    obtain rfl := erased
    refine ⟨stable, const_agrees (fun _ => rfl) rfl rfl (fun _ => rfl)⟩
  case bv32Lit r n =>
    rw [expr.eq_def] at built
    rw [toCoreExpr.eq_def] at lowered
    simp only [toCoreQuantExpr?, pure, StateT.pure, Except.pure] at built lowered
    have stable : after = entry.lowering := (congrArg Prod.snd (Except.ok.inj lowered)).symm
    have valueEq := (congrArg Prod.fst (Except.ok.inj built)).symm
    have rawEq := (congrArg Prod.fst (Except.ok.inj lowered)).symm
    subst valueEq rawEq
    cases target <;> simp [Lambda.LExpr.eraseTypes] at erased
    obtain rfl := erased
    refine ⟨stable, const_agrees (fun _ => rfl) rfl rfl (fun _ => rfl)⟩
  case bv64Lit r n =>
    rw [expr.eq_def] at built
    rw [toCoreExpr.eq_def] at lowered
    simp only [toCoreQuantExpr?, pure, StateT.pure, Except.pure] at built lowered
    have stable : after = entry.lowering := (congrArg Prod.snd (Except.ok.inj lowered)).symm
    have valueEq := (congrArg Prod.fst (Except.ok.inj built)).symm
    have rawEq := (congrArg Prod.fst (Except.ok.inj lowered)).symm
    subst valueEq rawEq
    cases target <;> simp [Lambda.LExpr.eraseTypes] at erased
    obtain rfl := erased
    refine ⟨stable, const_agrees (fun _ => rfl) rfl rfl (fun _ => rfl)⟩
  case bv128Lit r n =>
    rw [expr.eq_def] at built
    rw [toCoreExpr.eq_def] at lowered
    simp only [toCoreQuantExpr?, pure, StateT.pure, Except.pure] at built lowered
    have stable : after = entry.lowering := (congrArg Prod.snd (Except.ok.inj lowered)).symm
    have valueEq := (congrArg Prod.fst (Except.ok.inj built)).symm
    have rawEq := (congrArg Prod.fst (Except.ok.inj lowered)).symm
    subst valueEq rawEq
    cases target <;> simp [Lambda.LExpr.eraseTypes] at erased
    obtain rfl := erased
    refine ⟨stable, const_agrees (fun _ => rfl) rfl rfl (fun _ => rfl)⟩
  case bvar r index =>
    cases found : entry.source.locals.reverse[index]? with
    | none =>
      rw [expr.eq_def] at built
      simp [found, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
        reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, pure, Except.pure] at built
    | some binding =>
      have rawShape := (lowerLocalRead (checkingInterpretation (fun _ => true)) entry.source
        entry.lowering r index binding aligned.binders found).2
      have same := ExpressionWasLowered.unique ⟨after, lowered⟩ rawShape
      have readableName : coreIdent (.local binding.name) ∉ unwritten := by
        rw [same] at erased
        cases target <;> simp [Lambda.LExpr.eraseTypes] at erased
        case fvar md id annotation =>
          cases md
          subst id
          simpa [ready, Core.CmdType.freeVars, Lambda.LExpr.freeVars, coreIdent] using readable
      have stable : after = entry.lowering := by
        have bounded : index < entry.source.locals.length := by
          simpa using (List.getElem?_eq_some_iff.mp found).1
        have atIndex : entry.lowering.bvars[entry.lowering.bvars.size - index - 1]? =
            some (.fvar () ⟨binding.name, ()⟩ none) := by
          rw [aligned.binders]
          simp only [Array.size_map, List.size_toArray, Array.getElem?_map, List.getElem?_toArray]
          have position : entry.source.locals.length - index - 1 =
              entry.source.locals.length - 1 - index := by omega
          rw [position, ← List.getElem?_reverse bounded, found]
          rfl
        have below : index < entry.lowering.bvars.size := by
          simpa [aligned.binders] using bounded
        rw [toCoreExpr.eq_def] at lowered
        simp only [toCoreQuantExpr?, getBVarExpr, bind, StateT.bind, Except.bind,
          get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure] at lowered
        simp [below, atIndex, StateT.pure] at lowered
        exact (congrArg Prod.snd (Except.ok.inj lowered)).symm
      have distinct : (entry.source.locals.map Binding.name).Nodup :=
        (List.nodup_append.mp (by simpa only [List.map_append] using aligned.distinct :
          (entry.source.locals.map Binding.name ++ entry.source.globals.map Binding.name).Nodup)).1
      have present := List.mem_reverse.mp (List.mem_of_getElem? found)
      obtain ⟨_, total, agrees⟩ := local_read_agrees (factory := factory) (unwritten := unwritten)
        aligned.binders found (find_local_by_name distinct present) readableName built
        ⟨after, lowered⟩ erased
      exact ⟨stable, Agrees.of_total total agrees⟩
  case fvar r index =>
    cases resolves : entry.source.names.nameOf? index with
    | none =>
      rw [expr.eq_def] at built
      simp [resolves, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
        reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, pure, Except.pure] at built
    | some name =>
      cases found : findBinding name entry.source.globals with
      | none =>
        rw [expr.eq_def] at built
        simp [resolves, found, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
          StateT.get, reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, pure,
          Except.pure] at built
      | some binding =>
        have sameName := beq_iff_eq.mp
          (List.find?_some (p := fun b : Binding => b.name == name) found)
        have registered : entry.lowering.globalVarTypes.contains name = true := by
          rw [← sameName]
          exact aligned.globals binding (List.mem_of_find?_eq_some found)
        have rawShape := (lowerGlobalRead (checkingInterpretation (fun _ => true))
          entry.source entry.lowering r index name binding aligned.names resolves found
          registered).2
        have same := ExpressionWasLowered.unique ⟨after, lowered⟩ rawShape
        have readableName : coreIdent (.global name) ∉ unwritten := by
          rw [same] at erased
          cases target <;> simp [Lambda.LExpr.eraseTypes] at erased
          case fvar md ident annotation =>
            cases md
            subst ident
            simpa [ready, Core.CmdType.freeVars, Lambda.LExpr.freeVars, coreIdent] using readable
        have stable : after = entry.lowering := by
          have rawName : entry.lowering.gctx.nameOf? index = some name := aligned.names ▸ resolves
          have classified : getFVarIsOp r index entry.lowering = .ok (false, entry.lowering) := by
            cases foundAt : entry.lowering.gctx.vars[index]? with
            | none => simp [GlobalContext.nameOf?, foundAt] at rawName
            | some entryAtIndex =>
              obtain ⟨key, kind⟩ := entryAtIndex
              have nameEq : key = name := by simpa [GlobalContext.nameOf?, foundAt] using rawName
              subst key
              cases kind <;> simp [getFVarIsOp, TranslateState.isGlobalVar, foundAt, registered, bind,
                StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure,
                Except.pure]
          rw [toCoreExpr.eq_def] at lowered
          simp only [toCoreQuantExpr?, getFVarName, rawName, classified, mkIdent,
            bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
            pure, StateT.pure, Except.pure] at lowered
          exact (congrArg Prod.snd (Except.ok.inj lowered)).symm
        obtain ⟨_, total, agrees⟩ := global_read_agrees (factory := factory) (unwritten := unwritten)
          current aligned.names resolves found registered readableName built ⟨after, lowered⟩ erased
        exact ⟨stable, Agrees.of_total total agrees⟩
  case not r operand ih =>
    obtain ⟨inner, innerBuilt, innerSort, valueSort, compiled⟩ := compiled_not built
    obtain ⟨innerRaw, innerLowered, rfl⟩ := lower_not lowered
    obtain ⟨argument, rfl, argErased, argTyped⟩ := typed_boolNot_origin typed
      (aligned.builtins (Lambda.boolNotFunc (T := Core.CoreLParams)).func
        Core.coreFactory_boolNot) erased
    have argReady : ready unwritten argument = true := by
      simp [ready, Core.CmdType.freeVars, Lambda.LExpr.freeVars, Core.boolNotOp,
        List.all_append] at readable ⊢
      exact readable.2
    obtain ⟨rfl, innerAgrees⟩ := ih innerBuilt innerLowered argErased argTyped argReady
    refine ⟨rfl, ?_⟩
    intro state env result related evaluated
    cases ran : inner.eval state with
    | error e =>
      rw [compiled] at evaluated
      simp [Expression.unary, ran, bind, Except.bind] at evaluated
    | ok lv =>
      obtain ⟨_, v, encoded, core⟩ := innerAgrees state env lv related ran
      have boolSort : lv.sort = .bool := (innerAgrees state env lv related ran).1.trans innerSort
      obtain ⟨b, rfl⟩ := value_of_sort_bool boolSort
      rw [compiled] at evaluated
      obtain rfl := Except.ok.inj (evaluated.symm.trans (unary_not_bool ran))
      refine ⟨valueSort.symm, _, rfl, ?_⟩
      have lookup : env.factory.factory["Bool.Not"]? =
          some (Lambda.boolNotFunc (T := Core.CoreLParams)).func := by
        rw [related.1.factory_eq]
        exact ambient (Lambda.boolNotFunc (T := Core.CoreLParams)).func Core.coreFactory_boolNot
      obtain rfl := Option.some.inj encoded
      exact eval_boolNot lookup core
  case add bTy left right proof _leftBridge _rightBridge iha ihb =>
    cases bTy
    case int tr =>
      exact int_bin_agrees .add aligned ambient built lowered erased typed readable iha ihb
    case bool tr => exact False.elim (int_bin_rejects_bool .add built)
    all_goals simp [bridgeType] at proof
  case sub bTy left right proof _leftBridge _rightBridge iha ihb =>
    cases bTy
    case int tr =>
      exact int_bin_agrees .sub aligned ambient built lowered erased typed readable iha ihb
    case bool tr => exact False.elim (int_bin_rejects_bool .sub built)
    all_goals simp [bridgeType] at proof
  case mul bTy left right proof _leftBridge _rightBridge iha ihb =>
    cases bTy
    case int tr =>
      exact int_bin_agrees .mul aligned ambient built lowered erased typed readable iha ihb
    case bool tr => exact False.elim (int_bin_rejects_bool .mul built)
    all_goals simp [bridgeType] at proof
  case le bTy left right proof _leftBridge _rightBridge iha ihb =>
    cases bTy
    case int tr =>
      exact int_bin_agrees .le aligned ambient built lowered erased typed readable iha ihb
    case bool tr => exact False.elim (int_bin_rejects_bool .le built)
    all_goals simp [bridgeType] at proof
  case lt bTy left right proof _leftBridge _rightBridge iha ihb =>
    cases bTy
    case int tr =>
      exact int_bin_agrees .lt aligned ambient built lowered erased typed readable iha ihb
    case bool tr => exact False.elim (int_bin_rejects_bool .lt built)
    all_goals simp [bridgeType] at proof
  case ge bTy left right proof _leftBridge _rightBridge iha ihb =>
    cases bTy
    case int tr =>
      exact int_bin_agrees .ge aligned ambient built lowered erased typed readable iha ihb
    case bool tr => exact False.elim (int_bin_rejects_bool .ge built)
    all_goals simp [bridgeType] at proof
  case gt bTy left right proof _leftBridge _rightBridge iha ihb =>
    cases bTy
    case int tr =>
      exact int_bin_agrees .gt aligned ambient built lowered erased typed readable iha ihb
    case bool tr => exact False.elim (int_bin_rejects_bool .gt built)
    all_goals simp [bridgeType] at proof
  case and left right _lb _rb iha ihb =>
    exact bool_bin_agrees .and aligned ambient built lowered erased typed readable iha ihb
  case or left right _lb _rb iha ihb =>
    exact bool_bin_agrees .or aligned ambient built lowered erased typed readable iha ihb
  case implies left right _lb _rb iha ihb =>
    exact bool_bin_agrees .implies aligned ambient built lowered erased typed readable iha ihb
  case equiv left right _lb _rb iha ihb =>
    exact bool_bin_agrees .equiv aligned ambient built lowered erased typed readable iha ihb
  case equal bTy left right proof _lb _rb iha ihb =>
    cases bTy
    case int tr =>
      exact int_eq_agrees built lowered erased typed readable iha ihb
    case bool tr =>
      exact bool_eq_agrees built lowered erased typed readable iha ihb
    all_goals simp [bridgeType] at proof
  case notEqual bTy left right proof _lb _rb iha ihb =>
    cases bTy
    case int tr =>
      exact int_ne_agrees aligned ambient built lowered erased typed readable iha ihb
    case bool tr =>
      exact bool_ne_agrees aligned ambient built lowered erased typed readable iha ihb
    all_goals simp [bridgeType] at proof
  case neg bTy operand proof _bridge ih =>
    cases bTy
    case int tr =>
      exact int_neg_agrees aligned ambient built lowered erased typed readable ih
    case bool tr => exact False.elim (neg_rejects_bool built)
    all_goals simp [bridgeType] at proof
  case ite bTy guard yes no proof guardBridge yesBridge noBridge ihg ihy ihn =>
    cases bTy
    case int tr =>
      exact ite_agrees aligned (.inl rfl) guardBridge yesBridge noBridge built lowered erased
        typed readable ihg ihy ihn
    case bool tr =>
      exact ite_agrees aligned (.inr rfl) guardBridge yesBridge noBridge built lowered erased
        typed readable ihg ihy ihn
    all_goals simp [bridgeType] at proof
  case old => sorry

private theorem expr_agrees.exprAgrees
    {entry : CompilerScopes} {after : TranslateState}
    {factory : Lambda.Factory Core.CoreLParams} {unwritten : List Core.CoreIdent}
    {context : ReadContext}
    {expression : Boole.Expr} {value : TypedExpr} {raw target : Core.Expression.Expr}
    {ty : Lambda.LMonoTy}
    (bridge : BridgeTyped expression)
    (aligned : ScopesAgree entry)
    (ambient : ∀ fn : Lambda.LFunc Core.CoreLParams,
      Core.Factory[fn.name.name]? = some fn → factory[fn.name.name]? = some fn)
    (current : context.old = false)
    (built : expr expression context entry.source = .ok (value, entry.source))
    (lowered : toCoreExpr expression entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (typed : ExprWellTyped entry.context entry.variables target ty)
    (readable : ready unwritten target = true) :
    after = entry.lowering ∧
      ExprAgrees (ScopedStoresAgree entry.source factory unwritten) value.eval target := by
  obtain ⟨stable, agrees⟩ := expr_agrees bridge aligned ambient current built lowered erased typed readable
  refine ⟨stable, ?_⟩
  intro state env result related evaluated
  obtain ⟨_, v, encoded, core⟩ := agrees state env result related evaluated
  exact ⟨v, encoded, core⟩

end Strata.Boole.Hoare
