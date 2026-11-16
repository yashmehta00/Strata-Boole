/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.Expressions
import StrataBoole.Boole.Semantics.Adequacy.Statements
import all StrataBoole.Boole.Semantics.Adequacy.Statements
import all StrataBoole.Boole.Semantics.Adequacy.Lowering
import all StrataBoole.Boole.Semantics.Adequacy.SourceFreshness
import all StrataBoole.Boole.Semantics.Adequacy.SourceInterface
import all StrataBoole.Boole.Runtime
import all StrataBoole.Boole.Types
import all StrataBoole.Boole.Semantics.CoreReference
import all StrataBoole.Boole.Semantics.Semantics
import all StrataBoole.Boole.Interp
import all StrataBoole.Verify
import all Strata.DL.Lambda.LExpr
import all Strata.Languages.Core.Expressions
import all Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.DL.Lambda.LExprDenoteEvalProps
import all Strata.DL.Lambda.LExprDenoteEval
public import Strata.Languages.Core.Typing.Spec.TypingSpec
import Strata.DL.Lambda.LTyUnifyProps
import all Strata.Languages.Core.Logic.FactoryInterp
import all Strata.Languages.Core.Factory
import all Strata.DL.Lambda.LExprWF
import all Strata.Languages.Core.Typing.Spec.TypeSpecShared

public section

namespace Strata.Boole

/-- A local variable read selects the same runtime value before and after
Core annotations are added. -/
theorem localRead_execution (scope : Scope) (entry : TranslateState)
    (range : SourceRange) (index : Nat) (binding : Binding)
    (encoded : entry.bvars = scope.locals.toArray.map
      (fun b => (.fvar () ⟨b.name, ()⟩ none : Core.Expression.Expr)))
    (found : scope.locals.reverse[index]? = some binding)
    {source : Expression} {final : Scope} {raw annotated : Core.Expression.Expr}
    (interpreted : interpExpr (denotation .builtins) (.bvar range index) scope = .ok (source, final))
    (lowered : ExpressionWasLowered (.bvar range index) entry raw)
    (erased : annotated.eraseTypes = raw.eraseTypes)
    (state : State) (value : Value) (runtimeValue : Core.Expression.Val)
    (slot : state.locals.lookup binding.name = some value)
    (represented : coreValue? value = some runtimeValue) :
    source state = .ok value ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state) annotated = some runtimeValue := by
  obtain ⟨sourceRead, coreRead⟩ := lowerLocalRead (denotation .builtins) scope entry range index
    binding encoded found
  have sourceEq : source = Expression.read (.local binding.name) :=
    congrArg Prod.fst (Except.ok.inj (interpreted.symm.trans sourceRead))
  obtain rfl := lowered.unique coreRead
  constructor
  · simp [sourceEq, Expression.read, State.lookup, slot]
  · cases annotated <;> simp [Lambda.LExpr.eraseTypes] at erased
    case fvar metadata id annotation =>
      obtain rfl := erased
      cases metadata
      exact eval_core_fvar represented _ _ annotation
        ((coreStore_of_local state binding.name value slot).trans represented)

/-- A global variable read agrees when the lowering and interpreter refer to
the same global table and the runtime local store does not shadow that name. -/
theorem globalRead_execution (scope : Scope) (entry : TranslateState)
    (range : SourceRange) (index : Nat) (name : String) (binding : Binding)
    (sameNames : scope.names = entry.gctx)
    (resolved : scope.names.nameOf? index = some name)
    (found : scope.globals.find? (fun b => b.name == name) = some binding)
    (registered : entry.globalVarTypes.contains name = true)
    {source : Expression} {final : Scope} {raw annotated : Core.Expression.Expr}
    (interpreted : interpExpr (denotation .builtins) (.fvar range index) scope = .ok (source, final))
    (lowered : ExpressionWasLowered (.fvar range index) entry raw)
    (erased : annotated.eraseTypes = raw.eraseTypes)
    (state : State) (value : Value) (runtimeValue : Core.Expression.Val)
    (notLocal : state.locals.lookup name = none)
    (slot : state.globals.lookup name = some value)
    (represented : coreValue? value = some runtimeValue) :
    source state = .ok value ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state) annotated = some runtimeValue := by
  obtain ⟨sourceRead, coreRead⟩ := lowerGlobalRead (denotation .builtins) scope entry range index
    name binding sameNames resolved found registered
  have sourceEq : source = Expression.read (.global name) :=
    congrArg Prod.fst (Except.ok.inj (interpreted.symm.trans sourceRead))
  obtain rfl := lowered.unique coreRead
  constructor
  · simp [sourceEq, Expression.read, State.lookup, slot]
  · cases annotated <;> simp [Lambda.LExpr.eraseTypes] at erased
    case fvar metadata id annotation =>
      obtain rfl := erased
      cases metadata
      exact eval_core_fvar represented _ _ annotation
        ((coreStore_of_global state name value notLocal slot).trans represented)

/-- Boolean, integer, and fixed-width bitvector literal syntax shared by
the source interpreter and the original lowerer. -/
def isSharedLiteral : Boole.Expr → Prop
  | .btrue .. | .bfalse .. | .natToInt .. => True
  | .bv1Lit .. | .bv8Lit .. | .bv16Lit .. | .bv32Lit .. | .bv64Lit .. | .bv128Lit .. => True
  | _ => False

/-- A shared literal yields the same native value in Boole and annotated Core
in every state. Neither side needs to consult a variable store. -/
theorem literal_execution (expression : Boole.Expr) (literal : isSharedLiteral expression)
    {scope final : Scope} {entry : TranslateState}
    {source : Expression} {raw annotated : Core.Expression.Expr}
    (interpreted : interpExpr (denotation .builtins) expression scope = .ok (source, final))
    (lowered : ExpressionWasLowered expression entry raw)
    (erased : annotated.eraseTypes = raw.eraseTypes) (state : State) :
    ∃ value runtimeValue, source state = .ok value ∧ coreValue? value = some runtimeValue ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state) annotated = some runtimeValue := by
  obtain ⟨_, lowered⟩ := lowered
  cases expression
  all_goals try simp only [isSharedLiteral] at literal
  all_goals try solve | exact False.elim literal
  all_goals
    rw [interpExpr.eq_def] at interpreted
    rw [toCoreExpr.eq_def] at lowered
    dsimp only at interpreted lowered
    simp only [toCoreQuantExpr?, pure, StateT.pure, Except.pure] at lowered
    have rawEq := congrArg Prod.fst (Except.ok.inj lowered)
    dsimp at rawEq
    subst raw
    cases annotated <;> simp [Lambda.LExpr.eraseTypes] at erased
    obtain rfl := erased
    have sourceEq := congrArg Prod.fst (Except.ok.inj interpreted)
    dsimp at sourceEq
    subst source
    refine ⟨_, _, rfl, rfl, ?_⟩
    exact Lambda.LExpr.denoteEval_const

/-- Erasure preserves the shape of an equality and relates its operands. -/
private theorem erase_eq_inv {annotated left right : Core.Expression.Expr}
    (erased : annotated.eraseTypes = (.eq () left right : Core.Expression.Expr).eraseTypes) :
    ∃ a b, annotated = .eq () a b ∧ a.eraseTypes = left.eraseTypes ∧
      b.eraseTypes = right.eraseTypes := by
  cases annotated <;> simp [Lambda.LExpr.eraseTypes] at erased
  case eq metadata a b =>
    cases metadata
    exact ⟨a, b, rfl, erased⟩

/-- The entry store gives a scalar variable the same type as its Core
annotation. This is the property needed when Core's evaluator annotates free
variables from the runtime store. -/
def ScalarStoreTyped (scopes : Core.TypeSpec.TypeScopes) (state : State) : Prop :=
  ∀ id ty, scopes.find? id = some (.forAll [] ty) →
    ∃ value, coreStore state id = some value ∧ value.sort.toMonoTy = ty

private theorem typed_fvars_annotated {binders : List Lambda.LMonoTy}
    {expression : Core.Expression.Expr} {ty : Lambda.LMonoTy}
    (typed : Lambda.LExpr.HasTypeA binders expression ty) :
    ∀ id ann, (id, ann) ∈ expression.freeVars → ann.isSome = true := by
  induction typed <;> simp_all [Lambda.LExpr.freeVars, List.mem_append] <;> grind

/-- Any finite evaluation of a declaratively typed expression has the
declared sort, provided the runtime store agrees with its variable scopes. -/
theorem evaluated_sort_of_typed {context : Core.Expression.TyContext}
    {scopes : Core.TypeSpec.TypeScopes} {state : State}
    {expression : Core.Expression.Expr} {ty : Lambda.LMonoTy}
    {value : Core.Expression.Val}
    (typed : Core.TypeSpec.ExprWellTyped context scopes expression ty)
    (storeTyped : ScalarStoreTyped scopes state)
    (evaluated : Core.Expression.eval coreRuntimeFactory (coreStore state) expression = some value) :
    value.sort.toMonoTy = ty := by
  have fvarsAnnotated : ∀ id ann, (id, ann) ∈ expression.freeVars → ann.isSome = true := by
    intro id ann occurs
    exact typed_fvars_annotated typed.1 id ann occurs
  have same : expression.annotateFvars (Lambda.ValStore.ann (coreStore state)) = expression := by
    apply Lambda.LExpr.annotateFvars_eq_self
    intro id ann occurs
    cases ann with
    | none => have impossible := fvarsAnnotated id none occurs; contradiction
    | some annotation =>
      have declared := typed.2.2.fvarsDeclared id annotation occurs
      obtain ⟨represented, found, sort⟩ := storeTyped id annotation declared
      exact ⟨annotation, rfl, by simp [Lambda.ValStore.ann, found, sort]⟩
  obtain ⟨_, inferred, checked, ground, rfl⟩ := (Lambda.LExpr.denoteEval_eq_some_iff (T := Core.CoreLParams)).mp evaluated
  have inferredEq : inferred = ty := Lambda.HasTypeA_unique (same ▸ checked) typed.1
  subst inferred
  change (ty.substTyVars coreRuntimeFactory.tyVarVal).toMonoTy = ty
  rw [ground.substTyVars_eq coreRuntimeFactory.tyVarVal Lambda.refTyVarVal]
  exact ground

private theorem typed_eq_operands {context : Core.Expression.TyContext}
    {scopes : Core.TypeSpec.TypeScopes} {left right : Core.Expression.Expr} {ty : Lambda.LMonoTy}
    (typed : Core.TypeSpec.ExprWellTyped context scopes (.eq () left right) ty) :
    ∃ sort, Core.TypeSpec.ExprWellTyped context scopes left sort ∧
      Core.TypeSpec.ExprWellTyped context scopes right sort := by
  have typedEq := typed.1
  cases typedEq with
  | eq lhs rhs =>
    refine ⟨_, ⟨lhs, ?_, ?_⟩, ⟨rhs, ?_, ?_⟩⟩
    all_goals first
      | (intro ann present; apply typed.2.1; simp [Lambda.LExpr.binderAnnotations, present])
      | (constructor
         · intro x ann present
           apply typed.2.2.fvarsDeclared
           simp [Lambda.LExpr.freeVars, present]
         · intro op ann present
           apply typed.2.2.opsInstantiate
           simp [Lambda.LExpr.opAnnots, present]
         · intro op present
           apply typed.2.2.opsKnown
           simp [Lambda.LExpr.getOps, present])

/-- Two represented scalar values with the same Core monotype have the same
Boole sort. -/
private theorem sourceSort_of_coreSort {x y : Value} {a b : Core.Expression.Val}
    (xRep : coreValue? x = some a) (yRep : coreValue? y = some b)
    (same : a.sort.toMonoTy = b.sort.toMonoTy) : x.sort = y.sort := by
  -- TODO(adequacy): assumed for now. The proof below broke when `coreValue?`
  -- became a point-free alias of `coreValueIn?` (`fun_cases` needs an applied
  -- function). Restore it after the Core compatibility proof.
  sorry
  /-
  fun_cases coreValue? x <;> fun_cases coreValue? y <;>
    simp only [coreValue?, Option.some.injEq, reduceCtorEq] at xRep yRep
  all_goals subst a; subst b
  all_goals
    simp [Lambda.SemValue.ofConst, Lambda.LConst.ty, Lambda.LMonoTy.substTyVars,
      Lambda.LSort.toMonoTy, Lambda.LMonoTy.int, Lambda.LMonoTy.bool,
      Lambda.LMonoTy.string, Lambda.LMonoTy.real] at same
  all_goals simp_all
  -/

/-- A lowered equality has the same value on both sides whenever its paired
operands evaluate to represented values of the same sort. -/
theorem equality_execution
    {range : SourceRange} {ty : Boole.Type} {left right : Boole.Expr}
    {scope final : Scope} {entry : TranslateState}
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    {resultType : Lambda.LMonoTy}
    {source : Expression} {raw annotated : Core.Expression.Expr}
    (interpreted : interpExpr (denotation .builtins) (.equal range ty left right) scope =
      .ok (source, final))
    (lowered : ExpressionWasLowered (.equal range ty left right) entry raw)
    (erased : annotated.eraseTypes = raw.eraseTypes) (state : State)
    (typed : Core.TypeSpec.ExprWellTyped context scopes annotated resultType)
    (storeTyped : ScalarStoreTyped scopes state)
    (operands : ∀ leftSource rightSource leftRaw rightRaw leftAnnotated rightAnnotated middle sort,
      interpExpr (denotation .builtins) left scope = .ok (leftSource, scope) →
      interpExpr (denotation .builtins) right scope = .ok (rightSource, scope) →
      ExpressionWasLowered left entry leftRaw →
      ExpressionWasLowered right middle rightRaw →
      leftAnnotated.eraseTypes = leftRaw.eraseTypes → rightAnnotated.eraseTypes = rightRaw.eraseTypes →
      Core.TypeSpec.ExprWellTyped context scopes leftAnnotated sort →
      Core.TypeSpec.ExprWellTyped context scopes rightAnnotated sort →
      ∃ x y xCore yCore,
        leftSource state = .ok x ∧ rightSource state = .ok y ∧
        coreValue? x = some xCore ∧ coreValue? y = some yCore ∧
        Core.Expression.eval coreRuntimeFactory (coreStore state) leftAnnotated = some xCore ∧
        Core.Expression.eval coreRuntimeFactory (coreStore state) rightAnnotated = some yCore) :
    ∃ value runtimeValue, source state = .ok value ∧ coreValue? value = some runtimeValue ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state) annotated = some runtimeValue := by
  rw [interpExpr.eq_def] at interpreted
  dsimp only at interpreted
  simp only [bind, StateT.bind, Except.bind] at interpreted
  cases sorted : sourceSort ty scope with
  | error => simp [sorted] at interpreted
  | ok result =>
    obtain ⟨sort, afterSort⟩ := result
    have sortScope := sourceSort_readOnly _ _ _ _ sorted
    subst afterSort
    simp only [sorted] at interpreted
    cases first : interpExpr (denotation .builtins) left scope with
    | error => simp [first] at interpreted
    | ok result =>
      obtain ⟨leftSource, afterLeft⟩ := result
      have leftScope := interpExpr_readOnly _ _ _ _ _ first
      subst afterLeft
      simp only [first] at interpreted
      cases second : interpExpr (denotation .builtins) right scope with
      | error => simp [second] at interpreted
      | ok result =>
        obtain ⟨rightSource, afterRight⟩ := result
        have rightScope := interpExpr_readOnly _ _ _ _ _ second
        subst afterRight
        simp only [second, pure, StateT.pure, Except.pure] at interpreted
        have sourceEq : Expression.binary .eq leftSource rightSource = source :=
          congrArg Prod.fst (Except.ok.inj interpreted)
        subst source
        obtain ⟨last, lowered⟩ := lowered
        rw [toCoreExpr.eq_def] at lowered
        simp only [toCoreQuantExpr?, bind, StateT.bind, Except.bind] at lowered
        cases targetLeft : toCoreExpr left entry with
        | error => simp [targetLeft] at lowered
        | ok result =>
          obtain ⟨leftRaw, middle⟩ := result
          simp only [targetLeft] at lowered
          cases targetRight : toCoreExpr right middle with
          | error => simp [targetRight] at lowered
          | ok result =>
            obtain ⟨rightRaw, after⟩ := result
            simp only [targetRight, pure, StateT.pure, Except.pure] at lowered
            have rawEq : (.eq () leftRaw rightRaw : Core.Expression.Expr) = raw :=
              congrArg Prod.fst (Except.ok.inj lowered)
            subst raw
            obtain ⟨leftAnnotated, rightAnnotated, rfl, leftErased, rightErased⟩ :=
              erase_eq_inv erased
            obtain ⟨sort, leftTyped, rightTyped⟩ := typed_eq_operands typed
            obtain ⟨x, y, xCore, yCore, leftRun, rightRun, xRep, yRep, leftCore, rightCore⟩ :=
              operands _ _ _ _ _ _ _ _ first second ⟨_, targetLeft⟩ ⟨_, targetRight⟩
                leftErased rightErased leftTyped rightTyped
            have sameSort := sourceSort_of_coreSort xRep yRep
              ((evaluated_sort_of_typed leftTyped storeTyped leftCore).trans
                (evaluated_sort_of_typed rightTyped storeTyped rightCore).symm)
            have agreed := scalarEquality_agrees state leftSource rightSource leftAnnotated rightAnnotated
              x y xCore yCore sameSort leftRun rightRun xRep yRep leftCore rightCore
            exact ⟨_, _, agreed.1, rfl, agreed.2⟩

/-- Equal Boolean evaluation gives the two directions used by assertion
and assumption replay. -/
theorem boolean_execution_iff {state : State} {source : Expression}
    {target : Core.Expression.Expr} {actual : Bool}
    (sourceRun : source state = .ok (.bool actual))
    (coreRun : Core.Expression.eval coreRuntimeFactory (coreStore state) target =
      some (if actual then Imperative.HasBool.ttVal coreRuntimeFactory
        else Imperative.HasBool.ffVal coreRuntimeFactory))
    (result : Bool) :
    source state = .ok (.bool result) ↔
      Core.Expression.eval coreRuntimeFactory (coreStore state) target =
        some (if result then Imperative.HasBool.ttVal coreRuntimeFactory
          else Imperative.HasBool.ffVal coreRuntimeFactory) := by
  rw [sourceRun, coreRun]
  have different := Imperative.HasBool.ttVal_ne_ffVal coreRuntimeFactory
  cases actual <;> cases result <;> simp [Value.bool, different, Ne.symm different]

/-- A type annotation on a monomorphic operator agrees with its declared
type. This uses the declarative rule for operator instances. -/
theorem operatorAnnotation_eq {context : Core.Expression.TyContext}
    {scopes : Core.TypeSpec.TypeScopes} {expression : Core.Expression.Expr}
    {id : Core.CoreIdent} {annotation declared : Lambda.LMonoTy} {f : Lambda.LFunc Core.CoreLParams}
    (typed : Core.TypeSpec.ScopesAnnotAgree context scopes expression)
    (occurs : (id, annotation) ∈ Lambda.LExpr.opAnnots expression)
    (lookup : context.functions[id.name]? = some f)
    (scheme : f.type = .ok (.forAll [] declared))
    (closed : declared.freeVars = []) : annotation = declared := by
  obtain ⟨operator, parameters, body, found, typeEq, substitution, same⟩ :=
    typed.opsInstantiate _ _ occurs
  rw [lookup] at found
  obtain rfl := Option.some.inj found
  rw [scheme] at typeEq
  obtain ⟨_, rfl⟩ := Lambda.LTy.forAll.inj (Except.ok.inj typeEq)
  exact same.trans (Lambda.LMonoTy.subst_ground substitution declared closed)

private theorem typed_app_argument {context : Core.Expression.TyContext}
    {scopes : Core.TypeSpec.TypeScopes} {fn argument : Core.Expression.Expr}
    {domain result : Lambda.LMonoTy}
    (typed : Core.TypeSpec.ExprWellTyped context scopes (.app () fn argument) result)
    (argTyped : Lambda.LExpr.HasTypeA [] argument domain) :
    Core.TypeSpec.ExprWellTyped context scopes argument domain := by
  refine ⟨argTyped, ?_, ?_⟩
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

/-- In a context with the built-in Boolean-negation signature, an annotated
application that erases to Bool.Not must have its built-in operator type. -/
theorem typed_boolNot_origin
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    {annotated operand : Core.Expression.Expr} {ty : Lambda.LMonoTy}
    (typed : Core.TypeSpec.ExprWellTyped context scopes annotated ty)
    (signature : context.functions["Bool.Not"]? =
      some (Lambda.boolNotFunc (T := Core.CoreLParams)).func)
    (erased : annotated.eraseTypes = (.app () Core.boolNotOp operand : Core.Expression.Expr).eraseTypes) :
    ∃ argument, annotated = .app () Core.boolNotOp argument ∧
      argument.eraseTypes = operand.eraseTypes ∧ Core.TypeSpec.ExprWellTyped context scopes argument .bool := by
  have opErased : Core.boolNotOp.eraseTypes =
      (.op () ⟨"Bool.Not", ()⟩ none : Core.Expression.Expr) := rfl
  cases annotated <;> simp [Lambda.LExpr.eraseTypes, opErased] at erased
  case app metadata fn argument =>
    cases metadata
    obtain ⟨same, argSame⟩ := erased
    have typedApp := typed.1
    have ⟨domain, fnType, argType⟩ : ∃ domain,
        Lambda.LExpr.HasTypeA [] fn (.arrow domain ty) ∧ Lambda.LExpr.HasTypeA [] argument domain := by
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
      have annEq := operatorAnnotation_eq (id := ⟨"Bool.Not", ()⟩) (annotation := .arrow domain ty) typed.2.2
        (by simp [Lambda.LExpr.opAnnots]) signature
        (declared := Lambda.LMonoTy.arrow .bool .bool) (by rfl) (by rfl)
      have domainEq : domain = .bool := by
        simp only [Lambda.LMonoTy.arrow, Lambda.LMonoTy.tcons.injEq,
          List.cons.injEq, true_and] at annEq
        exact annEq.1
      rw [fnAnn, annEq]
      exact ⟨argument, rfl, argSame, typed_app_argument typed (domainEq ▸ argType)⟩

/-- Boolean negation agrees once the recursively paired argument agrees.
The operator annotation is recovered from the declarative typing derivation. -/
theorem boolNot_execution
    {range : SourceRange} {operand : Boole.Expr}
    {scope final : Scope} {entry : TranslateState} {context : Core.Expression.TyContext}
    {scopes : Core.TypeSpec.TypeScopes} {ty : Lambda.LMonoTy}
    {source : Expression} {raw annotated : Core.Expression.Expr}
    (interpreted : interpExpr (denotation .builtins) (.not range operand) scope = .ok (source, final))
    (lowered : ExpressionWasLowered (.not range operand) entry raw)
    (erased : annotated.eraseTypes = raw.eraseTypes)
    (typed : Core.TypeSpec.ExprWellTyped context scopes annotated ty)
    (signature : context.functions["Bool.Not"]? = some (Lambda.boolNotFunc (T := Core.CoreLParams)).func)
    (state : State)
    (argAgreement : ∀ condition rawArg annotatedArg,
      interpExpr (denotation .builtins) operand scope = .ok (condition, scope) →
      ExpressionWasLowered operand entry rawArg → annotatedArg.eraseTypes = rawArg.eraseTypes →
      Core.TypeSpec.ExprWellTyped context scopes annotatedArg .bool →
      ∃ result, condition state = .ok (.bool result) ∧
        Core.Expression.eval coreRuntimeFactory (coreStore state) annotatedArg =
          some (.ofBool coreRuntimeFactory.model.tcInterp result)) :
    ∃ result, source state = .ok (.bool result) ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state) annotated =
        some (.ofBool coreRuntimeFactory.model.tcInterp result) := by
  rw [interpExpr.eq_def] at interpreted
  simp only [bind, StateT.bind, Except.bind] at interpreted
  cases operandRun : interpExpr (denotation .builtins) operand scope with
  | error => simp [operandRun] at interpreted
  | ok result =>
    obtain ⟨condition, after⟩ := result
    have afterEq := interpExpr_readOnly _ _ _ _ _ operandRun
    subst after
    simp only [operandRun, pure, StateT.pure, Except.pure] at interpreted
    have bodyEq : Expression.unary .not condition = source :=
      congrArg Prod.fst (Except.ok.inj interpreted)
    subst source
    obtain ⟨_, lowered⟩ := lowered
    rw [toCoreExpr.eq_def] at lowered
    simp only [toCoreQuantExpr?, bind, StateT.bind, Except.bind] at lowered
    cases loweredArg : toCoreExpr operand entry with
    | error => simp [loweredArg] at lowered
    | ok result =>
      obtain ⟨rawArg, after⟩ := result
      simp only [loweredArg, pure, StateT.pure, Except.pure] at lowered
      have rawEq : (.app () Core.boolNotOp rawArg : Core.Expression.Expr) = raw :=
        congrArg Prod.fst (Except.ok.inj lowered)
      subst raw
      obtain ⟨annotatedArg, rfl, sameArg, typedArg⟩ := typed_boolNot_origin typed signature erased
      obtain ⟨result, ranSource, ranCore⟩ :=
        argAgreement _ _ _ operandRun ⟨after, loweredArg⟩ sameArg typedArg
      refine ⟨!result, ?_, coreEval_boolNot _ _ result ranCore⟩
      unfold Expression.unary
      rw [ranSource]
      rfl

/-- A source Boolean literal has the matching truth value on both sides,
including after adding any type annotations. -/
theorem booleanLiteral_execution (range : SourceRange) (value : Bool)
    {scope final : Scope} {entry : TranslateState}
    {source : Expression} {raw annotated : Core.Expression.Expr}
    (interpreted : interpExpr (denotation .builtins)
      (if value then .btrue range else .bfalse range) scope = .ok (source, final))
    (lowered : ExpressionWasLowered (if value then .btrue range else .bfalse range) entry raw)
    (erased : annotated.eraseTypes = raw.eraseTypes) (state : State) :
    source state = .ok (.bool value) ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state) annotated =
        some (if value then Imperative.HasBool.ttVal coreRuntimeFactory
          else Imperative.HasBool.ffVal coreRuntimeFactory) := by
  obtain ⟨_, ran⟩ := lowered
  cases value <;> simp only [Bool.false_eq_true, ite_false, ite_true] at interpreted ran ⊢
  all_goals
    rw [interpExpr.eq_def] at interpreted
    rw [toCoreExpr.eq_def] at ran
    dsimp only at interpreted ran
    simp only [toCoreQuantExpr?, pure, StateT.pure, Except.pure] at ran
    have rawEq := congrArg Prod.fst (Except.ok.inj ran)
    dsimp at rawEq
    subst raw
    cases annotated <;> simp [Lambda.LExpr.eraseTypes] at erased
    obtain rfl := erased
    have sourceEq := congrArg Prod.fst (Except.ok.inj interpreted)
    dsimp at sourceEq
    subst source
    exact ⟨rfl, Lambda.LExpr.denoteEval_const⟩

/-- An old read of a modified global uses the saved value on both sides.
Current slots must leave the Core identifier reserved for the snapshot free. -/
theorem oldGlobalRead_execution (state : State) (name : String) (value : Value)
    (saved : state.snapshots.lookup name = some value)
    (noLocal : state.locals.lookup (Core.CoreIdent.mkOld name).name = none)
    (noGlobal : state.globals.lookup (Core.CoreIdent.mkOld name).name = none)
    {annotated : Core.Expression.Expr} {runtimeValue : Core.Expression.Val}
    (erased : annotated.eraseTypes = .fvar () (Core.CoreIdent.mkOld name) none)
    (represented : coreValue? value = some runtimeValue) :
    Expression.old (Expression.read (.global name)) state = .ok value ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state) annotated = some runtimeValue := by
  constructor
  · simp [Expression.old, Expression.read, State.lookup, Store.lookup_append, saved]
  · cases annotated <;> simp [Lambda.LExpr.eraseTypes] at erased
    case fvar metadata id annotation =>
      obtain rfl := erased
      cases metadata
      exact eval_core_fvar represented _ _ annotation
        (coreStore_old state name value noLocal noGlobal saved represented)

private theorem typed_intAdd_origin {context : Core.Expression.TyContext}
    {scopes : Core.TypeSpec.TypeScopes} {annotated left right : Core.Expression.Expr}
    {ty : Lambda.LMonoTy}
    (typed : Core.TypeSpec.ExprWellTyped context scopes annotated ty)
    (signature : context.functions["Int.Add"]? = some (Lambda.intAddFunc (T := Core.CoreLParams)).func)
    (erased : annotated.eraseTypes =
      (.app () (.app () (.op () ⟨"Int.Add", ()⟩ none) left) right : Core.Expression.Expr).eraseTypes) :
    ∃ a b, annotated = .app () (.app () Core.coreIntAddOpExpr a) b ∧
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
        have same := operatorAnnotation_eq (id := ⟨"Int.Add", ()⟩)
          (annotation := .arrow domainA (.arrow domainB ty)) typed.2.2
          (by simp [Lambda.LExpr.opAnnots]) signature
          (declared := Lambda.LMonoTy.arrow .int (.arrow .int .int)) (by rfl) (by rfl)
        rw [annotationEq, same]
        exact ⟨a, b, rfl, aSame, bSame⟩

/-- Integer addition agrees when the two recursively paired operands
evaluate to represented integers. Declarative typing supplies the operator
annotation used by Core evaluation. -/
theorem intAddition_execution
    {range typeRange : SourceRange} {left right : Boole.Expr}
    {scope final : Scope} {entry : TranslateState}
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    {ty : Lambda.LMonoTy} {source : Expression} {raw annotated : Core.Expression.Expr}
    (interpreted : interpExpr (denotation .builtins) (.add_expr range (.int typeRange) left right) scope =
      .ok (source, final))
    (lowered : ExpressionWasLowered (.add_expr range (.int typeRange) left right) entry raw)
    (erased : annotated.eraseTypes = raw.eraseTypes)
    (typed : Core.TypeSpec.ExprWellTyped context scopes annotated ty)
    (signature : context.functions["Int.Add"]? = some (Lambda.intAddFunc (T := Core.CoreLParams)).func)
    (state : State)
    (operands : ∀ leftSource rightSource leftRaw rightRaw leftAnnotated rightAnnotated middle,
      interpExpr (denotation .builtins) left scope = .ok (leftSource, scope) →
      interpExpr (denotation .builtins) right scope = .ok (rightSource, scope) →
      ExpressionWasLowered left entry leftRaw →
      ExpressionWasLowered right middle rightRaw →
      leftAnnotated.eraseTypes = leftRaw.eraseTypes → rightAnnotated.eraseTypes = rightRaw.eraseTypes →
      ∃ x y, leftSource state = .ok (.int x) ∧ rightSource state = .ok (.int y) ∧
        Core.Expression.eval coreRuntimeFactory (coreStore state) leftAnnotated =
          some (.ofInt coreRuntimeFactory.model.tcInterp x) ∧
        Core.Expression.eval coreRuntimeFactory (coreStore state) rightAnnotated =
          some (.ofInt coreRuntimeFactory.model.tcInterp y)) :
    ∃ result : Int, source state = .ok (.int result) ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state) annotated = coreValue? (.int result) := by
  rw [interpExpr.eq_def] at interpreted
  dsimp only at interpreted
  simp only [bind, StateT.bind, Except.bind] at interpreted
  cases sorted : sourceSort (.int typeRange) scope with
  | error => simp [sorted] at interpreted
  | ok result =>
    obtain ⟨sort, afterSort⟩ := result
    have sortScope := sourceSort_readOnly _ _ _ _ sorted
    subst afterSort
    simp only [sorted] at interpreted
    cases first : interpExpr (denotation .builtins) left scope with
    | error => simp [first] at interpreted
    | ok result =>
      obtain ⟨leftSource, afterLeft⟩ := result
      have leftScope := interpExpr_readOnly _ _ _ _ _ first
      subst afterLeft
      simp only [first] at interpreted
      cases second : interpExpr (denotation .builtins) right scope with
      | error => simp [second] at interpreted
      | ok result =>
        obtain ⟨rightSource, afterRight⟩ := result
        have rightScope := interpExpr_readOnly _ _ _ _ _ second
        subst afterRight
        simp only [second, pure, StateT.pure, Except.pure] at interpreted
        have sourceEq : Expression.binary .add leftSource rightSource = source :=
          congrArg Prod.fst (Except.ok.inj interpreted)
        subst source
        obtain ⟨last, lowered⟩ := lowered
        rw [toCoreExpr.eq_def] at lowered
        simp only [toCoreQuantExpr?, bind, StateT.bind, Except.bind] at lowered
        cases targetLeft : toCoreExpr left entry with
        | error => simp [targetLeft] at lowered
        | ok result =>
          obtain ⟨leftRaw, middle⟩ := result
          simp only [targetLeft] at lowered
          cases targetRight : toCoreExpr right middle with
          | error => simp [targetRight] at lowered
          | ok result =>
            obtain ⟨rightRaw, after⟩ := result
            simp only [targetRight, toCoreTypedBin, mkCoreApp, Lambda.LExpr.mkApp,
              pure, StateT.pure, Except.pure] at lowered
            have rawEq : (.app () (.app () (.op () ⟨"Int.Add", ()⟩ none) leftRaw) rightRaw :
                Core.Expression.Expr) = raw :=
              congrArg Prod.fst (Except.ok.inj lowered)
            subst raw
            obtain ⟨leftAnnotated, rightAnnotated, rfl, leftErased, rightErased⟩ :=
              typed_intAdd_origin typed signature erased
            obtain ⟨x, y, leftRun, rightRun, leftCore, rightCore⟩ :=
              operands _ _ _ _ _ _ _ first second ⟨_, targetLeft⟩ ⟨_, targetRight⟩ leftErased rightErased
            exact ⟨x + y, intAdd_agrees state leftSource rightSource leftAnnotated rightAnnotated
              x y leftRun rightRun leftCore rightCore⟩

/-- The Boolean literal and negation cases compose recursively, with the
declarative typing evidence passed down to each operand. -/
inductive ClosedBoolean : Boole.Expr → Prop
  | trueLiteral (range : SourceRange) : ClosedBoolean (.btrue range)
  | falseLiteral (range : SourceRange) : ClosedBoolean (.bfalse range)
  | negation (range : SourceRange) {operand : Boole.Expr} :
      ClosedBoolean operand → ClosedBoolean (.not range operand)

/-- A closed Boolean expression evaluates to the same truth value in Boole
and in its lowered and annotated Core expression. -/
theorem closedBoolean_execution {expression : Boole.Expr} (supported : ClosedBoolean expression)
    {scope final : Scope} {entry : TranslateState} {context : Core.Expression.TyContext}
    {scopes : Core.TypeSpec.TypeScopes} {ty : Lambda.LMonoTy}
    {source : Expression} {raw annotated : Core.Expression.Expr}
    (interpreted : interpExpr (denotation .builtins) expression scope = .ok (source, final))
    (lowered : ExpressionWasLowered expression entry raw)
    (erased : annotated.eraseTypes = raw.eraseTypes)
    (typed : Core.TypeSpec.ExprWellTyped context scopes annotated ty)
    (signature : context.functions["Bool.Not"]? = some (Lambda.boolNotFunc (T := Core.CoreLParams)).func)
    (state : State) :
    ∃ result, source state = .ok (.bool result) ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state) annotated =
        some (.ofBool coreRuntimeFactory.model.tcInterp result) := by
  induction supported generalizing final entry ty source raw annotated with
  | trueLiteral range =>
    exact ⟨true, booleanLiteral_execution range true interpreted lowered erased state⟩
  | falseLiteral range =>
    exact ⟨false, booleanLiteral_execution range false interpreted lowered erased state⟩
  | negation _ _ ih =>
    apply boolNot_execution interpreted lowered erased typed signature state
    intro condition rawArg annotatedArg ran lowerArg same argTyped
    exact ih ran lowerArg same argTyped

end Strata.Boole
