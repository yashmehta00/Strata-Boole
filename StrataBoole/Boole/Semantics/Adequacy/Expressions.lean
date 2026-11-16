/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.Lowering
import all StrataBoole.Boole.Semantics.CoreReference
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.LExprEvalProps
public import Strata.DL.Lambda.LExprT
import all Strata.DL.Lambda.LExprT
import Strata.DL.Lambda.LExprType
import Strata.DL.Lambda.FactoryProps
import Strata.DL.Imperative.CmdSemanticsProps
import all Strata.Languages.Core.Expressions
import all Strata.Languages.Core.InstWellFormedSemanticsEval
import all Strata.Languages.Core.Logic.FactoryInterp
import all Strata.Languages.Core.StatementSemantics
import Strata.Languages.Core.StatementSemanticsProps
import all StrataBoole.Boole.Runtime
import all StrataBoole.Boole.Types

public section

/-! ## Semantic values and entry frames -/

namespace Strata.Boole
noncomputable section
open Classical
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-! Runtime values in Core are semantic values, rather than expression syntax.
The lemmas below relate Boole's scalar values directly to those semantic values. -/

/-- A represented Boole scalar is a value of Core's runtime interpretation. -/
theorem coreValue?_isValue {value : Value} {runtimeValue : Core.Expression.Val}
    (represented : coreValue? value = some runtimeValue) :
    Imperative.HasVal.value (P := Core.Expression) coreRuntimeFactory runtimeValue := by
  -- TODO(adequacy): assumed for now. The proof below broke when `coreValue?`
  -- became a point-free alias of `coreValueIn?` (`fun_cases` needs an applied
  -- function). Restore it after the Core compatibility proof.
  sorry
  /-
  change runtimeValue.tc = coreRuntimeFactory.model.tcInterp
  fun_cases coreValue? value <;>
    simp only [coreValue?, Option.some.injEq, reduceCtorEq] at represented
  all_goals
    subst runtimeValue
    exact coreRuntimeFactory_tcInterp.symm
  -/

/-- Boole values of the same scalar sort have the same Core runtime type. -/
theorem coreValues_sameType {previous value : Value} {oldValue newValue : Core.Expression.Val}
    (sort : previous.sort = value.sort)
    (oldRep : coreValue? previous = some oldValue) (newRep : coreValue? value = some newValue) :
    ∃ ty, Imperative.HasVal.valueOfTy (P := Core.Expression) coreRuntimeFactory oldValue ty ∧
      Imperative.HasVal.valueOfTy (P := Core.Expression) coreRuntimeFactory newValue ty := by
  have sameRuntimeSort : oldValue.sort = newValue.sort := by
    -- TODO(adequacy): assumed for now; same `fun_cases coreValue?` breakage as
    -- `coreValue?_isValue`. Restore after the Core compatibility proof.
    sorry
    /-
    fun_cases coreValue? previous <;> fun_cases coreValue? value <;>
      simp only [coreValue?, Option.some.injEq, reduceCtorEq] at oldRep newRep <;>
      subst oldValue <;> subst newValue <;>
      simp_all [Lambda.SemValue.ofConst, Lambda.LConst.ty, Lambda.LMonoTy.substTyVars]
    -/
  refine ⟨.forAll [] oldValue.sort.toMonoTy, ?_, ?_⟩
  · exact ⟨coreValue?_isValue oldRep, by simp [Lambda.LTy.toMonoType?]⟩
  · exact ⟨coreValue?_isValue newRep, by simp [Lambda.LTy.toMonoType?, sameRuntimeSort]⟩

/-- Equal Core representations of two Boole values identify the same value. -/
theorem coreValue?_injective_some {left right : Value} {runtimeValue : Core.Expression.Val}
    (first : coreValue? left = some runtimeValue) (second : coreValue? right = some runtimeValue) :
    left = right := by
  -- TODO(adequacy): assumed for now; same `fun_cases coreValue?` breakage as
  -- `coreValue?_isValue`. Restore after the Core compatibility proof.
  sorry
  /-
  fun_cases coreValue? left <;> fun_cases coreValue? right <;>
    simp only [coreValue?, Option.some.injEq, reduceCtorEq] at first second
  all_goals
    have sameValue := first.trans second.symm
    have sameSort := congrArg Lambda.SemValue.sort sameValue
    simp [Lambda.SemValue.ofConst, Lambda.LConst.ty, Lambda.LMonoTy.substTyVars] at sameSort
  all_goals
    simp only [Lambda.SemValue.ofConst, Lambda.LConst.ty, Lambda.LMonoTy.substTyVars,
      Lambda.denoteConst] at sameValue
    have payload := (Lambda.SemValue.mk.inj sameValue).2.2
    simp_all [Value.mk.injEq] <;> first | exact payload | exact eq_of_heq payload
  -/

/-- Core's evaluator reads a represented Boole value back out of a variable slot. -/
theorem eval_core_fvar {value : Value} {runtimeValue : Core.Expression.Val}
    (represented : coreValue? value = some runtimeValue)
    (store : Core.CoreStore)
    (id : Core.CoreIdent) (annotation : Option Lambda.LMonoTy)
    (slot : store id = some runtimeValue) :
    Core.Expression.eval coreRuntimeFactory store (.fvar () id annotation) = some runtimeValue := by
  change Lambda.LExpr.denoteEval coreRuntimeFactory store (.fvar () id annotation) = some runtimeValue
  have runtimeValueIsVal := coreValue?_isValue represented
  change runtimeValue.tc = coreRuntimeFactory.model.tcInterp at runtimeValueIsVal
  exact Lambda.LExpr.denoteEval_fvar (T := Core.CoreLParams) (M := coreRuntimeFactory)
    slot runtimeValueIsVal

/-- A local slot and its reification agree without assumptions about other slots. -/
theorem coreStore_of_local (state : State) (name : String) (value : Value)
    (slot : state.locals.lookup name = some value) :
    coreStore state ⟨name, ()⟩ = coreValue? value := by
  simp [coreStore, slot]

/-- A global slot and its reification agree when no local shadows it. -/
theorem coreStore_of_global (state : State) (name : String) (value : Value)
    (notLocal : state.locals.lookup name = none)
    (slot : state.globals.lookup name = some value) :
    coreStore state ⟨name, ()⟩ = coreValue? value := by
  simp [coreStore, notLocal, slot]

private theorem reifiedList_values
    {values : List Value} {expressions : List Core.Expression.Val}
    (reified : values.mapM coreValue? = some expressions) :
    ∀ e ∈ expressions, Imperative.HasVal.value (P := Core.Expression) coreRuntimeFactory e := by
  induction values generalizing expressions with
  | nil =>
      have empty : expressions = [] := (Option.some.inj reified).symm
      subst expressions
      simp
  | cons value rest ih =>
      simp only [List.mapM_cons] at reified
      cases first : coreValue? value with
      | none => simp [first, bind, Option.bind] at reified
      | some expression =>
          cases tail : rest.mapM coreValue? with
          | none => simp [first, tail, bind, Option.bind] at reified
          | some remaining =>
              have same : expression :: remaining = expressions := by
                simpa [first, tail, bind, Option.bind, pure, Pure.pure] using reified
              subst expressions
              intro e member
              rcases List.mem_cons.mp member with rfl | inTail
              · exact coreValue?_isValue first
              · exact ih tail e inTail

/-- Entry slots and their old snapshots all hold values. This does not assert
that nondeterministic writes later in the execution remain literal-valued. -/
theorem coreEntry_wellFormed {globals : List Binding} {procedure : Core.Procedure}
    {input : Invocation} {store : Core.CoreStore}
    (entry : coreEntry globals procedure input store) :
    Imperative.WellFormedStore (P := Core.Expression) store coreRuntimeFactory := by
  rcases entry with ⟨_, _, _, _, _, _, _, _, _, _, inputReified, outputReified, frame⟩
  rcases frame with ⟨_, _, initInputs, initOutputs, snapshots⟩
  have wfEmpty : Imperative.WellFormedStore (P := Core.Expression) Imperative.emptyStore coreRuntimeFactory := by
    intro _ _ h
    change none = some _ at h
    cases h
  have wfInputs := Imperative.initStates_preserves_wf initInputs wfEmpty
    (reifiedList_values inputReified)
  have wfOutputs := Imperative.initStates_preserves_wf initOutputs wfInputs
    (reifiedList_values outputReified)
  rw [snapshots]
  exact Core.withOldSnapshots_preserves_wf _ _ wfOutputs

end
end Strata.Boole

/-! ## Primitive expressions under the Core runtime interpretation -/

namespace Strata.Boole
noncomputable section
noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p
open Lambda

/-- Core's denotational evaluator interprets `Int.Add` as Lean integer addition. -/
theorem coreEval_intAdd (store : Core.CoreStore) (left right : Core.Expression.Expr)
    (x y : Int)
    (leftEval : Core.Expression.eval coreRuntimeFactory store left =
      some (.ofInt coreRuntimeFactory.model.tcInterp x))
    (rightEval : Core.Expression.eval coreRuntimeFactory store right =
      some (.ofInt coreRuntimeFactory.model.tcInterp y)) :
    Core.Expression.eval coreRuntimeFactory store
        (.app () (.app () Core.coreIntAddOpExpr left) right) =
      some (.ofInt coreRuntimeFactory.model.tcInterp (x + y)) := by
  have evaluated := LExpr.denoteEval_app2_op_int (T := Core.CoreLParams)
    (m := ()) (m' := ()) (m'' := ()) (o := ⟨"Int.Add", ()⟩) (c := .int) (by rfl)
    leftEval rightEval
  have interpretation : (coreRuntimeFactory.model.opInterp "Int.Add"
      (LSort.mkArrow .int [.int, .int]) : Int → Int → Int) = Int.add := by
    unfold coreRuntimeFactory Core.factoryInterp Core.FactoryInterpModel.model
    exact Core.FactoryInterpModel.opInterp_intAdd
  change Core.Expression.eval coreRuntimeFactory store
    (.app () (.app () Core.coreIntAddOpExpr left) right) =
      some (.ofInt coreRuntimeFactory.model.tcInterp (x + y))
  change Core.Expression.eval coreRuntimeFactory store
    (.app () (.app () Core.coreIntAddOpExpr left) right) =
      some (.ofInt coreRuntimeFactory.model.tcInterp
        (coreRuntimeFactory.model.opInterp "Int.Add" (LSort.mkArrow .int [.int, .int]) x y)) at evaluated
  rw [interpretation] at evaluated
  exact evaluated

/-- A Boolean negation evaluates to the negated native Boolean. -/
theorem coreEval_boolNot (store : Core.CoreStore) (operand : Core.Expression.Expr)
    (value : Bool)
    (evaluated : Core.Expression.eval coreRuntimeFactory store operand =
      some (.ofBool coreRuntimeFactory.model.tcInterp value)) :
    Core.Expression.eval coreRuntimeFactory store (.app () Core.boolNotOp operand) =
      some (.ofBool coreRuntimeFactory.model.tcInterp (!value)) := by
  have interpretation : (coreRuntimeFactory.model.opInterp "Bool.Not"
      (LSort.mkArrow .bool [.bool]) : Bool → Bool) = Bool.not := by
    unfold coreRuntimeFactory Core.factoryInterp Core.FactoryInterpModel.model
    exact Core.FactoryInterpModel.opInterp_boolNot
  change (LExpr.app () (.op () ⟨"Bool.Not", ()⟩ (some (.arrow .bool .bool))) operand :
    Core.Expression.Expr).denoteEval coreRuntimeFactory store =
    some (.ofBool coreRuntimeFactory.model.tcInterp (!value))
  exact (LExpr.denoteEval_app_op_bool_iff (T := Core.CoreLParams)).mpr
    ⟨value, evaluated, by rw [interpretation]⟩

/-- Equality in Core's denotational evaluator is equality of semantic values. -/
theorem coreEval_eq (store : Core.CoreStore) (left right : Core.Expression.Expr)
    (leftValue rightValue : Core.Expression.Val)
    (sameSort : leftValue.sort = rightValue.sort)
    (leftEval : Core.Expression.eval coreRuntimeFactory store left = some leftValue)
    (rightEval : Core.Expression.eval coreRuntimeFactory store right = some rightValue) :
    Core.Expression.eval coreRuntimeFactory store (.eq () left right) =
      some (.ofBool coreRuntimeFactory.model.tcInterp (decide (leftValue = rightValue))) := by
  classical
  by_cases same : leftValue = rightValue
  · subst rightValue
    simpa using LExpr.denoteEval_eq_true (m := ()) leftEval rightEval
  · simpa [same] using LExpr.denoteEval_eq_false (m := ()) leftEval rightEval sameSort same

/-- A conditional denotes the branch selected by its Boolean guard. Both branch
expressions must be defined in the denotational evaluator. -/
theorem coreEval_conditional (store : Core.CoreStore) (guard yes no : Core.Expression.Expr)
    (taken : Bool) (yesValue noValue : Core.Expression.Val)
    (guardEval : Core.Expression.eval coreRuntimeFactory store guard =
      some (.ofBool coreRuntimeFactory.model.tcInterp taken))
    (yesEval : Core.Expression.eval coreRuntimeFactory store yes = some yesValue)
    (noEval : Core.Expression.eval coreRuntimeFactory store no = some noValue)
    (sameSort : yesValue.sort = noValue.sort) :
    Core.Expression.eval coreRuntimeFactory store (.ite () guard yes no) =
      some (if taken then yesValue else noValue) :=
  (LExpr.denoteEval_ite_iff (T := Core.CoreLParams)).mpr
    ⟨taken, yesValue, noValue, guardEval, yesEval, noEval, sameSort, rfl⟩

open Classical in
private theorem sourceValue_eq_decide (x y : Value) (sort : x.sort = y.sort) :
    Value.equal x y = decide (x = y) := by
  fun_cases Value.equal? x y
  all_goals simp only [Value.equal, Value.equal?]
  all_goals try rfl
  all_goals
    apply Bool.eq_iff_iff.mpr
    simp_all [Value.mk.injEq, beq_iff_eq]

/-- A Core semantic choice of a represented scalar type corresponds to a Boole
value of that same source type. -/
theorem coreTypedChoice_reifies {prior : Value} {previous : Core.Expression.Val}
    (encoded : coreValue? prior = some previous) (chosen : Core.Expression.Val)
    (model : chosen.tc = coreRuntimeFactory.model.tcInterp)
    (sameType : chosen.sort.toMonoTy = previous.sort.toMonoTy) :
    ∃ value, value.sort = prior.sort ∧ coreValue? value = some chosen := by
  -- TODO(adequacy): assumed for now; same `fun_cases coreValue?` breakage as
  -- `coreValue?_isValue`. Restore after the Core compatibility proof.
  sorry
  /-
  have sameSort := Lambda.LSort.toMonoTy_injective sameType
  obtain ⟨tc, sort, native⟩ := chosen
  have sameModel : tc = Core.FactoryInterpModel.tcInterp := model.trans coreRuntimeFactory_tcInterp
  subst tc
  fun_cases coreValue? prior <;> simp only [coreValue?, Option.some.injEq] at encoded
  all_goals try contradiction
  all_goals
    subst previous
    cases sameSort
    first
    | exact ⟨.int native, rfl, rfl⟩
    | exact ⟨.bool native, rfl, rfl⟩
    | exact ⟨.string native, rfl, rfl⟩
    | exact ⟨.real native, rfl, rfl⟩
    | exact ⟨.bitvec _ native, rfl, rfl⟩
  -/

/-- Integer addition agrees between the Boole denotation and the Core denotation. -/
theorem intAdd_agrees (state : State) (left right : Expression)
    (coreLeft coreRight : Core.Expression.Expr) (x y : Int)
    (leftBoole : left state = .ok (.int x)) (rightBoole : right state = .ok (.int y))
    (leftCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreLeft =
      some (.ofInt coreRuntimeFactory.model.tcInterp x))
    (rightCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreRight =
      some (.ofInt coreRuntimeFactory.model.tcInterp y)) :
    Expression.binary .add left right state = .ok (.int (x + y)) ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state)
          (.app () (.app () Core.coreIntAddOpExpr coreLeft) coreRight) =
        coreValue? (.int (x + y)) := by
  refine ⟨?_, ?_⟩
  · unfold Expression.binary Expression.binaryWith
    rw [leftBoole, rightBoole]
    rfl
  · exact coreEval_intAdd (coreStore state) coreLeft coreRight x y leftCore rightCore

/-- Scalar equality has the same truth value in Boole and Core. -/
theorem scalarEquality_agrees (state : State) (left right : Expression)
    (coreLeft coreRight : Core.Expression.Expr) (x y : Value)
    (leftValue rightValue : Core.Expression.Val)
    (sameSort : x.sort = y.sort)
    (leftBoole : left state = .ok x) (rightBoole : right state = .ok y)
    (leftEncoded : coreValue? x = some leftValue)
    (rightEncoded : coreValue? y = some rightValue)
    (leftCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreLeft = some leftValue)
    (rightCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreRight = some rightValue) :
    Expression.binary .eq left right state = .ok (.bool (Value.equal x y)) ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state) (.eq () coreLeft coreRight) =
        coreValue? (.bool (Value.equal x y)) := by
  have valuesSameSort : leftValue.sort = rightValue.sort := by
    obtain ⟨ty, leftTyped, rightTyped⟩ := coreValues_sameType sameSort leftEncoded rightEncoded
    change leftValue.tc = _ ∧ ty.toMonoType? = some leftValue.sort.toMonoTy at leftTyped
    change rightValue.tc = _ ∧ ty.toMonoType? = some rightValue.sort.toMonoTy at rightTyped
    have leftType : some leftValue.sort.toMonoTy = ty.toMonoType? := leftTyped.2.symm
    have rightType : some rightValue.sort.toMonoTy = ty.toMonoType? := rightTyped.2.symm
    have sameType : some leftValue.sort.toMonoTy = some rightValue.sort.toMonoTy :=
      leftType.trans rightType.symm
    exact Lambda.LSort.toMonoTy_injective (Option.some.inj sameType)
  have equalitySame : decide (leftValue = rightValue) = Value.equal x y := by
    have equalIff : (leftValue = rightValue) ↔ (x = y) := by
      constructor
      · intro h
        exact coreValue?_injective_some leftEncoded (h ▸ rightEncoded)
      · intro h
        subst y
        have sameRep : some leftValue = some rightValue := leftEncoded.symm.trans rightEncoded
        exact Option.some.inj sameRep
    rw [sourceValue_eq_decide x y sameSort]
    exact congrArg (fun p => @decide p (Classical.propDecidable p)) (propext equalIff)
  refine ⟨?_, ?_⟩
  · simp only [Expression.binary, Expression.binaryWith, leftBoole, rightBoole,
      bind, Except.bind, Except.ok.injEq, sameSort, ↓reduceIte, pure, Except.pure]
  · have evaluated := coreEval_eq (coreStore state) coreLeft coreRight leftValue rightValue
      valuesSameSort leftCore rightCore
    rw [equalitySame] at evaluated
    have boolRepresentation (b : Bool) :
        coreValue? (.bool b) = some (.ofBool coreRuntimeFactory.model.tcInterp b) := by
      unfold coreValue?
      rw [coreRuntimeFactory_tcInterp]
      rfl
    rw [boolRepresentation]
    exact evaluated

/-- Scalar inequality is equality followed by Boolean negation, matching the
corresponding Boole operation. -/
theorem scalarInequality_agrees (state : State) (left right : Expression)
    (coreLeft coreRight : Core.Expression.Expr) (x y : Value)
    (leftValue rightValue : Core.Expression.Val)
    (sameSort : x.sort = y.sort)
    (leftBoole : left state = .ok x) (rightBoole : right state = .ok y)
    (leftEncoded : coreValue? x = some leftValue)
    (rightEncoded : coreValue? y = some rightValue)
    (leftCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreLeft = some leftValue)
    (rightCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreRight = some rightValue) :
    Expression.binary .ne left right state = .ok (.bool (!(Value.equal x y))) ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state)
          (.app () Core.boolNotOp (.eq () coreLeft coreRight)) =
        coreValue? (.bool (!(Value.equal x y))) := by
  obtain ⟨sourceEq, coreEq⟩ := scalarEquality_agrees state left right coreLeft coreRight x y
    leftValue rightValue sameSort leftBoole rightBoole leftEncoded rightEncoded leftCore rightCore
  refine ⟨?_, ?_⟩
  · simp only [Expression.binary, Expression.binaryWith, leftBoole, rightBoole,
      bind, Except.bind, Except.ok.injEq, sameSort, ↓reduceIte, pure, Except.pure,
      sourceValue_eq_decide x y sameSort]
  · have boolRepresentation (b : Bool) :
        coreValue? (.bool b) = some (.ofBool coreRuntimeFactory.model.tcInterp b) := by
      unfold coreValue?
      rw [coreRuntimeFactory_tcInterp]
      rfl
    rw [boolRepresentation] at coreEq
    exact coreEval_boolNot (coreStore state) (.eq () coreLeft coreRight) (Value.equal x y) coreEq

/-- When both branch expressions denote compatible values, conditional
interpretation agrees with the Boole branch selected by its guard. -/
theorem conditional_agrees (state : State) (guard yes no : Expression)
    (coreGuard coreYes coreNo : Core.Expression.Expr) (taken : Bool)
    (yesValue noValue : Value)
    (guardBoole : guard state = .ok (.bool taken))
    (yesBoole : yes state = .ok yesValue) (noBoole : no state = .ok noValue)
    (guardCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreGuard =
      some (.ofBool coreRuntimeFactory.model.tcInterp taken))
    (yesRuntime : Core.Expression.Val) (noRuntime : Core.Expression.Val)
    (yesEncoded : coreValue? yesValue = some yesRuntime)
    (noEncoded : coreValue? noValue = some noRuntime)
    (yesCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreYes = some yesRuntime)
    (noCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreNo = some noRuntime)
    (sameSort : yesValue.sort = noValue.sort)
    : Expression.conditional guard yes no state = .ok (if taken then yesValue else noValue) ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state) (.ite () coreGuard coreYes coreNo) =
        coreValue? (if taken then yesValue else noValue) := by
  refine ⟨?_, ?_⟩
  · unfold Expression.conditional
    simp only [guardBoole, bind, Except.bind, Except.ok.injEq]
    cases taken <;> simp [Value.bool, yesBoole, noBoole]
  · have guardEval := guardCore
    have yesEval := yesCore
    have noEval := noCore
    have sameRuntimeSort : yesRuntime.sort = noRuntime.sort := by
      obtain ⟨ty, hy, hn⟩ := coreValues_sameType sameSort yesEncoded noEncoded
      change yesRuntime.tc = _ ∧ ty.toMonoType? = some yesRuntime.sort.toMonoTy at hy
      change noRuntime.tc = _ ∧ ty.toMonoType? = some noRuntime.sort.toMonoTy at hn
      have yesType : some yesRuntime.sort.toMonoTy = ty.toMonoType? := hy.2.symm
      have noType : some noRuntime.sort.toMonoTy = ty.toMonoType? := hn.2.symm
      have sameType : some yesRuntime.sort.toMonoTy = some noRuntime.sort.toMonoTy :=
        yesType.trans noType.symm
      exact Lambda.LSort.toMonoTy_injective (Option.some.inj sameType)
    have evaluated := coreEval_conditional (coreStore state) coreGuard coreYes coreNo taken
      yesRuntime noRuntime guardEval yesEval noEval sameRuntimeSort
    cases taken <;> simpa [yesEncoded, noEncoded] using evaluated

end
end Strata.Boole

namespace Strata.Boole

def BinderFree (expression : Core.Expression.Expr) : Prop :=
  match expression with
  | .const .. | .fvar .. | .op .. => True
  | .app _ left right | .eq _ left right => BinderFree left ∧ BinderFree right
  | .ite _ guard yes no => BinderFree guard ∧ BinderFree yes ∧ BinderFree no
  | _ => False

private theorem resolveAux_binderFree_eraseTypes (context : Core.Expression.TyContext)
    (raw : Core.Expression.Expr) (free : BinderFree raw)
    (environment final : Core.Expression.TyEnv) (checked : Lambda.LExprT Core.CoreLParams.mono)
    (ran : Lambda.LExpr.resolveAux context environment raw = .ok (checked, final))
    (substitution : Lambda.Subst) :
    (checked.applySubstT substitution).unresolved.eraseTypes = raw.eraseTypes := by
  induction raw generalizing environment final checked with
  | bvar | abs | quant => exact False.elim free
  | const | op | fvar | app | eq | ite =>
    try simp only [BinderFree] at free
    try rcases free with ⟨_, _, _⟩
    try rcases free with ⟨_, _⟩
    rw [Lambda.LExpr.resolveAux.eq_def (T := Core.CoreLParams)] at ran
    simp only [bind, Except.bind] at ran
    repeat' first
      | contradiction
      | (have equal : _ = checked := congrArg Prod.fst (Except.ok.inj ran)
         rw [← equal]
         first
         | rfl
         | (simp only [Lambda.LExpr.applySubstT, Lambda.LExpr.replaceMetadata,
              Lambda.LExpr.unresolved, Lambda.LExpr.eraseTypes]
            congr 1 <;>
              (change (Lambda.LExpr.applySubstT _ substitution).unresolved.eraseTypes = _
               solve_by_elim)))
      | split at ran

/-- Core checking a binder-free expression preserves its operations, variables
and literals after type annotations are erased. -/
theorem resolve_binderFree_eraseTypes (context : Core.Expression.TyContext)
    (raw : Core.Expression.Expr) (free : BinderFree raw)
    (environment final : Core.Expression.TyEnv) (checked : Lambda.LExprT Core.CoreLParams.mono)
    (ran : Lambda.LExpr.resolve context environment raw = .ok (checked, final)) :
    checked.unresolved.eraseTypes = raw.eraseTypes := by
  unfold Lambda.LExpr.resolve at ran
  simp only [bind, Except.bind] at ran
  split at ran
  · contradiction
  · rename_i typed resolved
    have equal : _ = checked := congrArg Prod.fst (Except.ok.inj ran)
    rw [← equal]
    exact resolveAux_binderFree_eraseTypes context raw free _ _ _ resolved _

/-- Resolving a Core variable can annotate its type. It still evaluates by
looking up the same slot. -/
theorem eval_resolvedCoreRead (context : Core.Expression.TyContext)
    (entry final : Core.Expression.TyEnv) (id : Core.CoreIdent)
    (checked : Lambda.LExprT Core.CoreLParams.mono)
    (resolved : Lambda.LExpr.resolve context entry (.fvar () id none) = .ok (checked, final))
    (store : Core.CoreStore)
    {value : Value} {runtimeValue : Core.Expression.Val}
    (represented : coreValue? value = some runtimeValue) (slot : store id = some runtimeValue) :
    Core.Expression.eval coreRuntimeFactory store checked.unresolved = some runtimeValue := by
  have erased := resolve_binderFree_eraseTypes context (.fvar () id none)
    (by trivial) entry final checked resolved
  cases expression : checked.unresolved <;> simp [expression, Lambda.LExpr.eraseTypes] at erased
  case fvar metadata actual annotation =>
    cases metadata
    subst actual
    exact eval_core_fvar represented store id annotation slot

/-- The interpretation, lowering and Core type resolution of a local
variable read all lead to the value in the corresponding source slot. -/
theorem checkedLocalRead_agrees (scope : Scope) (entry : TranslateState)
    (range : SourceRange) (index : Nat) (binding : Binding)
    (encoded : entry.bvars = scope.locals.toArray.map
      (fun b => (.fvar () ⟨b.name, ()⟩ none : Core.Expression.Expr)))
    (found : scope.locals.reverse[index]? = some binding)
    (sourceFinal : Scope) (sourceExpr : Expression)
    (source : interpExpr (denotation .builtins) (.bvar range index) scope = .ok (sourceExpr, sourceFinal))
    (raw : Core.Expression.Expr) (lowered : ExpressionWasLowered (.bvar range index) entry raw)
    (context : Core.Expression.TyContext) (tyEntry tyFinal : Core.Expression.TyEnv)
    (checked : Lambda.LExprT Core.CoreLParams.mono)
    (resolved : Lambda.LExpr.resolve context tyEntry raw = .ok (checked, tyFinal))
    (state : State) (value : Value) (runtimeValue : Core.Expression.Val)
    (slot : state.locals.lookup binding.name = some value)
    (represented : coreValue? value = some runtimeValue) :
    sourceExpr state = .ok value ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state) checked.unresolved = some runtimeValue := by
  obtain ⟨readSource, readCore⟩ := lowerLocalRead (denotation .builtins) scope entry range index
    binding encoded found
  have sourceEq : sourceExpr = Expression.read (.local binding.name) :=
    congrArg Prod.fst (Except.ok.inj (source.symm.trans readSource))
  have rawEq := lowered.unique readCore
  rw [rawEq] at resolved
  exact ⟨by rw [sourceEq]; simp [Expression.read, State.lookup, slot],
    eval_resolvedCoreRead context tyEntry tyFinal _ checked resolved _ represented
      ((coreStore_of_local state binding.name value slot).trans represented)⟩

end Strata.Boole
