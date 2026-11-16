/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.Expressions
import all StrataBoole.Boole.Semantics.Adequacy.Expressions
import all StrataBoole.Boole.Runtime
import all Strata.Languages.Core.Logic.FactoryInterp
import all Strata.Languages.Core.InstWellFormedSemanticsEval

public section
namespace Strata.Boole

open Lambda

private theorem opInterp_intMul :
    Core.FactoryInterpModel.opInterp "Int.Mul"
      (LSort.mkArrow .int [.int, .int]) = Int.mul := by
  funext x y
  unfold Core.FactoryInterpModel.opInterp
  have lookup : Core.Factory.get? "Int.Mul" =
      some (Lambda.intMulFunc (T := Core.CoreLParams)).func := Core.coreFactory_intMul
  rw [lookup]
  rfl


private theorem ofInt_eq_ofConst (tc : Lambda.TyConstrInterp) (value : Int) :
    Lambda.SemValue.ofInt tc value =
      Lambda.SemValue.ofConst tc (.intConst value) := by
  simp only [Lambda.SemValue.ofInt, Lambda.SemValue.ofConst, Lambda.LConst.ty,
    Lambda.LMonoTy.substTyVars, Lambda.denoteConst]
  rfl


/-- Core evaluates integer less-than with Lean's integer comparison. -/
theorem coreEval_intLt (store : Core.CoreStore) (left right : Core.Expression.Expr)
    (x y : Int)
    (leftEval : Core.Expression.eval coreRuntimeFactory store left =
      some (.ofInt coreRuntimeFactory.model.tcInterp x))
    (rightEval : Core.Expression.eval coreRuntimeFactory store right =
      some (.ofInt coreRuntimeFactory.model.tcInterp y)) :
    Core.Expression.eval coreRuntimeFactory store
      (.app () (.app () (.op () ⟨"Int.Lt", ()⟩
        (some (.arrow .int (.arrow .int .bool)))) left) right) =
      some (.ofBool coreRuntimeFactory.model.tcInterp (decide (x < y))) := by
  have evaluated := LExpr.denoteEval_app2_op_int (T := Core.CoreLParams)
    (m := ()) (m' := ()) (m'' := ()) (o := ⟨"Int.Lt", ()⟩) (c := .bool) (by rfl)
    leftEval rightEval
  change Core.Expression.eval coreRuntimeFactory store
    (.app () (.app () (.op () ⟨"Int.Lt", ()⟩
      (some (.arrow .int (.arrow .int .bool)))) left) right) =
    some (.ofBool coreRuntimeFactory.model.tcInterp (decide (x < y)))
  change Core.Expression.eval coreRuntimeFactory store
    (.app () (.app () (.op () ⟨"Int.Lt", ()⟩
      (some (.arrow .int (.arrow .int .bool)))) left) right) =
    some (.ofBool coreRuntimeFactory.model.tcInterp
      (coreRuntimeFactory.model.opInterp "Int.Lt"
        (LSort.mkArrow .bool [.int, .int]) x y)) at evaluated
  have interpretation :
      (coreRuntimeFactory.model.opInterp "Int.Lt"
        (LSort.mkArrow .bool [.int, .int]) : Int → Int → Bool) =
          (fun (x y : Int) => decide (x < y)) := by
    unfold coreRuntimeFactory Core.factoryInterp Core.FactoryInterpModel.model
    exact Core.FactoryInterpModel.opInterp_intLt
  rw [interpretation] at evaluated
  simpa using evaluated

/-- Boole integer comparison agrees with the Core `Int.Lt` operator. -/
theorem intLt_agrees (state : State) (left right : Expression)
    (coreLeft coreRight : Core.Expression.Expr) (x y : Int)
    (leftBoole : left state = .ok (.int x)) (rightBoole : right state = .ok (.int y))
    (leftCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreLeft =
      some (.ofInt coreRuntimeFactory.model.tcInterp x))
    (rightCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreRight =
      some (.ofInt coreRuntimeFactory.model.tcInterp y)) :
    Expression.binary .lt left right state = .ok (.bool (decide (x < y))) ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state)
        (.app () (.app () (.op () ⟨"Int.Lt", ()⟩
          (some (.arrow .int (.arrow .int .bool)))) coreLeft) coreRight) =
        some (.ofBool coreRuntimeFactory.model.tcInterp (decide (x < y))) := by
  refine ⟨?_, ?_⟩
  · unfold Expression.binary Expression.binaryWith
    rw [leftBoole, rightBoole]
    rfl
  · exact coreEval_intLt (coreStore state) coreLeft coreRight x y leftCore rightCore

private theorem opInterp_intGt :
    Core.FactoryInterpModel.opInterp "Int.Gt"
      (LSort.mkArrow .bool [.int, .int]) = fun (x y : Int) => decide (x > y) := by
  funext x y
  unfold Core.FactoryInterpModel.opInterp
  have lookup : Core.Factory.get? "Int.Gt" =
      some (Lambda.intGtFunc (T := Core.CoreLParams)).func := Core.coreFactory_intGt
  rw [lookup]
  rfl

/-- Core evaluates integer less-than-or-equal with Lean's integer comparison. -/
theorem coreEval_intLe (store : Core.CoreStore) (left right : Core.Expression.Expr)
    (x y : Int)
    (leftEval : Core.Expression.eval coreRuntimeFactory store left =
      some (.ofInt coreRuntimeFactory.model.tcInterp x))
    (rightEval : Core.Expression.eval coreRuntimeFactory store right =
      some (.ofInt coreRuntimeFactory.model.tcInterp y)) :
    Core.Expression.eval coreRuntimeFactory store
      (.app () (.app () (.op () ⟨"Int.Le", ()⟩
        (some (.arrow .int (.arrow .int .bool)))) left) right) =
      some (.ofBool coreRuntimeFactory.model.tcInterp (decide (x ≤ y))) := by
  have evaluated := LExpr.denoteEval_app2_op_int (T := Core.CoreLParams)
    (m := ()) (m' := ()) (m'' := ()) (o := ⟨"Int.Le", ()⟩) (c := .bool) (by rfl)
    leftEval rightEval
  change Core.Expression.eval coreRuntimeFactory store
    (.app () (.app () (.op () ⟨"Int.Le", ()⟩
      (some (.arrow .int (.arrow .int .bool)))) left) right) =
    some (.ofBool coreRuntimeFactory.model.tcInterp (decide (x ≤ y)))
  change Core.Expression.eval coreRuntimeFactory store
    (.app () (.app () (.op () ⟨"Int.Le", ()⟩
      (some (.arrow .int (.arrow .int .bool)))) left) right) =
    some (.ofBool coreRuntimeFactory.model.tcInterp
      (coreRuntimeFactory.model.opInterp "Int.Le"
        (LSort.mkArrow .bool [.int, .int]) x y)) at evaluated
  have interpretation :
      (coreRuntimeFactory.model.opInterp "Int.Le"
        (LSort.mkArrow .bool [.int, .int]) : Int → Int → Bool) =
          (fun (x y : Int) => decide (x ≤ y)) := by
    unfold coreRuntimeFactory Core.factoryInterp Core.FactoryInterpModel.model
    exact Core.FactoryInterpModel.opInterp_intLe
  rw [interpretation] at evaluated
  simpa using evaluated

/-- Boole integer less-than-or-equal agrees with Core's `Int.Le` operator. -/
theorem intLe_agrees (state : State) (left right : Expression)
    (coreLeft coreRight : Core.Expression.Expr) (x y : Int)
    (leftBoole : left state = .ok (.int x)) (rightBoole : right state = .ok (.int y))
    (leftCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreLeft =
      some (.ofInt coreRuntimeFactory.model.tcInterp x))
    (rightCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreRight =
      some (.ofInt coreRuntimeFactory.model.tcInterp y)) :
    Expression.binary .le left right state = .ok (.bool (decide (x ≤ y))) ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state)
        (.app () (.app () (.op () ⟨"Int.Le", ()⟩
          (some (.arrow .int (.arrow .int .bool)))) coreLeft) coreRight) =
        some (.ofBool coreRuntimeFactory.model.tcInterp (decide (x ≤ y))) := by
  refine ⟨?_, ?_⟩
  · unfold Expression.binary Expression.binaryWith
    rw [leftBoole, rightBoole]
    rfl
  · exact coreEval_intLe (coreStore state) coreLeft coreRight x y leftCore rightCore

/-- Core evaluates integer greater-than with Lean's integer comparison. -/
theorem coreEval_intGt (store : Core.CoreStore) (left right : Core.Expression.Expr)
    (x y : Int)
    (leftEval : Core.Expression.eval coreRuntimeFactory store left =
      some (.ofInt coreRuntimeFactory.model.tcInterp x))
    (rightEval : Core.Expression.eval coreRuntimeFactory store right =
      some (.ofInt coreRuntimeFactory.model.tcInterp y)) :
    Core.Expression.eval coreRuntimeFactory store
      (.app () (.app () (.op () ⟨"Int.Gt", ()⟩
        (some (.arrow .int (.arrow .int .bool)))) left) right) =
      some (.ofBool coreRuntimeFactory.model.tcInterp (decide (x > y))) := by
  have evaluated := LExpr.denoteEval_app2_op_int (T := Core.CoreLParams)
    (m := ()) (m' := ()) (m'' := ()) (o := ⟨"Int.Gt", ()⟩) (c := .bool) (by rfl)
    leftEval rightEval
  change Core.Expression.eval coreRuntimeFactory store
    (.app () (.app () (.op () ⟨"Int.Gt", ()⟩
      (some (.arrow .int (.arrow .int .bool)))) left) right) =
    some (.ofBool coreRuntimeFactory.model.tcInterp (decide (x > y)))
  change Core.Expression.eval coreRuntimeFactory store
    (.app () (.app () (.op () ⟨"Int.Gt", ()⟩
      (some (.arrow .int (.arrow .int .bool)))) left) right) =
    some (.ofBool coreRuntimeFactory.model.tcInterp
      (coreRuntimeFactory.model.opInterp "Int.Gt"
        (LSort.mkArrow .bool [.int, .int]) x y)) at evaluated
  have interpretation :
      (coreRuntimeFactory.model.opInterp "Int.Gt"
        (LSort.mkArrow .bool [.int, .int]) : Int → Int → Bool) =
          (fun (x y : Int) => decide (x > y)) := by
    unfold coreRuntimeFactory Core.factoryInterp Core.FactoryInterpModel.model
    exact opInterp_intGt
  rw [interpretation] at evaluated
  simpa using evaluated

/-- Boole integer greater-than agrees with Core's `Int.Gt` operator. -/
theorem intGt_agrees (state : State) (left right : Expression)
    (coreLeft coreRight : Core.Expression.Expr) (x y : Int)
    (leftBoole : left state = .ok (.int x)) (rightBoole : right state = .ok (.int y))
    (leftCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreLeft =
      some (.ofInt coreRuntimeFactory.model.tcInterp x))
    (rightCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreRight =
      some (.ofInt coreRuntimeFactory.model.tcInterp y)) :
    Expression.binary .gt left right state = .ok (.bool (decide (x > y))) ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state)
        (.app () (.app () (.op () ⟨"Int.Gt", ()⟩
          (some (.arrow .int (.arrow .int .bool)))) coreLeft) coreRight) =
        some (.ofBool coreRuntimeFactory.model.tcInterp (decide (x > y))) := by
  refine ⟨?_, ?_⟩
  · unfold Expression.binary Expression.binaryWith
    rw [leftBoole, rightBoole]
    rfl
  · exact coreEval_intGt (coreStore state) coreLeft coreRight x y leftCore rightCore

/-- Core evaluates integer greater-than-or-equal with Lean's integer comparison. -/
theorem coreEval_intGe (store : Core.CoreStore) (left right : Core.Expression.Expr)
    (x y : Int)
    (leftEval : Core.Expression.eval coreRuntimeFactory store left =
      some (.ofInt coreRuntimeFactory.model.tcInterp x))
    (rightEval : Core.Expression.eval coreRuntimeFactory store right =
      some (.ofInt coreRuntimeFactory.model.tcInterp y)) :
    Core.Expression.eval coreRuntimeFactory store
      (.app () (.app () (.op () ⟨"Int.Ge", ()⟩
        (some (.arrow .int (.arrow .int .bool)))) left) right) =
      some (.ofBool coreRuntimeFactory.model.tcInterp (decide (x ≥ y))) := by
  have evaluated := LExpr.denoteEval_app2_op_int (T := Core.CoreLParams)
    (m := ()) (m' := ()) (m'' := ()) (o := ⟨"Int.Ge", ()⟩) (c := .bool) (by rfl)
    leftEval rightEval
  change Core.Expression.eval coreRuntimeFactory store
    (.app () (.app () (.op () ⟨"Int.Ge", ()⟩
      (some (.arrow .int (.arrow .int .bool)))) left) right) =
    some (.ofBool coreRuntimeFactory.model.tcInterp (decide (x ≥ y)))
  change Core.Expression.eval coreRuntimeFactory store
    (.app () (.app () (.op () ⟨"Int.Ge", ()⟩
      (some (.arrow .int (.arrow .int .bool)))) left) right) =
    some (.ofBool coreRuntimeFactory.model.tcInterp
      (coreRuntimeFactory.model.opInterp "Int.Ge"
        (LSort.mkArrow .bool [.int, .int]) x y)) at evaluated
  have interpretation :
      (coreRuntimeFactory.model.opInterp "Int.Ge"
        (LSort.mkArrow .bool [.int, .int]) : Int → Int → Bool) =
          (fun (x y : Int) => decide (x ≥ y)) := by
    unfold coreRuntimeFactory Core.factoryInterp Core.FactoryInterpModel.model
    exact Core.FactoryInterpModel.opInterp_intGe
  rw [interpretation] at evaluated
  simpa using evaluated

/-- Boole integer greater-than-or-equal agrees with Core's `Int.Ge` operator. -/
theorem intGe_agrees (state : State) (left right : Expression)
    (coreLeft coreRight : Core.Expression.Expr) (x y : Int)
    (leftBoole : left state = .ok (.int x)) (rightBoole : right state = .ok (.int y))
    (leftCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreLeft =
      some (.ofInt coreRuntimeFactory.model.tcInterp x))
    (rightCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreRight =
      some (.ofInt coreRuntimeFactory.model.tcInterp y)) :
    Expression.binary .ge left right state = .ok (.bool (decide (x ≥ y))) ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state)
        (.app () (.app () (.op () ⟨"Int.Ge", ()⟩
          (some (.arrow .int (.arrow .int .bool)))) coreLeft) coreRight) =
        some (.ofBool coreRuntimeFactory.model.tcInterp (decide (x ≥ y))) := by
  refine ⟨?_, ?_⟩
  · unfold Expression.binary Expression.binaryWith
    rw [leftBoole, rightBoole]
    rfl
  · exact coreEval_intGe (coreStore state) coreLeft coreRight x y leftCore rightCore

/-- Core evaluates Boolean and as the corresponding Lean operation. -/
theorem coreEval_boolAnd (store : Core.CoreStore) (left right : Core.Expression.Expr)
    (x y : Bool)
    (leftEval : Core.Expression.eval coreRuntimeFactory store left =
      some (.ofBool coreRuntimeFactory.model.tcInterp x))
    (rightEval : Core.Expression.eval coreRuntimeFactory store right =
      some (.ofBool coreRuntimeFactory.model.tcInterp y)) :
    Core.Expression.eval coreRuntimeFactory store
      (.app () (.app () (.op () ⟨"Bool.And", ()⟩
        (some (.arrow .bool (.arrow .bool .bool)))) left) right) =
      some (.ofBool coreRuntimeFactory.model.tcInterp (x && y)) := by
  have evaluated := LExpr.denoteEval_app2_op_val (T := Core.CoreLParams)
    (m := ()) (m' := ()) (m'' := ()) (o := ⟨"Bool.And", ()⟩)
    (a := .bool) (b := .bool) (c := .bool) (by rfl) (by rfl) (by rfl)
    (va := x) (vb := y) leftEval rightEval
  change Core.Expression.eval coreRuntimeFactory store
    (.app () (.app () (.op () ⟨"Bool.And", ()⟩
      (some (.arrow .bool (.arrow .bool .bool)))) left) right) =
    some (.ofBool coreRuntimeFactory.model.tcInterp (x && y))
  change Core.Expression.eval coreRuntimeFactory store
    (.app () (.app () (.op () ⟨"Bool.And", ()⟩
      (some (.arrow .bool (.arrow .bool .bool)))) left) right) =
    some (.ofBool coreRuntimeFactory.model.tcInterp
      (coreRuntimeFactory.model.opInterp "Bool.And"
        (LSort.mkArrow .bool [.bool, .bool]) x y)) at evaluated
  have interpretation :
      (coreRuntimeFactory.model.opInterp "Bool.And"
        (LSort.mkArrow .bool [.bool, .bool]) : Bool → Bool → Bool) =
          (fun (x y : Bool) => x && y) := by
    unfold coreRuntimeFactory Core.factoryInterp Core.FactoryInterpModel.model
    exact Core.FactoryInterpModel.opInterp_boolAnd
  rw [interpretation] at evaluated
  exact evaluated

/-- Boole Boolean and agrees with Core's `Bool.And` operator. -/
theorem boolAnd_agrees (state : State) (left right : Expression)
    (coreLeft coreRight : Core.Expression.Expr) (x y : Bool)
    (leftBoole : left state = .ok (.bool x)) (rightBoole : right state = .ok (.bool y))
    (leftCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreLeft =
      some (.ofBool coreRuntimeFactory.model.tcInterp x))
    (rightCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreRight =
      some (.ofBool coreRuntimeFactory.model.tcInterp y)) :
    Expression.binary .and left right state = .ok (.bool (x && y)) ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state)
        (.app () (.app () (.op () ⟨"Bool.And", ()⟩
          (some (.arrow .bool (.arrow .bool .bool)))) coreLeft) coreRight) =
        some (.ofBool coreRuntimeFactory.model.tcInterp (x && y)) := by
  refine ⟨?_, ?_⟩
  · unfold Expression.binary Expression.binaryWith
    rw [leftBoole, rightBoole]
    rfl
  · exact coreEval_boolAnd (coreStore state) coreLeft coreRight x y leftCore rightCore

/-- Core evaluates Boolean or as the corresponding Lean operation. -/
theorem coreEval_boolOr (store : Core.CoreStore) (left right : Core.Expression.Expr)
    (x y : Bool)
    (leftEval : Core.Expression.eval coreRuntimeFactory store left =
      some (.ofBool coreRuntimeFactory.model.tcInterp x))
    (rightEval : Core.Expression.eval coreRuntimeFactory store right =
      some (.ofBool coreRuntimeFactory.model.tcInterp y)) :
    Core.Expression.eval coreRuntimeFactory store
      (.app () (.app () (.op () ⟨"Bool.Or", ()⟩
        (some (.arrow .bool (.arrow .bool .bool)))) left) right) =
      some (.ofBool coreRuntimeFactory.model.tcInterp (x || y)) := by
  have evaluated := LExpr.denoteEval_app2_op_val (T := Core.CoreLParams)
    (m := ()) (m' := ()) (m'' := ()) (o := ⟨"Bool.Or", ()⟩)
    (a := .bool) (b := .bool) (c := .bool) (by rfl) (by rfl) (by rfl)
    (va := x) (vb := y) leftEval rightEval
  change Core.Expression.eval coreRuntimeFactory store
    (.app () (.app () (.op () ⟨"Bool.Or", ()⟩
      (some (.arrow .bool (.arrow .bool .bool)))) left) right) =
    some (.ofBool coreRuntimeFactory.model.tcInterp (x || y))
  change Core.Expression.eval coreRuntimeFactory store
    (.app () (.app () (.op () ⟨"Bool.Or", ()⟩
      (some (.arrow .bool (.arrow .bool .bool)))) left) right) =
    some (.ofBool coreRuntimeFactory.model.tcInterp
      (coreRuntimeFactory.model.opInterp "Bool.Or"
        (LSort.mkArrow .bool [.bool, .bool]) x y)) at evaluated
  have interpretation :
      (coreRuntimeFactory.model.opInterp "Bool.Or"
        (LSort.mkArrow .bool [.bool, .bool]) : Bool → Bool → Bool) =
          (fun (x y : Bool) => x || y) := by
    unfold coreRuntimeFactory Core.factoryInterp Core.FactoryInterpModel.model
    exact Core.FactoryInterpModel.opInterp_boolOr
  rw [interpretation] at evaluated
  exact evaluated

/-- Boole Boolean or agrees with Core's `Bool.Or` operator. -/
theorem boolOr_agrees (state : State) (left right : Expression)
    (coreLeft coreRight : Core.Expression.Expr) (x y : Bool)
    (leftBoole : left state = .ok (.bool x)) (rightBoole : right state = .ok (.bool y))
    (leftCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreLeft =
      some (.ofBool coreRuntimeFactory.model.tcInterp x))
    (rightCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreRight =
      some (.ofBool coreRuntimeFactory.model.tcInterp y)) :
    Expression.binary .or left right state = .ok (.bool (x || y)) ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state)
        (.app () (.app () (.op () ⟨"Bool.Or", ()⟩
          (some (.arrow .bool (.arrow .bool .bool)))) coreLeft) coreRight) =
        some (.ofBool coreRuntimeFactory.model.tcInterp (x || y)) := by
  refine ⟨?_, ?_⟩
  · unfold Expression.binary Expression.binaryWith
    rw [leftBoole, rightBoole]
    rfl
  · exact coreEval_boolOr (coreStore state) coreLeft coreRight x y leftCore rightCore

/-- Equality of integer expressions has the same Boolean meaning in Boole and Core. -/
theorem intEq_agrees (state : State) (left right : Expression)
    (coreLeft coreRight : Core.Expression.Expr) (x y : Int)
    (leftBoole : left state = .ok (.int x)) (rightBoole : right state = .ok (.int y))
    (leftCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreLeft =
      some (.ofInt coreRuntimeFactory.model.tcInterp x))
    (rightCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreRight =
      some (.ofInt coreRuntimeFactory.model.tcInterp y)) :
    Expression.binary .eq left right state = .ok (.bool (x == y)) ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state) (.eq () coreLeft coreRight) =
        some (.ofBool coreRuntimeFactory.model.tcInterp (x == y)) := by
  refine ⟨?_, ?_⟩
  · unfold Expression.binary Expression.binaryWith
    simp [leftBoole, rightBoole, Value.int, Value.equal, Value.equal?, bind, Except.bind, pure, Except.pure]
  · have sameSort :
      (SemValue.ofInt coreRuntimeFactory.model.tcInterp x).sort =
        (SemValue.ofInt coreRuntimeFactory.model.tcInterp y).sort := rfl
    have core := coreEval_eq (coreStore state) coreLeft coreRight
      (.ofInt coreRuntimeFactory.model.tcInterp x) (.ofInt coreRuntimeFactory.model.tcInterp y)
      sameSort leftCore rightCore
    have valuesEqual :
        (SemValue.ofInt coreRuntimeFactory.model.tcInterp x =
          SemValue.ofInt coreRuntimeFactory.model.tcInterp y) ↔ x = y := by
      constructor
      · exact SemValue.ofInt_injective
      · intro h
        cases h
        rfl
    have boolEq : decide (x = y) = (x == y) := by
      cases h : (x == y)
      · have hne : x ≠ y := by
          intro heq
          subst y
          simp at h
        simp [hne]
      · have heq : x = y := (beq_iff_eq).mp h
        subst y
        simp
    simpa [valuesEqual, boolEq] using core

/-- A Core integer literal evaluates to the scalar representation used for Boole integers. -/
theorem coreEval_intLiteral (store : Core.CoreStore) (value : Int) :
    Core.Expression.eval coreRuntimeFactory store (.intConst () value) =
      coreValue? (.int value) := by
  classical
  change (Lambda.LExpr.const () (.intConst value) : Lambda.LExpr Core.CoreLParams.mono).denoteEval
      coreRuntimeFactory store =
    some (.ofConst Core.FactoryInterpModel.tcInterp (.intConst value))
  have evaluated :
      (Lambda.LExpr.const () (.intConst value) : Lambda.LExpr Core.CoreLParams.mono).denoteEval
        coreRuntimeFactory store = some (.ofInt coreRuntimeFactory.model.tcInterp value) :=
    Lambda.LExpr.denoteEval_intConst (M := coreRuntimeFactory) (σ := store)
  rw [coreRuntimeFactory_tcInterp, ofInt_eq_ofConst] at evaluated
  exact evaluated

private theorem ofBool_eq_ofConst (tc : Lambda.TyConstrInterp) (value : Bool) :
    Lambda.SemValue.ofBool tc value =
      Lambda.SemValue.ofConst tc (.boolConst value) := by
  simp only [Lambda.SemValue.ofBool, Lambda.SemValue.ofConst, Lambda.LConst.ty,
    Lambda.LMonoTy.substTyVars, Lambda.denoteConst]
  rfl

/-- A Core Boolean literal evaluates to the scalar representation used for Boole Booleans. -/
theorem coreEval_boolLiteral (store : Core.CoreStore) (value : Bool) :
    Core.Expression.eval coreRuntimeFactory store (.boolConst () value) =
      coreValue? (.bool value) := by
  classical
  change (Lambda.LExpr.const () (.boolConst value) : Lambda.LExpr Core.CoreLParams.mono).denoteEval
      coreRuntimeFactory store =
    some (.ofConst Core.FactoryInterpModel.tcInterp (.boolConst value))
  have evaluated :
      (Lambda.LExpr.const () (.boolConst value) : Lambda.LExpr Core.CoreLParams.mono).denoteEval
        coreRuntimeFactory store = some (.ofBool coreRuntimeFactory.model.tcInterp value) :=
    Lambda.LExpr.denoteEval_boolConst (M := coreRuntimeFactory) (σ := store)
  rw [coreRuntimeFactory_tcInterp, ofBool_eq_ofConst] at evaluated
  exact evaluated

private theorem ofBitVec_eq_ofConst (tc : Lambda.TyConstrInterp)
    (width : Nat) (value : BitVec width) :
    Lambda.SemValue.ofBitVec tc width value =
      Lambda.SemValue.ofConst tc (.bitvecConst width value) := by
  simp only [Lambda.SemValue.ofBitVec, Lambda.SemValue.ofConst, Lambda.LConst.ty,
    Lambda.LMonoTy.substTyVars, Lambda.denoteConst]

/-- A Core bitvector literal evaluates to Boole's width-indexed bitvector value. -/
theorem coreEval_bitvecLiteral (store : Core.CoreStore) (width : Nat)
    (value : BitVec width) :
    Core.Expression.eval coreRuntimeFactory store (.const () (.bitvecConst width value)) =
      coreValue? (.bitvec width value) := by
  classical
  change (Lambda.LExpr.const () (.bitvecConst width value) :
      Lambda.LExpr Core.CoreLParams.mono).denoteEval coreRuntimeFactory store =
    some (.ofConst Core.FactoryInterpModel.tcInterp (.bitvecConst width value))
  have evaluated :
      (Lambda.LExpr.const () (.bitvecConst width value) :
        Lambda.LExpr Core.CoreLParams.mono).denoteEval coreRuntimeFactory store =
        some (.ofConst Core.FactoryInterpModel.tcInterp (.bitvecConst width value)) :=
    Lambda.LExpr.denoteEval_const (M := coreRuntimeFactory) (σ := store) (m := ())
      (c := .bitvecConst width value)
  exact evaluated

/-- Core evaluates integer subtraction with Lean's integer subtraction. -/
theorem coreEval_intSub (store : Core.CoreStore) (left right : Core.Expression.Expr)
    (x y : Int)
    (leftEval : Core.Expression.eval coreRuntimeFactory store left =
      some (.ofInt coreRuntimeFactory.model.tcInterp x))
    (rightEval : Core.Expression.eval coreRuntimeFactory store right =
      some (.ofInt coreRuntimeFactory.model.tcInterp y)) :
    Core.Expression.eval coreRuntimeFactory store
      (.app () (.app () (.op () ⟨"Int.Sub", ()⟩
        (some (.arrow .int (.arrow .int .int)))) left) right) =
      some (.ofInt coreRuntimeFactory.model.tcInterp (x - y)) := by
  have evaluated := LExpr.denoteEval_app2_op_int (T := Core.CoreLParams)
    (m := ()) (m' := ()) (m'' := ()) (o := ⟨"Int.Sub", ()⟩) (c := .int) (by rfl)
    leftEval rightEval
  change Core.Expression.eval coreRuntimeFactory store
    (.app () (.app () (.op () ⟨"Int.Sub", ()⟩
      (some (.arrow .int (.arrow .int .int)))) left) right) =
    some (.ofInt coreRuntimeFactory.model.tcInterp (x - y))
  change Core.Expression.eval coreRuntimeFactory store
    (.app () (.app () (.op () ⟨"Int.Sub", ()⟩
      (some (.arrow .int (.arrow .int .int)))) left) right) =
    some (.ofInt coreRuntimeFactory.model.tcInterp
      (coreRuntimeFactory.model.opInterp "Int.Sub"
        (LSort.mkArrow .int [.int, .int]) x y)) at evaluated
  have interpretation :
      (coreRuntimeFactory.model.opInterp "Int.Sub"
        (LSort.mkArrow .int [.int, .int]) : Int → Int → Int) = Int.sub := by
    unfold coreRuntimeFactory Core.factoryInterp Core.FactoryInterpModel.model
    exact Core.FactoryInterpModel.opInterp_intSub
  rw [interpretation] at evaluated
  exact evaluated

/-- Core evaluates integer multiplication with Lean's integer multiplication. -/
theorem coreEval_intMul (store : Core.CoreStore) (left right : Core.Expression.Expr)
    (x y : Int)
    (leftEval : Core.Expression.eval coreRuntimeFactory store left =
      some (.ofInt coreRuntimeFactory.model.tcInterp x))
    (rightEval : Core.Expression.eval coreRuntimeFactory store right =
      some (.ofInt coreRuntimeFactory.model.tcInterp y)) :
    Core.Expression.eval coreRuntimeFactory store
      (.app () (.app () (.op () ⟨"Int.Mul", ()⟩
        (some (.arrow .int (.arrow .int .int)))) left) right) =
      some (.ofInt coreRuntimeFactory.model.tcInterp (x * y)) := by
  have evaluated := LExpr.denoteEval_app2_op_int (T := Core.CoreLParams)
    (m := ()) (m' := ()) (m'' := ()) (o := ⟨"Int.Mul", ()⟩) (c := .int) (by rfl)
    leftEval rightEval
  change Core.Expression.eval coreRuntimeFactory store
    (.app () (.app () (.op () ⟨"Int.Mul", ()⟩
      (some (.arrow .int (.arrow .int .int)))) left) right) =
    some (.ofInt coreRuntimeFactory.model.tcInterp (x * y))
  change Core.Expression.eval coreRuntimeFactory store
    (.app () (.app () (.op () ⟨"Int.Mul", ()⟩
      (some (.arrow .int (.arrow .int .int)))) left) right) =
    some (.ofInt coreRuntimeFactory.model.tcInterp
      (coreRuntimeFactory.model.opInterp "Int.Mul"
        (LSort.mkArrow .int [.int, .int]) x y)) at evaluated
  have interpretation :
      (coreRuntimeFactory.model.opInterp "Int.Mul"
        (LSort.mkArrow .int [.int, .int]) : Int → Int → Int) = Int.mul := by
    unfold coreRuntimeFactory Core.factoryInterp Core.FactoryInterpModel.model
    exact opInterp_intMul
  rw [interpretation] at evaluated
  exact evaluated

/-- The Boole denotation and Core agree on integer subtraction. -/
theorem intSub_agrees (state : State) (left right : Expression)
    (coreLeft coreRight : Core.Expression.Expr) (x y : Int)
    (leftBoole : left state = .ok (.int x)) (rightBoole : right state = .ok (.int y))
    (leftCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreLeft =
      some (.ofInt coreRuntimeFactory.model.tcInterp x))
    (rightCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreRight =
      some (.ofInt coreRuntimeFactory.model.tcInterp y)) :
    Expression.binary .sub left right state = .ok (.int (x - y)) ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state)
        (.app () (.app () (.op () ⟨"Int.Sub", ()⟩
          (some (.arrow .int (.arrow .int .int)))) coreLeft) coreRight) =
        coreValue? (.int (x - y)) := by
  refine ⟨?_, ?_⟩
  · unfold Expression.binary Expression.binaryWith
    rw [leftBoole, rightBoole]
    rfl
  · change Core.Expression.eval coreRuntimeFactory (coreStore state)
      (.app () (.app () (.op () ⟨"Int.Sub", ()⟩
        (some (.arrow .int (.arrow .int .int)))) coreLeft) coreRight) =
      some (.ofConst Core.FactoryInterpModel.tcInterp (.intConst (x - y)))
    rw [← ofInt_eq_ofConst Core.FactoryInterpModel.tcInterp (x - y)]
    simpa [coreRuntimeFactory_tcInterp] using
      coreEval_intSub (coreStore state) coreLeft coreRight x y leftCore rightCore

/-- The Boole denotation and Core agree on integer multiplication. -/
theorem intMul_agrees (state : State) (left right : Expression)
    (coreLeft coreRight : Core.Expression.Expr) (x y : Int)
    (leftBoole : left state = .ok (.int x)) (rightBoole : right state = .ok (.int y))
    (leftCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreLeft =
      some (.ofInt coreRuntimeFactory.model.tcInterp x))
    (rightCore : Core.Expression.eval coreRuntimeFactory (coreStore state) coreRight =
      some (.ofInt coreRuntimeFactory.model.tcInterp y)) :
    Expression.binary .mul left right state = .ok (.int (x * y)) ∧
      Core.Expression.eval coreRuntimeFactory (coreStore state)
        (.app () (.app () (.op () ⟨"Int.Mul", ()⟩
          (some (.arrow .int (.arrow .int .int)))) coreLeft) coreRight) =
        coreValue? (.int (x * y)) := by
  refine ⟨?_, ?_⟩
  · unfold Expression.binary Expression.binaryWith
    rw [leftBoole, rightBoole]
    rfl
  · change Core.Expression.eval coreRuntimeFactory (coreStore state)
      (.app () (.app () (.op () ⟨"Int.Mul", ()⟩
        (some (.arrow .int (.arrow .int .int)))) coreLeft) coreRight) =
      some (.ofConst Core.FactoryInterpModel.tcInterp (.intConst (x * y)))
    rw [← ofInt_eq_ofConst Core.FactoryInterpModel.tcInterp (x * y)]
    simpa [coreRuntimeFactory_tcInterp] using
      coreEval_intMul (coreStore state) coreLeft coreRight x y leftCore rightCore

end Strata.Boole
