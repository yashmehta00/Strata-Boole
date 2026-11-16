/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.Boole.Hoare.Compatibility
import StrataBoole.Boole.Hoare.Reflect
import StrataBooleTest.hoare_max2

/-! The Boole certificate supplies the arithmetic facts in the Core triple.
The Core lemmas from `hoare_max2` supply the executable and denotational
interpretations of the same expressions. -/

namespace HoareMax2

open Strata Strata.Boole.Hoare Lambda

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option mvcgen.warning false

private theorem native_post
    (certificate : VerifiedSource (boole% max2Pgm) "max2") (x y : Int) :
    let r := if y ≤ x then x else y
    x ≤ r ∧ y ≤ r ∧ (r = x ∨ r = y) := by
  obtain ⟨prepared, compiled, valid⟩ := verifiedSource_iff.mp certificate
  cbv at compiled
  cases compiled
  simp only [Prepared.Valid, forValues] at valid
  have checked := (valid x y (0 : Int) True.intro).le_wp _ rfl
  clear valid certificate
  boole_lift at checked
  by_cases guard : y ≤ x <;> simp [Obligation, guard] at checked ⊢ <;> exact checked

/-- Transfer a certificate for the same source that Lydia lowered. -/
theorem max2_certificate_transfers
    (certificate : VerifiedSource (boole% max2Pgm) "max2") :
    Core.Logic.Hoare.Procedure.contractTriple max2Core params "max2" := by
  have certified := native_post certificate
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core_typed max2Core params "max2" max2Proc _
    max2_findProc max2_body_eq max2_checksTyped (fun model => ?_)
  refine (Core.Logic.Hoare.block max2Core.findProcByString? params ?_
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide))) model
  refine Core.Logic.Hoare.block max2Core.findProcByString? params ?_
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide))
  refine Core.Logic.Hoare.ite max2Core.findProcByString? params ?_ ?_
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide))
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide))
  · refine set_int_var _ rV xV intTy md1 _ _ ?_ ?_
    · intro ρ ⟨pre, _⟩
      obtain ⟨_, x, _, hx, _⟩ := max2_pre_ints model ρ pre
      exact ⟨x, hx⟩
    · intro ρ store x ⟨pre, condition⟩ assigned result frame
      obtain ⟨factory, a, b, ha, hb⟩ := max2_pre_ints model ρ pre
      have same : a = x := by rw [ha] at assigned; simpa [LExpr.intConst] using assigned
      subst x
      rw [factory, show Core.Expression.eval = LExpr.evalFully (TBase := Core.CoreLParams) from rfl,
        HoareLift.evalFully_intGe_store _ _ _ _ _ a b ha hb] at condition
      have guard : b ≤ a := by
        have tt : (Imperative.HasBool.tt : Core.Expression.Expr) = .const () (.boolConst true) := rfl
        simpa [tt, LExpr.boolConst] using condition
      have facts : a ≤ a ∧ b ≤ a ∧ (a = a ∨ a = b) := by
        simpa only [guard, ↓reduceIte] using certified a b
      exact max2_post model _ a b a factory (by simpa [frame xV (by decide)] using ha)
        (by simpa [frame yV (by decide)] using hb) result facts.1 facts.2.1 facts.2.2
  · refine set_int_var _ rV yV intTy md2 _ _ ?_ ?_
    · intro ρ ⟨pre, _⟩
      obtain ⟨_, _, y, _, hy⟩ := max2_pre_ints model ρ pre
      exact ⟨y, hy⟩
    · intro ρ store y ⟨pre, condition⟩ assigned result frame
      obtain ⟨factory, a, b, ha, hb⟩ := max2_pre_ints model ρ pre
      have same : b = y := by rw [hb] at assigned; simpa [LExpr.intConst] using assigned
      subst y
      rw [factory, show Core.Expression.eval = LExpr.evalFully (TBase := Core.CoreLParams) from rfl,
        HoareLift.evalFully_intGe_store _ _ _ _ _ a b ha hb] at condition
      have guard : ¬ b ≤ a := by
        have ff : (Imperative.HasBool.ff : Core.Expression.Expr) = .const () (.boolConst false) := rfl
        simpa [ff, LExpr.boolConst] using condition
      have facts : a ≤ b ∧ b ≤ b ∧ (b = a ∨ b = b) := by
        simpa only [guard, ↓reduceIte] using certified a b
      exact max2_post model _ a b b factory (by simpa [frame xV (by decide)] using ha)
        (by simpa [frame yV (by decide)] using hb) result facts.1 facts.2.1 facts.2.2

example : Core.Logic.Hoare.Procedure.contractTriple max2Core params "max2" :=
  max2_certificate_transfers (by boole_vcgen <;> grind)

end HoareMax2

namespace HoareCompatibility

open Strata.Boole.Hoare

private def unusedRealGlobal :=
#strata
program Boole;
var g : real;
procedure ignoreGlobal() { };
#end

-- An unsupported global must be excluded even when no statement reads it.
example (checked : Core.Program) :
    ¬ CoreBridgeFragment (boole% unusedRealGlobal).ast (boole% unusedRealGlobal).names
      checked "ignoreGlobal" := by
  intro fragment
  have globals := fragment.1
  cbv at globals

end HoareCompatibility
