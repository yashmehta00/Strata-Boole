/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.Tagless.Hoare.Interpretation
import Std.Internal.Do
import Std.Tactic.Do

/-! # WP adapter and proved rules for the Hoare interpretation

The WP instance projects `.transform`. The rules below justify vcgen reductions
for that meaning; they do not yet establish its correspondence to Core execution.
No new axioms or admitted proofs are used.
-/

namespace Strata.Tagless.Hoare

open Std.Internal.Do Lean.Order

instance : WP Transformer Unit (State → Prop) Prop where
  wpTrans command := ⟨fun post _ => command.transform (post ())⟩
  wp_trans_monotone command := by
    intro post post' exceptional exceptional' _ hpost
    exact command.monotone _ _ (hpost ())

/-- The framework's WP is exactly the supplied transformer applied to its normal
postcondition. Commands return Unit and have no exceptional outcome here. -/
theorem wp_eq (command : Transformer) (Q : Unit → State → Prop) (exceptional : Prop) :
    wp command Q exceptional = command.transform (Q ()) := rfl

abbrev Triple (P : State → Prop) (command : Transformer) (Q : State → Prop) : Prop :=
  Std.Internal.Do.Triple command P (fun _ => Q) False

/-- A transformer triple says that every state satisfying the precondition
satisfies the command's generated requirement for the postcondition. -/
theorem triple_iff : Triple P command Q ↔
    ∀ σ, P σ → command.transform Q σ :=
  ⟨fun h => h.le_wp, fun h => ⟨h⟩⟩

/-- Skip establishes a postcondition precisely by requiring it initially. -/
@[spec] theorem skip_spec {Q : Unit → State → Prop} :
    Std.Internal.Do.Triple Transformer.skip (Q ()) Q False :=
  ⟨fun _ h => h⟩

/-- A sequence requires the first command to establish the second command's
requirement for the requested final postcondition. -/
@[spec] theorem seq_spec (first second : Transformer) {Q : Unit → State → Prop} :
    Std.Internal.Do.Triple (Transformer.seq first second)
      (wp first (fun _ => wp second Q False) False) Q False :=
  ⟨fun _ h => h⟩

/-- Assignment requires a defined expression and the postcondition in the state
obtained by updating the assigned variable with that expression's value. -/
@[spec] theorem assign_spec (ty : Ty) (x : String) (e : Expr ty)
    {Q : Unit → State → Prop} :
    Std.Internal.Do.Triple (Transformer.assign ty x e)
      (fun σ => e.defined σ ∧ Q () (σ.write ty x (e σ))) Q False :=
  ⟨fun _ h => h⟩

/-- Havoc requires the postcondition for every value of the assigned type. -/
@[spec] theorem havoc_spec (ty : Ty) (x : String) {Q : Unit → State → Prop} :
    Std.Internal.Do.Triple (Transformer.havoc ty x)
      (fun σ => ∀ v : ty.denote, Q () (σ.write ty x v)) Q False :=
  ⟨fun _ h => h⟩

/-- Assertion requires its expression to be defined and true, together with
the continuation's requirement in the unchanged state. -/
@[spec] theorem assert_spec (info : ClauseInfo) (e : Expr .bool)
    {Q : Unit → State → Prop} :
    Std.Internal.Do.Triple (Transformer.assert info e)
      ((fun σ => Obligation info.label (e.Holds σ)) ⊓ Q ()) Q False := by
  constructor
  intro σ h
  change Obligation info.label (e.Holds σ) ∧ Q () σ
  simpa only [meet_apply, meet_prop_eq_and] using h

/-- Assumption requires the continuation whenever the condition may hold;
undefined conditions supply no information and cannot discard the path. -/
@[spec] theorem assume_spec (info : ClauseInfo) (e : Expr .bool)
    {Q : Unit → State → Prop} :
    Std.Internal.Do.Triple (Transformer.assume info e)
      (e.MayHold ⇨ Q ()) Q False := by
  constructor
  intro σ h
  change e.MayHold σ → Q () σ
  simpa only [himp_apply, himp_prop_eq_imp] using h

/-- A branch requires a defined guard and the appropriate branch's requirement
for each possible Boolean value of that guard. -/
@[spec] theorem branch_spec (guard : Expr .bool) (yes no : Transformer)
    {Q : Unit → State → Prop} :
    Std.Internal.Do.Triple (Transformer.branch guard yes no)
      (guard.defined ⊓
       (((fun σ => guard σ = true) ⇨ wp yes Q False) ⊓
        ((fun σ => guard σ = false) ⇨ wp no Q False))) Q False := by
  constructor
  intro σ h
  simp only [meet_apply, meet_prop_eq_and, himp_apply, himp_prop_eq_imp, wp_eq] at h
  change guard.defined σ ∧
    if guard σ then yes.transform (Q ()) σ else no.transform (Q ()) σ
  refine ⟨h.1, ?_⟩
  by_cases hg : guard σ = true
  · simpa [hg] using h.2.1 hg
  · have hf : guard σ = false := Bool.eq_false_iff.mpr hg
    simpa [hf] using h.2.2 hf

/-- Nondeterministic choice requires both alternatives to establish the
postcondition, because execution may choose either one. -/
@[spec] theorem choice_spec (yes no : Transformer) {Q : Unit → State → Prop} :
    Std.Internal.Do.Triple (Transformer.choice yes no)
      (wp yes Q False ⊓ wp no Q False) Q False := by
  constructor
  intro σ h
  change yes.transform (Q ()) σ ∧ no.transform (Q ()) σ
  simpa only [meet_apply, meet_prop_eq_and, wp_eq] using h

/-- A scoped block establishes the postcondition after restoring its local
names to their entry values; other names retain the body's final values. -/
@[spec] theorem block_spec (locals : List String) (body : Transformer)
    {Q : Unit → State → Prop} :
    Std.Internal.Do.Triple (Transformer.block locals body)
      (fun entry => wp body (fun _ final => Q () (State.restore locals entry final)) False entry)
      Q False :=
  ⟨fun _ h => h⟩

/-- Keep the loop entry state in the generated predicate, so facts established
before the loop remain available for all unwritten variables. Nested body WPs
are reduced by `tagless_lift` using the same checked transformer definitions. -/
@[spec] theorem loop_spec (writes : List String) (guard : Expr .bool)
    (invariants : List (ClauseInfo × Expr .bool)) (measure : Option (Expr .int))
    (body : Transformer) {Q : Unit → State → Prop} :
    Std.Internal.Do.Triple (Transformer.loop writes guard invariants measure body)
      (fun entry => Transformer.loopHead invariants measure entry ∧
        ∀ arbitrary,
          let before := entry.havoc writes arbitrary
          Transformer.loopHead invariants measure before →
          guard.defined before ∧
          (guard before = true →
            wp body (fun _ after => Transformer.loopHead invariants measure after ∧
              Transformer.measureDrops measure before after) False before) ∧
          (guard before = false → Q () before)) Q False :=
  ⟨fun _ h => h⟩

/-- Only the remaining predicate-transformer equations are normalized here.
This does not revisit the Core AST or implement another VC generator. -/
macro "tagless_lift" : tactic => `(tactic|
  simp [requiresClause, ensuresClause, Expr.Holds, Expr.MayHold,
    Expr.total, Expr.unary, Expr.binary, Expr.divide, Expr.modulo, Expr.ite,
    State.read, State.write, State.restore, State.havoc,
    wp_eq, Transformer.skip, Transformer.seq, Transformer.assign, Transformer.havoc,
    Transformer.assert, Transformer.assume, Transformer.branch, Transformer.choice,
    Transformer.block, Transformer.loop, Transformer.invariantsHold,
    Transformer.loopHead, Transformer.measureBound, Transformer.measureDrops] at *)

end Strata.Tagless.Hoare
