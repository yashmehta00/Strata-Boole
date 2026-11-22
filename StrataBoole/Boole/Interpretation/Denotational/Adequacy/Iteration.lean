/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Legacy.Semantics
import all StrataBoole.Boole.Interpretation.Legacy.Semantics

public section

namespace Strata.Boole.Computation

/-- An induction principle presented as a relation for finite loop outcomes. -/
inductive Iteration (guard : Computation Bool) (body : Computation Unit) : State → Outcome Unit → Prop
  | stop : guard.run initial (.returned false final) → Iteration guard body initial (.returned () final)
  | next : guard.run initial (.returned true middle) → body.run middle (.returned () nextState) →
      Iteration guard body nextState outcome → Iteration guard body initial outcome
  | guardExit : guard.run initial (.exited label final) → Iteration guard body initial (.exited label final)
  | guardFailure : guard.run initial (.assertionFailed label final) →
      Iteration guard body initial (.assertionFailed label final)
  | guardStuck : guard.run initial (.stuck reason final) → Iteration guard body initial (.stuck reason final)
  | bodyExit : guard.run initial (.returned true middle) → body.run middle (.exited label final) →
      Iteration guard body initial (.exited label final)
  | bodyFailure : guard.run initial (.returned true middle) → body.run middle (.assertionFailed label final) →
      Iteration guard body initial (.assertionFailed label final)
  | bodyStuck : guard.run initial (.returned true middle) → body.run middle (.stuck reason final) →
      Iteration guard body initial (.stuck reason final)

private theorem iteration_of_unfold {guard : Computation Bool} {body : Computation Unit}
    (n : Nat) {initial : State} {outcome : Outcome Unit}
    (ran : (loopUnfold guard body n).run initial outcome) :
    Iteration guard body initial outcome := by
  induction n generalizing initial outcome with
  | zero => exact False.elim ran
  | succ n ih =>
    change ((loopStep guard body (loopUnfold guard body n)).run initial outcome) at ran
    rcases ran with ⟨proceed, middle, tested, continued⟩ | ⟨_, _, tested, rfl⟩ |
      ⟨_, _, tested, rfl⟩ | ⟨_, _, tested, rfl⟩
    · cases proceed
      · change outcome = .returned () middle at continued
        subst outcome
        exact .stop tested
      · rcases continued with ⟨⟨⟩, next, stepped, rest⟩ | ⟨_, _, stepped, rfl⟩ |
          ⟨_, _, stepped, rfl⟩ | ⟨_, _, stepped, rfl⟩
        · exact .next tested stepped (ih rest)
        · exact .bodyExit tested stepped
        · exact .bodyFailure tested stepped
        · exact .bodyStuck tested stepped
    · exact .guardExit tested
    · exact .guardFailure tested
    · exact .guardStuck tested

/-- The unfolding semantics and the inductive loop rules admit the same
outcomes from every initial state. -/
theorem loop_iff_iteration {guard : Computation Bool} {body : Computation Unit}
    {initial : State} {outcome : Outcome Unit} :
    (loop guard body).run initial outcome ↔ Iteration guard body initial outcome := by
  constructor
  · rintro ⟨n, ran⟩
    exact iteration_of_unfold n ran
  · intro ran
    induction ran with
    | stop h =>
      exact ⟨1, .inl ⟨false, _, h, rfl⟩⟩
    | next tested stepped _ ih =>
      obtain ⟨n, rest⟩ := ih
      exact ⟨n + 1, .inl ⟨true, _, tested, .inl ⟨(), _, stepped, rest⟩⟩⟩
    | guardExit h => exact ⟨1, .inr (.inl ⟨_, _, h, rfl⟩)⟩
    | guardFailure h => exact ⟨1, .inr (.inr (.inl ⟨_, _, h, rfl⟩))⟩
    | guardStuck h => exact ⟨1, .inr (.inr (.inr ⟨_, _, h, rfl⟩))⟩
    | bodyExit tested stepped =>
      exact ⟨1, .inl ⟨true, _, tested, .inr (.inl ⟨_, _, stepped, rfl⟩)⟩⟩
    | bodyFailure tested stepped =>
      exact ⟨1, .inl ⟨true, _, tested, .inr (.inr (.inl ⟨_, _, stepped, rfl⟩))⟩⟩
    | bodyStuck tested stepped =>
      exact ⟨1, .inl ⟨true, _, tested, .inr (.inr (.inr ⟨_, _, stepped, rfl⟩))⟩⟩

end Strata.Boole.Computation
