/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.Tagless.Embed
import StrataBoole.Tagless.Hoare.Rules

/-! # Procedure certificates and the verification entry point

A certificate retains both the checked embedding equation and the interpreted
contract proof. `tagless_vcgen` constructs that certificate using the WP adapter
and proved rules in `Rules.lean`; it does not establish Core soundness itself.
-/

namespace Strata.Tagless.Hoare

/-- Successful embedding and validity of the resulting transformer contract.
The bridge to Core's operational semantics remains a separate theorem. -/
def Verified (p : Core.Procedure) : Prop :=
  ∃ recipes, embedCore p = .ok recipes ∧
    let (P, command, Q) := interpret recipes
    Triple P command Q

open Lean Elab Tactic

/-- Specialize embedding once, retaining its checked equality as part of the
certificate. A scratch equality lets the same `tagless_embed` equations supply
both precise failure diagnostics and the successful recipe witness. -/
elab "tagless_start" : tactic => do
  let target ← getMainTarget
  unless target.isAppOfArity ``Verified 1 do
    throwError "tagless_vcgen expects a goal Hoare.Verified p"
  let embedding ← Meta.mkAppM ``embedCore #[target.getArg! 0]
  let result ← Meta.mkFreshExprMVar (← Meta.inferType embedding)
  let equality ← Meta.mkFreshExprMVar (← Meta.mkEq embedding result)
  let savedGoals ← getGoals
  try
    setGoals [equality.mvarId!]
    evalTactic (← `(tactic| (tagless_embed; try rfl)))
    unless (← getGoals).isEmpty do
      throwError "cannot specialize embedCore; unfold the concrete Core procedure first"
  finally
    setGoals savedGoals
  let normalized := (← Meta.whnf (← instantiateMVars result)).consumeMData
  if normalized.isAppOf ``Except.error then
    throwError "tagless embedding failed: {normalized.getAppArgs.back!}"
  unless normalized.isAppOf ``Except.ok do
    throwError "cannot specialize embedCore; unfold the concrete Core procedure first"
  let recipes := normalized.getAppArgs.back!
  let existsType ← Meta.whnf target
  let contract ← Meta.whnf (Lean.mkApp existsType.appArg! recipes)
  let obligation ← Meta.mkFreshExprMVar contract.appArg!
  let pair ← Meta.mkAppM ``And.intro #[← instantiateMVars equality, obligation]
  let proof ← Meta.mkAppOptM ``Exists.intro
    #[some (existsType.getArg! 0), some existsType.appArg!, some recipes, some pair]
  (← getMainGoal).assign proof
  replaceMainGoal [obligation.mvarId!]

/-- Name remaining goals using their first source clause, then remove the
transparent presentation wrapper. This changes no proof obligation. -/
elab "tagless_label" : tactic => do
  for goal in ← getGoals do
    goal.withContext do
      let target ← instantiateMVars (← goal.getType)
      if let some term := target.find? (fun e => e.isAppOfArity ``Obligation 2) then
        if let .lit (.strVal label) := term.getArg! 0 then
          if !label.isEmpty then
            goal.setTag ((← goal.getTag).str label)
  evalTactic (← `(tactic| all_goals simp only [Obligation] at *))

/-- Expose the concrete Core definition before invoking this tactic. It specializes
its recipes, applies the registered WP rules, and simplifies the resulting VCs. -/
macro "tagless_vcgen" : tactic => `(tactic| (
  tagless_start
  dsimp only [interpret, interpretation]
  vcgen
  all_goals tagless_lift
  tagless_label))

end Strata.Tagless.Hoare
