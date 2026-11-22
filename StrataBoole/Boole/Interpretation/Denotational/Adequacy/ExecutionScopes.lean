/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.Typing
import all Strata.Languages.Core.Statement
import all Strata.Languages.Core.Typing.Spec.TypingSpec

public section
namespace Strata.Boole

open Core.TypeSpec

/-- A declaratively well-typed statement list can be cut at any source-list
boundary. The intermediate context and variable scopes are the outputs of
typing the prefix and the inputs for typing the suffix. -/
theorem statementsWellTyped_append_split
    {P : Core.Program} {C C' : Lambda.LContext Core.CoreLParams}
    {ts ts' : TypeScopes} {labels : List String}
    {headChunk tailChunk : List Core.Statement}
    (typed : StatementsWellTyped P C ts labels (headChunk ++ tailChunk) C' ts') :
    ∃ middleContext middleScopes,
      StatementsWellTyped P C ts labels headChunk middleContext middleScopes ∧
      StatementsWellTyped P middleContext middleScopes labels tailChunk C' ts' := by
  induction headChunk generalizing C ts with
  | nil =>
      refine ⟨C, ts, ?_, ?_⟩
      · exact .nil C ts labels ts (Strata.Util.HMaps.Equiv.refl ts)
      · simpa using typed
  | cons statement rest ih =>
      simp only [List.cons_append] at typed
      cases typed with
      | cons _ inferredContext _ _ inferredScopes _ _ _ _ headTyped tailTyped =>
          obtain ⟨middleContext, middleScopes, headTypedRest, suffixTyped⟩ := ih tailTyped
          exact ⟨middleContext, middleScopes,
            .cons C inferredContext middleContext ts inferredScopes middleScopes
              labels statement rest headTyped headTypedRest,
            suffixTyped⟩

/-- Erasing annotations commutes with cutting a statement list at a given
length. This lets a raw lowered list and its checked, annotated list be split
at the same clause boundary. -/
theorem statementsEraseTypes_take_drop
    {typed raw : List Core.Statement}
    (alignment : eraseStatementsAnnotations typed = raw) (n : Nat) :
    eraseStatementsAnnotations (typed.take n) = raw.take n ∧
    eraseStatementsAnnotations (typed.drop n) = raw.drop n := by
  subst raw
  constructor
  · induction typed generalizing n with
    | nil => simp [eraseStatementsAnnotations]
    | cons statement rest ih => cases n <;> simp [eraseStatementsAnnotations, ih]
  · induction typed generalizing n with
    | nil => simp [eraseStatementsAnnotations]
    | cons statement rest ih => cases n <;> simp [eraseStatementsAnnotations, ih]

end Strata.Boole
