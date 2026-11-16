/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.BlockShape
import all StrataBoole.Boole.Semantics.Adequacy.Lowering

public section

namespace Strata.Boole

/-- A successful block interpretation contains a successful interpretation of
its statement list. The block itself applies the runtime scope constructor to
that list's denotation. -/
private theorem interpBlock_inner {I : Interpretation}
    (range annotation : SourceRange) (statements : Array (BooleDDM.Statement SourceRange))
    (entry final : Scope) (body : I.Statement)
    (success : interpBlock I (.block range ⟨annotation, statements⟩) entry = .ok (body, final)) :
    ∃ (inner : I.Statement) (middle : Scope),
      interpStmts I statements.toList entry = .ok (inner, middle) ∧ body = I.scope inner ∧ final = entry := by
  have success' : withScope
      (do let inner ← interpStmts I statements.toList; pure (I.scope inner)) entry =
      .ok (body, final) := by
    simpa only [interpBlock] using success
  obtain ⟨middle, action⟩ := withScope_success success'
  have finalEq : final = entry := by
    simp only [withScope, bind, StateT.bind, Except.bind, pure, StateT.pure,
      Except.pure, get, getThe, MonadStateOf.get, StateT.get, set,
      MonadStateOf.set, StateT.set] at success'
    split at success'
    · contradiction
    · rename_i result evaluated
      have sameState := congrArg Prod.snd (Except.ok.inj success')
      cases result
      simp_all
  change (interpStmts I statements.toList >>= fun inner => pure (I.scope inner)) entry =
      .ok (body, middle) at action
  cases statementsRun : interpStmts I statements.toList entry with
  | error error =>
      simp only [statementsRun, bind, StateT.bind, Except.bind] at action
      simp at action
  | ok result =>
      obtain ⟨inner, after⟩ := result
      simp only [statementsRun, bind, StateT.bind, Except.bind] at action
      obtain ⟨bodyEq, middleEq⟩ := Prod.mk.inj (Except.ok.inj action)
      exact ⟨inner, after, rfl, bodyEq.symm, finalEq⟩

/-- When a nonempty Boole procedure body lowers to one named Core block,
the source interpreter and the lowerer refer to that same block and the
same inner Core statement list. This is the structural bridge needed before
comparing the two bodies' executions. -/
theorem nonempty_body_alignment
    {command : BooleDDM.Command SourceRange} {source : ProcedureMeaning} {procedure : Core.Procedure}
    (interpreted : ProcedureWasInterpreted (denotation .builtins) command source)
    (translated : ProcedureWasLowered command procedure)
    (name : String) (raw : List Core.Statement)
    (shape : procedure.body = .structured [.block name raw .empty]) :
    ∃ (range annotation : SourceRange)
      (sourceStatements : Array (BooleDDM.Statement SourceRange))
      (entry innerFinal : Scope) (inner : (denotation .builtins).Statement),
      sourceStatements ≠ #[] ∧
      BlockWasLowered (.block range ⟨annotation, sourceStatements⟩) raw ∧
      interpStmts (denotation .builtins) sourceStatements.toList entry = .ok (inner, innerFinal) ∧
      source.body = Computation.block name (Computation.scope inner) := by
  obtain ⟨block, loweredName, entry, final, body, loweredRaw, sourceRun,
    sourceBody, loweringRun, originShape⟩ := lowered_body_origin interpreted translated
  cases block with
  | block range statements =>
    obtain ⟨annotation, sourceStatements⟩ := statements
    have rawNonempty : loweredRaw ≠ [] := by
      intro empty
      have bodies := shape.symm.trans originShape
      rw [empty] at bodies
      simp at bodies
    have canonicalShape : procedure.body =
        .structured [.block loweredName loweredRaw .empty] := by
      simpa [List.isEmpty_eq_false_iff.mpr rawNonempty] using originShape
    have bodyEq := Imperative.Body.structured.inj (shape.symm.trans canonicalShape)
    have sameBlock : (.block name raw .empty : Core.Statement) =
        .block loweredName loweredRaw .empty := by
      rcases List.cons.inj bodyEq with ⟨sameBlock, _⟩
      exact sameBlock
    injection sameBlock with sameName sameRaw sameMetadata
    subst loweredName
    subst loweredRaw
    have sourceNonempty : sourceStatements ≠ #[] := by
      intro empty
      have emptyLowering : BlockWasLowered
          (.block range ⟨annotation, #[]⟩ : BooleDDM.Block SourceRange) raw := by
        simpa [empty] using loweringRun
      have loweredEmpty := BlockWasLowered.empty range annotation raw emptyLowering
      exact rawNonempty loweredEmpty
    obtain ⟨inner, middle, innerRun, bodyEq, _⟩ :=
      interpBlock_inner range annotation sourceStatements entry final body sourceRun
    refine ⟨range, annotation, sourceStatements, entry, middle, inner, sourceNonempty,
      loweringRun, innerRun, ?_⟩
    · simpa [denotation, bodyEq] using sourceBody


/-- Align the nonempty body of a procedure matched by the checker-based proof. -/
theorem MatchedProcedure.nonempty_body_alignment (matched : MatchedProcedure)
    (name : String) (raw : List Core.Statement)
    (shape : matched.loweredProcedure.body = .structured [.block name raw .empty]) :
    ∃ (range annotation : SourceRange)
      (sourceStatements : Array (BooleDDM.Statement SourceRange))
      (entry innerFinal : Scope) (inner : (denotation .builtins).Statement),
      sourceStatements ≠ #[] ∧
      BlockWasLowered (.block range ⟨annotation, sourceStatements⟩) raw ∧
      interpStmts (denotation .builtins) sourceStatements.toList entry = .ok (inner, innerFinal) ∧
      matched.source.body = Computation.block name (Computation.scope inner) :=
  Strata.Boole.nonempty_body_alignment matched.interpreted matched.translated name raw shape

end Strata.Boole
