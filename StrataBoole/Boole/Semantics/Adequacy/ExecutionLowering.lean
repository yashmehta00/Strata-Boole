/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.Lowering
import all StrataBoole.Boole.Semantics.Adequacy.Lowering
import all StrataBoole.Verify

public section
namespace Strata.Boole

open StrataDDM

/-- The Core statements emitted for one source statement. Most statements
emit one Core statement; variable declarations can emit several. -/
def lowerStatementChunk (statement : BooleDDM.Statement SourceRange) :
    TranslateM (List Core.Statement) :=
  match statement with
  | .varStatement range _ declarations => lowerVarStatement range declarations
  | statement => do return [← toCoreStmt statement]

/-- In a successful chunk traversal, the head source statement was lowered
successfully, and the tail is lowered from the state it produced. -/
theorem mapM_lowerStatementChunk_cons
    (head : BooleDDM.Statement SourceRange) (tail : List (BooleDDM.Statement SourceRange))
    (entry final : TranslateState) (chunks : List (List Core.Statement))
    (success : (head :: tail).mapM lowerStatementChunk entry = .ok (chunks, final)) :
    ∃ headChunk middle tailChunks,
      lowerStatementChunk head entry = .ok (headChunk, middle) ∧
      tail.mapM lowerStatementChunk middle = .ok (tailChunks, final) ∧
      chunks = headChunk :: tailChunks := by
  simp only [List.mapM_cons, bind, StateT.bind, Except.bind] at success
  cases first : lowerStatementChunk head entry with
  | error error => simp [first] at success
  | ok pair =>
    obtain ⟨headChunk, middle⟩ := pair
    cases rest : tail.mapM lowerStatementChunk middle with
    | error error => simp [first, rest] at success
    | ok result =>
      obtain ⟨tailChunks, after⟩ := result
      simp only [first, rest, pure, StateT.pure, Except.pure] at success
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
      exact ⟨headChunk, middle, tailChunks, by simpa using first,
        by simpa using rest, rfl⟩

/-- Recover the statement chunks from a lowering run with a known entry scope. -/
private theorem lower_block_chunks {range annotation : SourceRange}
    {source : Array (BooleDDM.Statement SourceRange)} {raw : List Core.Statement}
    {entry final : TranslateState}
    (ran : toCoreBlock (.block range ⟨annotation, source⟩) entry = .ok (raw, final)) :
    ∃ chunks,
      source.toList.mapM lowerStatementChunk entry = .ok (chunks, final) ∧
      chunks.flatten = raw := by
  rw [toCoreBlock] at ran
  have same : (fun s : BooleDDM.Statement SourceRange =>
      match s with
      | .varStatement range _ declarations => lowerVarStatement range declarations
      | _ => do return [← toCoreStmt s]) = lowerStatementChunk := by
    funext statement
    cases statement <;> rfl
  conv at ran =>
    lhs
    arg 1
    arg 1
    change (fun s : BooleDDM.Statement SourceRange =>
      match s with
      | .varStatement range _ declarations => lowerVarStatement range declarations
      | _ => do return [← toCoreStmt s])
    rw [same]
  simp only [bind, StateT.bind, Except.bind] at ran
  cases ranChunks : source.toList.mapM lowerStatementChunk entry with
  | error => simp [ranChunks] at ran
  | ok result =>
    obtain ⟨chunks, after⟩ := result
    simp only [ranChunks, pure, StateT.pure, Except.pure] at ran
    obtain ⟨sameStatements, rfl⟩ := Prod.mk.inj (Except.ok.inj ran)
    exact ⟨chunks, rfl, sameStatements⟩

/-- Recover the chunks produced by the original lowering of this block. -/
theorem BlockWasLowered.chunks {range annotation : SourceRange}
    {source : Array (BooleDDM.Statement SourceRange)} {raw : List Core.Statement}
    (lowered : BlockWasLowered (.block range ⟨annotation, source⟩) raw) :
    ∃ entry final chunks,
      source.toList.mapM lowerStatementChunk entry = .ok (chunks, final) ∧
      chunks.flatten = raw := by
  obtain ⟨entry, final, ran⟩ := lowered
  exact ⟨entry, final, lower_block_chunks ran⟩

end Strata.Boole
