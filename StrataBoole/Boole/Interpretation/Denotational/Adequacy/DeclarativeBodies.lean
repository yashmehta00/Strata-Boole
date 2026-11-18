/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.Typing
public import StrataBoole.Boole.Semantics.Adequacy.BodyAlignment
import all Strata.Languages.Core.Typing.Spec.TypingSpec
import all Strata.DL.Imperative.Stmt

public section

namespace Strata.Boole

open Core.TypeSpec

private def statementExitCoverage (P : Core.Program) :
    (C : Lambda.LContext Core.CoreLParams) → (ts : TypeScopes) → (labels : List String) →
    (statement : Core.Statement) → (C' : Lambda.LContext Core.CoreLParams) →
    (ts' : TypeScopes) → StatementWellTyped P C ts labels statement C' ts' → Prop :=
  fun _ _ labels statement _ _ _ => Imperative.Stmt.exitsCoveredByBlocks labels statement

private def statementsExitCoverage (P : Core.Program) :
    (C : Lambda.LContext Core.CoreLParams) → (ts : TypeScopes) → (labels : List String) →
    (statements : List Core.Statement) → (C' : Lambda.LContext Core.CoreLParams) →
    (ts' : TypeScopes) → StatementsWellTyped P C ts labels statements C' ts' → Prop :=
  fun _ _ labels statements _ _ _ => Imperative.Block.exitsCoveredByBlocks labels statements

private theorem exitCoverageRecursor (P : Core.Program)
    {C : Lambda.LContext Core.CoreLParams} {ts : TypeScopes} {labels : List String}
    {statements : List Core.Statement} {C' : Lambda.LContext Core.CoreLParams} {ts' : TypeScopes}
    (typed : StatementsWellTyped P C ts labels statements C' ts') :
    Imperative.Block.exitsCoveredByBlocks labels statements := by
  exact Core.TypeSpec.StatementsWellTyped.rec
    (motive_1 := statementExitCoverage P) (motive_2 := statementsExitCoverage P)
    (by
      intro C ts labels c ts' commandTyped
      change Imperative.Stmt.exitsCoveredByBlocks labels (.cmd c)
      simp [Imperative.Stmt.exitsCoveredByBlocks])
    (by
      intro C ts Cbody tsbody labels label body md ts' fresh bodyTyped equiv bodyCovered
      change Imperative.Block.exitsCoveredByBlocks (label :: labels) body at bodyCovered
      change Imperative.Stmt.exitsCoveredByBlocks labels (.block label body md)
      simpa [Imperative.Stmt.exitsCoveredByBlocks] using bodyCovered)
    (by
      intro C ts Ct tst Ce tse labels cond yes no md ts' guard yesTyped noTyped equiv yesCovered noCovered
      change Imperative.Block.exitsCoveredByBlocks labels yes ∧
        Imperative.Block.exitsCoveredByBlocks labels no
      exact ⟨yesCovered, noCovered⟩)
    (by
      intro C ts Ct tst Ce tse labels yes no md ts' yesTyped noTyped equiv yesCovered noCovered
      change Imperative.Block.exitsCoveredByBlocks labels yes ∧
        Imperative.Block.exitsCoveredByBlocks labels no
      exact ⟨yesCovered, noCovered⟩)
    (by
      intro C ts Cbody tsbody labels guard measure invariants body md ts' guardTyped measureTyped invariantTyped bodyTyped equiv bodyCovered
      change Imperative.Block.exitsCoveredByBlocks labels body at bodyCovered
      change Imperative.Stmt.exitsCoveredByBlocks labels (.loop guard measure invariants body md)
      simpa [Imperative.Stmt.exitsCoveredByBlocks] using bodyCovered)
    (by
      intro C ts labels label md ts' inScope equiv
      change label ∈ labels
      exact inScope)
    (by
      intro C C' ts labels tc md ts' noName added equiv
      change Imperative.Stmt.exitsCoveredByBlocks labels (.typeDecl tc md)
      simp [Imperative.Stmt.exitsCoveredByBlocks])
    (by
      intro C ts labels ts' equiv
      change Imperative.Block.exitsCoveredByBlocks labels []
      simp [Imperative.Block.exitsCoveredByBlocks])
    (by
      intro C C' C'' ts ts' ts'' labels statement rest headTyped tailTyped headCovered tailCovered
      change Imperative.Block.exitsCoveredByBlocks labels (statement :: rest)
      exact ⟨headCovered, tailCovered⟩)
    typed

/-- A typed statement list has no exit whose target falls outside its
lexically enclosing block labels. -/
theorem statementsWellTyped_exitsCovered
    {P : Core.Program} {C C' : Lambda.LContext Core.CoreLParams}
    {ts ts' : TypeScopes} {labels : List String} {statements : List Core.Statement}
    (typed : StatementsWellTyped P C ts labels statements C' ts') :
    Imperative.Block.exitsCoveredByBlocks labels statements :=
  exitCoverageRecursor P typed

/-- Declarative typing ensures each exit is caught by a lexically enclosing
block or by a label supplied by the surrounding context. -/
theorem statementWellTyped_exitsCovered
    {P : Core.Program} {C C' : Lambda.LContext Core.CoreLParams}
    {ts ts' : TypeScopes} {labels : List String} {statement : Core.Statement}
    (typed : StatementWellTyped P C ts labels statement C' ts') :
    Imperative.Stmt.exitsCoveredByBlocks labels statement := by
  have empty : StatementsWellTyped P C' ts' labels [] C' ts' :=
    .nil C' ts' labels ts' (Strata.Util.HMaps.Equiv.refl ts')
  have singleton : StatementsWellTyped P C ts labels [statement] C' ts' :=
    @StatementsWellTyped.cons P C C' C' ts ts' ts' labels statement [] typed empty
  have coverage := statementsWellTyped_exitsCovered singleton
  simpa [Imperative.Block.exitsCoveredByBlocks] using coverage.1

/-- Align the successful Boole statement-list interpretation with the
declaratively typed Core statements originating from that same block. -/
theorem declarative_body_alignment
    {command : BooleDDM.Command SourceRange} {source : ProcedureMeaning}
    {program : Core.Program} {context : Core.Expression.TyContext}
    {scopes : TypeScopes} {raw annotated : Core.Procedure}
    {name : String} {rawStatements : List Core.Statement}
    (interpreted : ProcedureWasInterpreted denotation command source)
    (translated : ProcedureWasLowered command raw)
    (typed : ProcWellTyped program context scopes annotated)
    (rawBody : raw.body = .structured [.block name rawStatements .empty])
    (sameBody : (procedureWithoutAnnotations annotated).body = (procedureWithoutAnnotations raw).body) :
    ∃ (range annotation : SourceRange)
      (sourceStatements : Array (BooleDDM.Statement SourceRange))
      (entry final : Scope) (inner : denotation.Statement)
      (annotatedStatements : List Core.Statement)
      (finalContext : Core.Expression.TyContext) (finalScopes : TypeScopes),
      BlockWasLowered (.block range ⟨annotation, sourceStatements⟩) rawStatements ∧
      interpStmts denotation sourceStatements.toList entry = .ok (inner, final) ∧
      source.body = Computation.block name (Computation.scope inner) ∧
      annotated.body = .structured [.block name annotatedStatements .empty] ∧
      eraseStatementsAnnotations annotatedStatements = eraseStatementsAnnotations rawStatements ∧
      StatementsWellTyped program context (procBodyScopes scopes annotated) [name]
        annotatedStatements finalContext finalScopes ∧
      Imperative.Stmt.exitsCoveredByBlocks [] (.block name annotatedStatements .empty) := by
  obtain ⟨range, annotation, sourceStatements, entry, final, inner, _, lowered, ran, sourceBody⟩ :=
    nonempty_body_alignment interpreted translated name rawStatements rawBody
  obtain ⟨annotatedStatements, finalContext, finalScopes, body, sameStatements, statementsTyped⟩ :=
    typed_lowered_block typed rawBody sameBody
  obtain ⟨_, _, wrapperTyped⟩ := typed_structured_body typed body
  have covered := statementsWellTyped_exitsCovered wrapperTyped
  exact ⟨range, annotation, sourceStatements, entry, final, inner, annotatedStatements,
    finalContext, finalScopes, lowered, ran, sourceBody, body, sameStatements,
    statementsTyped, covered.1⟩

end Strata.Boole
