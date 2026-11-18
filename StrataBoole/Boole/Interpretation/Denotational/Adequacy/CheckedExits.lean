/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementType
import all Strata.Languages.Core.StatementType
public import Strata.DL.Imperative.StmtProps

namespace Strata.Boole

open Imperative

private theorem exitsCovered_reverse (labels : List String) (ss : List Core.Statement)
    (covered : Block.exitsCoveredByBlocks labels ss) :
    Block.exitsCoveredByBlocks labels ss.reverse := by
  induction ss with
  | nil => exact covered
  | cons statement rest ih =>
    rw [List.reverse_cons]
    exact block_exitsCoveredByBlocks_append labels _ _ (ih covered.2) ⟨covered.1, trivial⟩

private theorem checked_before_error_context {action : Except ε α} {result : α}
    {annotate : ε → ε}
    (success : action.tryCatch (fun error => .error (annotate error)) = .ok result) :
    action = .ok result := by
  cases action <;> simpa [Except.tryCatch] using success

set_option maxHeartbeats 1200000 in
private theorem checkedList_exitsCovered (program : Core.Program) (procedure : Option Core.Procedure)
    (context : Core.Expression.TyContext) (initial : Core.Expression.TyEnv)
    (ss acc : List Core.Statement) (labels : List String) :
    ∀ result,
      Core.Statement.typeCheckAux.go program procedure context initial ss acc labels = .ok result →
      Block.exitsCoveredByBlocks labels acc → Block.exitsCoveredByBlocks labels result.1 := by
  refine Core.Statement.typeCheckAux.go.induct program procedure
    (motive1 := fun context initial ss acc labels => ∀ result,
      Core.Statement.typeCheckAux.go program procedure context initial ss acc labels = .ok result →
      Block.exitsCoveredByBlocks labels acc → Block.exitsCoveredByBlocks labels result.1)
    (motive2 := fun context initial ss acc labels => ∀ result,
      Core.Statement.typeCheckAux.goBlock program procedure context initial ss acc labels = .ok result →
      Block.exitsCoveredByBlocks labels acc → Block.exitsCoveredByBlocks labels result.1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ context initial ss acc labels
  · intro context initial acc labels result ran covered
    rw [Core.Statement.typeCheckAux.go] at ran
    obtain rfl := Except.ok.inj ran
    exact exitsCovered_reverse _ _ covered
  · intro context initial acc labels rest command next result ran covered
    simp only [Core.Statement.typeCheckAux.go, bind, Except.bind] at ran
    split at ran
    · contradiction
    · exact next _ _ _ _ ran ⟨trivial, covered⟩
  · intro context initial acc labels rest label body md repeated next checked result ran covered
    simp only [Core.Statement.typeCheckAux.go, repeated, ↓reduceIte, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw] at ran
    contradiction
  · intro context initial acc labels rest label body md fresh next checked result ran covered
    simp only [Core.Statement.typeCheckAux.go, fresh, Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at ran
    split at ran
    · contradiction
    · rename_i intermediate ranBlock
      exact next _ _ _ _ ran ⟨checked _ ranBlock trivial, covered⟩
  · intro context initial acc labels rest cond yes no md next branches result ran covered
    cases cond with
    | det c =>
      obtain ⟨yesChecked, noChecked⟩ := branches
      simp only [Core.Statement.typeCheckAux.go, bind, Except.bind, tryCatch, tryCatchThe,
        MonadExceptOf.tryCatch] at ran
      split at ran
      · contradiction
      · rename_i statement headChecked
        replace headChecked := checked_before_error_context headChecked
        repeat' first
          | contradiction
          | (obtain rfl := Except.ok.inj headChecked
             exact next _ _ _ _ ran ⟨⟨yesChecked _ _ (by assumption) trivial,
               noChecked _ _ _ (by assumption) trivial⟩, covered⟩)
          | split at headChecked
    | nondet =>
      obtain ⟨yesChecked, noChecked⟩ := branches
      simp only [Core.Statement.typeCheckAux.go, bind, Except.bind, tryCatch, tryCatchThe,
        MonadExceptOf.tryCatch] at ran
      split at ran
      · contradiction
      · rename_i statement headChecked
        replace headChecked := checked_before_error_context headChecked
        repeat' first
          | contradiction
          | (obtain rfl := Except.ok.inj headChecked
             exact next _ _ _ _ ran ⟨⟨yesChecked _ (by assumption) trivial,
               noChecked _ _ _ (by assumption) trivial⟩, covered⟩)
          | split at headChecked
  · intro context initial acc labels rest guard measure invariants body md next bodyChecked result ran covered
    simp only [Core.Statement.typeCheckAux.go, bind, Except.bind, tryCatch, tryCatchThe,
      MonadExceptOf.tryCatch] at ran
    split at ran
    · contradiction
    · rename_i statement headChecked
      replace headChecked := checked_before_error_context headChecked
      repeat' first
        | contradiction
        | (obtain rfl := Except.ok.inj headChecked
           exact next _ _ _ _ ran ⟨bodyChecked _ _ (by assumption) trivial, covered⟩)
        | split at headChecked
  · intro context initial acc labels rest label md next result ran covered
    cases procedure with
    | none =>
      simp [Core.Statement.typeCheckAux.go, bind, Except.bind, tryCatch, tryCatchThe,
        MonadExceptOf.tryCatch, Except.tryCatch] at ran
    | some procedure =>
      by_cases visible : label ∈ labels
      · simp [Core.Statement.typeCheckAux.go, visible, bind, Except.bind, tryCatch, tryCatchThe,
          MonadExceptOf.tryCatch, Except.tryCatch] at ran
        exact next _ _ _ _ ran ⟨visible, covered⟩
      · simp [Core.Statement.typeCheckAux.go, visible, bind, Except.bind, tryCatch, tryCatchThe,
          MonadExceptOf.tryCatch, Except.tryCatch] at ran
  · intro context initial acc labels rest tc md next result ran covered
    simp only [Core.Statement.typeCheckAux.go, bind, Except.bind, tryCatch, tryCatchThe,
      MonadExceptOf.tryCatch] at ran
    split at ran
    · contradiction
    · rename_i statement headChecked
      replace headChecked := checked_before_error_context headChecked
      repeat' first
        | contradiction
        | (obtain rfl := Except.ok.inj headChecked
           exact next _ _ _ _ ran ⟨trivial, covered⟩)
        | split at headChecked
  · intro context initial ss acc labels pushed checked result ran covered
    unfold Core.Statement.typeCheckAux.goBlock at ran
    simp only [bind, Except.bind] at ran
    split at ran
    · contradiction
    · rename_i intermediate success
      obtain rfl := Except.ok.inj ran
      exact checked intermediate success covered

private theorem substList_exitsCovered (subst : Lambda.Subst)
    (ss acc : List Core.Statement) (labels : List String) :
    Block.exitsCoveredByBlocks labels ss → Block.exitsCoveredByBlocks labels acc →
    Block.exitsCoveredByBlocks labels (Core.Statement.Statement.subst.go subst ss acc) := by
  refine Core.Statement.Statement.subst.go.induct subst
    (motive_1 := fun ss acc => ∀ labels,
      Block.exitsCoveredByBlocks labels ss → Block.exitsCoveredByBlocks labels acc →
      Block.exitsCoveredByBlocks labels (Core.Statement.Statement.subst.go subst ss acc))
    (motive_2 := fun s => ∀ labels, Stmt.exitsCoveredByBlocks labels s →
      Stmt.exitsCoveredByBlocks labels (Core.Statement.Statement.subst subst s))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ss acc labels
  · intro cmd labels covered
    rw [Core.Statement.Statement.subst]
    exact trivial
  · intro label body md ih labels covered
    rw [Core.Statement.Statement.subst]
    exact ih (label :: labels) covered trivial
  · intro cond yes no md yesIH noIH labels covered
    rw [Core.Statement.Statement.subst]
    exact ⟨yesIH labels covered.1 trivial, noIH labels covered.2 trivial⟩
  · intro guard measure invariant body md ih labels covered
    rw [Core.Statement.Statement.subst]
    exact ih labels covered trivial
  · intro label md labels covered
    simpa only [Core.Statement.Statement.subst] using covered
  · intro tc md labels covered
    simpa only [Core.Statement.Statement.subst] using covered
  · intro acc labels _ covered
    rw [Core.Statement.Statement.subst.go]
    exact exitsCovered_reverse _ _ covered
  · intro acc head tail headIH tailIH labels covered accCovered
    rw [Core.Statement.Statement.subst.go]
    exact tailIH labels covered.2 ⟨headIH labels covered.1, accCovered⟩

public section

/-- A successfully checked structured body has an enclosing block for every
exit. Type substitution preserves exit labels and their enclosing blocks. -/
theorem checkedStatements_exitsCovered {program : Core.Program} {procedure : Option Core.Procedure}
    {context : Core.Expression.TyContext} {initial final : Core.Expression.TyEnv}
    {raw checked : List Core.Statement}
    (success : Core.Statement.typeCheck context initial program procedure raw = .ok (checked, final)) :
    Block.exitsCoveredByBlocks [] checked := by
  unfold Core.Statement.typeCheck Core.Statement.typeCheckAux at success
  simp only [bind, Except.bind] at success
  split at success
  · contradiction
  · rename_i intermediate ran
    have output := congrArg Prod.fst (Except.ok.inj success)
    dsimp only at output
    rw [← output]
    exact substList_exitsCovered _ _ _ [] (checkedList_exitsCovered _ _ _ _ _ _ _ _ ran trivial)
      trivial

end

end Strata.Boole
