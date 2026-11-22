module

public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.Lowering
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Lowering
import all StrataBoole.Verify

public section

namespace Strata.Boole

private abbrev VarAcc := List (Imperative.Stmt Core.Expression Core.Command) × List Core.Expression.Expr

private def lowerOneBind (m : SourceRange) (d : BooleDDM.Bind SourceRange)
    (acc : VarAcc) : TranslateM (ForInStep VarAcc) := do
  let binding ← toCoreBind d
  let metadata ← toCoreMetaData m
  pure (.yield (Core.Statement.init binding.1 binding.2 .nondet metadata :: acc.1,
    (.fvar () binding.1 none : Core.Expression.Expr) :: acc.2))

private theorem lowerOneBind_adds_statement (m : SourceRange) (d : BooleDDM.Bind SourceRange)
    (acc : VarAcc) (state state' : TranslateState) (step : ForInStep VarAcc)
    (run : lowerOneBind m d acc state = .ok (step, state')) :
    ∃ binding : Core.Expression.Ident × Core.Expression.Ty, ∃ metadata, step = .yield (Core.Statement.init binding.1 binding.2 .nondet metadata :: acc.1,
      (.fvar () binding.1 none : Core.Expression.Expr) :: acc.2) := by
  simp only [lowerOneBind, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at run
  cases bindRun : toCoreBind d state with
  | error e => simp [bindRun] at run
  | ok bindResult =>
      obtain ⟨binding, afterBind⟩ := bindResult
      rw [bindRun] at run
      cases metadataRun : toCoreMetaData m afterBind with
      | error e => simp [metadataRun] at run
      | ok metadataResult =>
          obtain ⟨metadata, afterMetadata⟩ := metadataResult
          simp [metadataRun] at run
          rcases run with ⟨stepEq, _⟩
          rw [← stepEq]
          exact ⟨binding, metadata, rfl⟩

private theorem lowerOneBind_loop_nonempty (m : SourceRange) (ds : List (BooleDDM.Bind SourceRange))
    (acc : VarAcc) (state : TranslateState) (result : VarAcc) (final : TranslateState)
    (success : (forIn ds acc (lowerOneBind m)) state = .ok (result, final))
    (initialNonempty : acc.1 ≠ [] ∨ ds ≠ []) : result.1 ≠ [] := by
  induction ds generalizing acc state result final with
  | nil =>
      rw [List.forIn_nil] at success
      simp only [pure, StateT.pure, Except.pure, Prod.mk.injEq] at success
      rcases success with ⟨rfl, rfl⟩
      rcases initialNonempty with nonempty | impossible
      · exact nonempty
      · exact False.elim (impossible rfl)
  | cons d ds ih =>
      rw [List.forIn_cons] at success
      simp only [bind, StateT.bind, Except.bind] at success
      cases firstRun : lowerOneBind m d acc state with
      | error e => simp [firstRun] at success
      | ok firstResult =>
          obtain ⟨step, afterFirst⟩ := firstResult
          have stepHasHead := lowerOneBind_adds_statement m d acc state afterFirst step firstRun
          cases step with
          | done acc' =>
              obtain ⟨binding, metadata, h⟩ := stepHasHead
              cases h
          | yield acc' =>
              obtain ⟨binding, metadata, h⟩ := stepHasHead
              have accEq : acc' = (Core.Statement.init binding.1 binding.2 .nondet metadata :: acc.1,
                  (.fvar () binding.1 none : Core.Expression.Expr) :: acc.2) := by injection h
              have accNonempty : acc'.1 ≠ [] := by simp [accEq]
              simp only [firstRun, Except.bind, Except.map] at success
              cases tailRun : (forIn ds acc' (lowerOneBind m)) afterFirst with
              | error e => simp [tailRun] at success
              | ok tailResult =>
                  obtain ⟨tailAcc, tailFinal⟩ := tailResult
                  have same : tailAcc = result ∧ tailFinal = final := by
                    simpa [tailRun] using success
                  rcases same with ⟨rfl, rfl⟩
                  exact ih acc' afterFirst _ _ tailRun (Or.inl accNonempty)

private theorem declListToListRev_ne_nil (ds : BooleDDM.DeclList SourceRange)
    (acc : List (BooleDDM.Bind SourceRange)) : declListToListRev ds acc ≠ [] := by
  induction ds generalizing acc with
  | declAtom _ bind => simp [declListToListRev]
  | declPush _ rest bind ih => simpa [declListToListRev] using ih (bind :: acc)

private theorem declListToList_ne_nil (ds : BooleDDM.DeclList SourceRange) : declListToList ds ≠ [] := by
  exact declListToListRev_ne_nil ds []

private theorem lowerVarStatement_nonempty (m : SourceRange) (ds : BooleDDM.DeclList SourceRange)
    (state : TranslateState) (out : List Core.Statement) (final : TranslateState)
    (success : lowerVarStatement m ds state = .ok (out, final)) : out ≠ [] := by
  simp only [lowerVarStatement, bind, StateT.bind, Except.bind] at success
  cases loopRun : (forIn (declListToList ds) ([], []) (fun d acc =>
      StateT.bind (toCoreBind d) fun bindResult =>
        StateT.bind (toCoreMetaData m) fun metadata =>
          pure (.yield (Core.Statement.init bindResult.1 bindResult.2 .nondet metadata :: acc.1,
            (.fvar () bindResult.1 none : Core.Expression.Expr) :: acc.2)))) state with
  | error e => simp [loopRun] at success
  | ok loopResult =>
      obtain ⟨reversePair, afterLoop⟩ := loopResult
      obtain ⟨reverseOut, reverseExprs⟩ := reversePair
      rw [loopRun] at success
      simp only [Except.bind, Except.map] at success
      simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, Except.pure, pure, StateT.pure] at success

      injection success with pairEq
      have outEq : reverseOut.reverse = out := congrArg Prod.fst pairEq
      subst out
      intro empty
      have reversedEmpty : reverseOut.reverse = [] := by simpa using empty
      have reverseIsEmpty : reverseOut = [] := List.reverse_eq_nil_iff.mp reversedEmpty
      have sameBinder : (fun d acc => lowerOneBind m d acc) =
          (fun d acc => StateT.bind (toCoreBind d) fun bindResult =>
            StateT.bind (toCoreMetaData m) fun metadata =>
              pure (.yield (Core.Statement.init bindResult.1 bindResult.2 .nondet metadata :: acc.1,
                (.fvar () bindResult.1 none : Core.Expression.Expr) :: acc.2))) := by
        funext d acc
        rfl
      have loopSuccess : (forIn (declListToList ds) ([], []) (lowerOneBind m)) state =
          .ok ((reverseOut, reverseExprs), afterLoop) := by
        simpa only [← sameBinder] using loopRun
      exact (lowerOneBind_loop_nonempty m (declListToList ds) ([], []) state
        (reverseOut, reverseExprs) afterLoop loopSuccess (Or.inr (declListToList_ne_nil ds)))
        reverseIsEmpty


private theorem singletonAction_nonempty {α : Type} (action : TranslateM α)
    (state : TranslateState) (output : List α) (final : TranslateState)
    (success : (do let value ← action; pure [value]) state = .ok (output, final)) : output ≠ [] := by
  simp only [bind, StateT.bind, Except.bind] at success
  cases actionRun : action state with
  | error e => simp [actionRun] at success
  | ok result =>
      obtain ⟨value, next⟩ := result
      simp only [actionRun, pure, StateT.pure, Except.pure] at success
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
      simp

private theorem mapM_cons_success {α β : Type} (action : α → TranslateM β)
    (first : α) (rest : List α) (state : TranslateState)
    (results : List β) (final : TranslateState)
    (success : (first :: rest).mapM action state = .ok (results, final)) :
    ∃ (head : β) (afterHead : TranslateState) (tail : List β),
      action first state = .ok (head, afterHead) ∧
      rest.mapM action afterHead = .ok (tail, final) ∧ results = head :: tail := by
  simp only [List.mapM_cons, bind, StateT.bind, Except.bind] at success
  cases headRun : action first state with
  | error e => simp [headRun] at success
  | ok headResult =>
      obtain ⟨head, afterHead⟩ := headResult
      rw [headRun] at success
      cases tailRun : rest.mapM action afterHead with
      | error e => simp [tailRun] at success
      | ok tailResult =>
          obtain ⟨tail, afterTail⟩ := tailResult
          simp only [tailRun, pure, StateT.pure, Except.pure] at success
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
          exact ⟨head, afterHead, tail, rfl, tailRun, rfl⟩

private theorem flattenedAction_success {action : TranslateM (List (List Core.Statement))}
    {entry final : TranslateState} {target : List Core.Statement}
    (success : (do let parts ← action; pure parts.flatten) entry = .ok (target, final)) :
    ∃ parts, action entry = .ok (parts, final) ∧ target = parts.flatten := by
  simp only [bind, StateT.bind, Except.bind] at success
  cases ran : action entry with
  | error error => simp [ran] at success
  | ok result =>
    obtain ⟨parts, finalState⟩ := result
    simp only [ran, pure, StateT.pure, Except.pure] at success
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
    exact ⟨parts, rfl, rfl⟩

/-- A nonempty source block cannot lower successfully to an empty Core list. -/
theorem BlockWasLowered.nonempty (range annotation : SourceRange)
    (sourceStatements : Array (BooleDDM.Statement SourceRange))
    (target : List Core.Statement)
    (lowered : BlockWasLowered (.block range ⟨annotation, sourceStatements⟩) target)
    (nonempty : sourceStatements ≠ #[]) : target ≠ [] := by
  obtain ⟨entry, final, success⟩ := lowered
  cases listEq : sourceStatements.toList with
  | nil => exact (nonempty (Array.toList_eq_nil_iff.mp listEq)).elim
  | cons first rest =>
    rw [toCoreBlock, listEq] at success
    obtain ⟨parts, mapped, rfl⟩ := flattenedAction_success success
    obtain ⟨head, _, tail, headRun, _, rfl⟩ :=
      mapM_cons_success _ first rest entry parts final mapped
    have nonempty : head ≠ [] := by
      cases first
      all_goals
        first
        | exact lowerVarStatement_nonempty _ _ _ _ _ headRun
        | exact singletonAction_nonempty (toCoreStmt _) _ _ _ headRun
    simp only [List.flatten_cons]
    exact fun empty => nonempty (List.append_eq_nil_iff.mp empty).1

end Strata.Boole
