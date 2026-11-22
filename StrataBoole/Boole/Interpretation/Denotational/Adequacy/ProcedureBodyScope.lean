/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.SourceInterface
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.SourceInterface
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.SourceFreshness
import all StrataBoole.Boole.Interpretation.Legacy.Interp
import all StrataBoole.Boole.Interpretation.Source
import all StrataBoole.Boole.Interpretation.Legacy.Semantics

public section
namespace Strata.Boole
open StrataDDM

private theorem forIn_preservesScope {α β : Type} (items : List α)
    (step : α → β → InterpM (ForInStep β))
    (stepPreserves : ∀ item before state control after,
      step item before state = .ok (control, after) → after = state)
    (before : β) (entry final : Scope) (result : β)
    (ran : forIn items before step entry = .ok (result, final)) : final = entry := by
  induction items generalizing before entry with
  | nil => exact (congrArg Prod.snd (Except.ok.inj ran)).symm
  | cons head tail ih =>
      simp only [List.forIn_cons, bind, StateT.bind, Except.bind, pure] at ran
      cases first : step head before entry with
      | error error => simp [first] at ran
      | ok pair =>
          obtain ⟨control, middle⟩ := pair
          have same := stepPreserves head before entry control middle first
          subst middle
          cases control with
          | done value =>
              simp only [first] at ran
              change Except.ok (value, entry) = Except.ok (result, final) at ran
              exact (congrArg Prod.snd (Except.ok.inj ran)).symm
          | yield next => exact ih next entry (by simpa [first] using ran)

private def modifiedNameStep (I : Interpretation) (range : SourceRange) (name : StrataDDM.Ann String SourceRange)
    (before : Contract I.Expression) : InterpM (ForInStep (Contract I.Expression)) := do
  if (findBinding name.val (← (get : InterpM Scope)).globals).isNone then
    reject range s!"Unknown modified global '{name.val}'"
  if !before.modifies.contains name.val then
    pure (.yield { before with modifies := before.modifies ++ [name.val] })
  else pure (.yield before)

private theorem modifiedNameStep_preservesScope (I : Interpretation) (range : SourceRange)
    (name : StrataDDM.Ann String SourceRange) (before : Contract I.Expression)
    (state : Scope) (control : ForInStep (Contract I.Expression)) (after : Scope)
    (ran : modifiedNameStep I range name before state = .ok (control, after)) : after = state := by
  unfold modifiedNameStep at ran
  simp only [bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, Except.pure, reject, throw, throwThe, MonadExceptOf.throw,
    Function.comp_apply, StateT.lift, Functor.map, Except.map] at ran
  repeat' first
    | contradiction
    | exact (congrArg Prod.snd (Except.ok.inj ran)).symm
    | split at ran

/-- Successful contract interpretation preserves the complete lexical scope. -/
theorem interpContract_preservesScope (I : Interpretation)
    (specification : Option (BooleDDM.Spec SourceRange)) (entry final : Scope)
    (contract : Contract I.Expression)
    (success : interpContract I specification entry = .ok (contract, final)) :
    final = entry := by
  cases specification with
  | none =>
      unfold interpContract at success
      simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at success
      exact (congrArg Prod.snd (Except.ok.inj success)).symm
  | some spec =>
      cases spec with
      | spec_mk range elements =>
          unfold interpContract at success
          simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at success
          split at success
          · contradiction
          · rename_i result loop
            rw [← Array.toArray_toList (xs := elements.val), List.forIn_toArray] at loop
            have resultFinal : result.2 = final :=
              congrArg Prod.snd (Except.ok.inj success)
            let step : BooleDDM.SpecElt SourceRange → Contract I.Expression →
                InterpM (ForInStep (Contract I.Expression)) := fun element before =>
              match element with
              | .modifies_spec range names => do
                  let updated ← forIn names.val before (modifiedNameStep I range)
                  pure (.yield updated)
              | .requires_spec range label free expression => do
                  let clause ← interpExpr I expression
                  pure (.yield { before with requires := before.requires ++
                    [⟨sourceLabel range label.val, free.val.isSome, clause⟩] })
              | .ensures_spec range label free expression => do
                  let clause ← interpExpr I expression
                  pure (.yield { before with ensures := before.ensures ++
                    [⟨sourceLabel range label.val, free.val.isSome, clause⟩] })
            have loopPair : (forIn elements.val.toList ({} : Contract I.Expression) step) entry =
                .ok (result.1, result.2) := by
              cases result with
              | mk accumulator last => change forIn elements.val.toList ({} : Contract I.Expression) step entry = .ok (accumulator, last) at loop; exact loop
            have preserved : result.2 = entry := by
              apply forIn_preservesScope elements.val.toList step ?_ {} entry result.2 result.1 loopPair
              intro element before state control after ran
              cases element with
              | modifies_spec range names =>
                  simp only [step, bind, StateT.bind, Except.bind, pure, StateT.pure,
                    Except.pure] at ran
                  cases inner : forIn names.val before (modifiedNameStep I range) state with
                  | error error => simp [inner] at ran
                  | ok pair =>
                      obtain ⟨updated, afterInner⟩ := pair
                      have innerRun : forIn names.val before (modifiedNameStep I range) state =
                          .ok (updated, afterInner) := inner
                      have listRun : forIn names.val.toList before (modifiedNameStep I range) state =
                          .ok (updated, afterInner) := by
                        rw [← (Array.toArray_toList (xs := names.val)), List.forIn_toArray] at innerRun
                        exact innerRun
                      have stable := forIn_preservesScope names.val.toList
                        (modifiedNameStep I range) (fun n acc s c t h =>
                          modifiedNameStep_preservesScope I range n acc s c t h)
                        before state afterInner updated listRun
                      simp only [inner] at ran
                      have fields := Except.ok.inj ran
                      exact (congrArg Prod.snd fields).symm.trans stable
              | requires_spec range label free expression =>
                  cases exprRun : interpExpr I expression state with
                  | error error => simp [step, bind, StateT.bind, Except.bind, exprRun] at ran
                  | ok pair =>
                      obtain ⟨value, afterExpr⟩ := pair
                      simp only [step, bind, StateT.bind, Except.bind, exprRun, pure, StateT.pure, Except.pure] at ran
                      have fields := Except.ok.inj ran
                      exact (congrArg Prod.snd fields).symm.trans
                        (interpExpr_readOnly _ _ _ _ _ exprRun)
              | ensures_spec range label free expression =>
                  cases exprRun : interpExpr I expression state with
                  | error error => simp [step, bind, StateT.bind, Except.bind, exprRun] at ran
                  | ok pair =>
                      obtain ⟨value, afterExpr⟩ := pair
                      simp only [step, bind, StateT.bind, Except.bind, exprRun, pure, StateT.pure, Except.pure] at ran
                      have fields := Except.ok.inj ran
                      exact (congrArg Prod.snd fields).symm.trans
                        (interpExpr_readOnly _ _ _ _ _ exprRun)
            exact resultFinal.symm.trans preserved

/-- The block starts with the procedure formals in scope. The contract
traversal leaves those slots unchanged and supplies the modifies list. -/
theorem interpProc_body_scope {I : Interpretation} {range : SourceRange}
    {name : String} {types : Option (BooleDDM.TypeArgs SourceRange)}
    {parameters : BooleDDM.Bindings SourceRange} {outputs : Option (BooleDDM.MonoDeclList SourceRange)}
    {specification : Option (BooleDDM.Spec SourceRange)} {block : BooleDDM.Block SourceRange}
    {initial final : Scope} {procedure : InterpProcedure I.Expression I.Statement}
    (distinct : ((initial.globals ++ initial.locals).map Binding.name).Nodup)
    (noSpaces : ∀ b ∈ initial.globals ++ initial.locals, b.name.contains ' ' = false)
    (success : interpProc I range name types parameters outputs specification (some block) initial =
      .ok (procedure, final)) :
    ∃ bodyEntry bodyFinal body,
      interpBlock I block bodyEntry = .ok (body, bodyFinal) ∧
      procedure.body = I.block name body ∧
      bodyEntry.globals = initial.globals ∧
      bodyEntry.locals = initial.locals ++ procedure.inputs ++ procedure.outputs ∧
      bodyEntry.modifies = procedure.contract.modifies ∧ bodyEntry.labels = [name] := by
  have valid : ValidNames (initial.globals ++ initial.locals) := ⟨distinct, noSpaces⟩
  unfold interpProc at success
  obtain ⟨_, ran⟩ := withScope_success success
  cases types with
  | some => contradiction
  | none =>
    simp only [Option.isSome, Bool.false_eq_true, ite_false] at ran
    obtain ⟨ins, afterInputs, readInputs, ran⟩ := split_run ran
    obtain ⟨inputGlobals, inputLocals, validInputs⟩ :=
      inputBindings_names parameters _ _ _ valid readInputs
    cases outputs
    all_goals
      obtain ⟨outs, afterOutputs, readOutputs, ran⟩ := split_run ran
      have outputFacts : afterOutputs.globals = afterInputs.globals ∧
          afterOutputs.locals = afterInputs.locals ++ outs ∧
          ValidNames (afterOutputs.globals ++ afterOutputs.locals) := by
        first
        | exact addsLocals_none _ _ _ validInputs readOutputs
        | exact outputBindings_names _ _ _ _ validInputs readOutputs
      obtain ⟨outputGlobals, outputLocals, _⟩ := outputFacts
      obtain ⟨contract, afterContract, readContract, ran⟩ := split_run ran
      have same := interpContract_preservesScope I specification afterOutputs afterContract contract readContract
      subst afterContract
      let bodyEntry : Scope := { afterOutputs with modifies := contract.modifies, labels := [name] }
      have entryEq : bodyEntry = { afterOutputs with modifies := contract.modifies, labels := [name] } := rfl
      simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
      rw [← entryEq] at ran
      cases bodyRan : interpBlock I block bodyEntry with
      | error => simp [bodyRan] at ran
      | ok result =>
        obtain ⟨body, bodyFinal⟩ := result
        simp only [bodyRan] at ran
        have equals : (⟨name, ins, outs, contract, I.block name body⟩ :
            InterpProcedure I.Expression I.Statement) = procedure :=
          congrArg Prod.fst (Except.ok.inj ran)
        subst procedure
        exact ⟨bodyEntry, bodyFinal, body, bodyRan, rfl, outputGlobals.trans inputGlobals,
          outputLocals.trans (congrArg (· ++ outs) inputLocals), rfl, rfl⟩

end Strata.Boole
