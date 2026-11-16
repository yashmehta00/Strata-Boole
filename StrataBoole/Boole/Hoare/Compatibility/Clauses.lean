/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all StrataBoole.Verify
import all StrataBoole.Boole.Hoare.Compile
import all StrataBoole.Boole.Hoare.Compatibility.Body
import all StrataBoole.Boole.Interp
import all Strata.Languages.Core.Procedure
import all Strata.Util.ListMap

namespace Strata.Boole.Hoare

open StrataDDM

private abbrev ClauseTerms := Boole.Expr × Bool

private def clauseTerms (isPrecondition : Bool) (elt : BooleDDM.SpecElt SourceRange) : Option ClauseTerms :=
  match elt with
  | .requires_spec _ _ free condition => if isPrecondition then some (condition, free.val.isSome) else none
  | .ensures_spec _ _ free condition => if isPrecondition then none else some (condition, free.val.isSome)
  | .modifies_spec .. => none

private abbrev RawChecks := List (String × Core.Procedure.Check)

private def IsRawClause (terms : ClauseTerms) (check : String × Core.Procedure.Check) : Prop :=
  (check.2.attr = .Free ↔ terms.2 = true) ∧
    ∃ initial final, toCoreExpr terms.1 initial = .ok (check.2.expr, final)

private def rawClauseStep (name : String) (elt : BooleDDM.SpecElt SourceRange)
    (checks : RawChecks × RawChecks) : TranslateM (ForInStep (RawChecks × RawChecks)) := do
  match elt with
  | .modifies_spec .. => pure (.yield checks)
  | .requires_spec range ⟨_, label⟩ ⟨_, free⟩ condition =>
    let md ← toCoreMetaData range
    let label ← defaultLabel range s!"{name}_requires" label
    let expr ← toCoreExpr condition
    pure (.yield ((label, ⟨expr, checkAttrOf free, md⟩) :: checks.1, checks.2))
  | .ensures_spec range ⟨_, label⟩ ⟨_, free⟩ condition =>
    let md ← toCoreMetaData range
    let label ← defaultLabel range s!"{name}_ensures" label
    let expr ← toCoreExpr condition
    pure (.yield (checks.1, (label, ⟨expr, checkAttrOf free, md⟩) :: checks.2))

private theorem rawClauseStep_records (name : String)
    (elt : BooleDDM.SpecElt SourceRange) {before : RawChecks × RawChecks}
    {initial final : TranslateState} {control : ForInStep (RawChecks × RawChecks)}
    (ran : rawClauseStep name elt before initial = .ok (control, final))
    {pres posts : List ClauseTerms}
    (pre : List.Rel₂ IsRawClause pres before.1)
    (post : List.Rel₂ IsRawClause posts before.2) :
    ∃ after, control = .yield after ∧
      List.Rel₂ IsRawClause ((clauseTerms true elt).toList ++ pres) after.1 ∧
      List.Rel₂ IsRawClause ((clauseTerms false elt).toList ++ posts) after.2 := by
  cases elt
  case' modifies_spec => exact ⟨before, (congrArg Prod.fst (Except.ok.inj ran)).symm, pre, post⟩
  case' requires_spec range label free condition => cases label; cases free
  case' ensures_spec range label free condition => cases label; cases free
  all_goals
    repeat' first
      | contradiction
      | simp only [rawClauseStep, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
      | split at ran
    have equal := (congrArg Prod.fst (Except.ok.inj ran)).symm
    refine ⟨_, equal, ?_, ?_⟩
    all_goals
      simp only [clauseTerms, Bool.false_eq_true, ite_true, ite_false,
        Option.toList_none, Option.toList_some, List.nil_append, List.singleton_append]
    all_goals first
      | exact pre
      | exact post
      | (apply List.Rel₂.cons
         · refine ⟨?_, ⟨_, _, by assumption⟩⟩
           unfold checkAttrOf
           split <;> simp_all
         · first | exact pre | exact post)

private theorem rawClauseLoop_records (name : String)
    (elts : List (BooleDDM.SpecElt SourceRange)) {before after : RawChecks × RawChecks}
    {initial final : TranslateState}
    (ran : forIn elts before (rawClauseStep name) initial = .ok (after, final))
    {pres posts : List ClauseTerms}
    (pre : List.Rel₂ IsRawClause pres before.1)
    (post : List.Rel₂ IsRawClause posts before.2) :
    List.Rel₂ IsRawClause (elts.reverse.filterMap (clauseTerms true) ++ pres) after.1 ∧
    List.Rel₂ IsRawClause (elts.reverse.filterMap (clauseTerms false) ++ posts) after.2 := by
  induction elts generalizing before initial pres posts with
  | nil =>
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj ran)
    exact ⟨pre, post⟩
  | cons elt rest ih =>
    simp only [List.forIn_cons, bind, StateT.bind, Except.bind, pure] at ran
    cases first : rawClauseStep name elt before initial with
    | error => simp [first] at ran
    | ok result =>
      obtain ⟨control, middle⟩ := result
      obtain ⟨next, rfl, newPre, newPost⟩ := rawClauseStep_records name elt first pre post
      have tail : forIn rest next (rawClauseStep name) middle = .ok (after, final) := by
        simpa [first] using ran
      obtain ⟨pre, post⟩ := ih tail newPre newPost
      constructor <;>
        simp only [List.reverse_cons, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
          List.append_assoc] <;>
        first
        | cases h : clauseTerms true elt <;> simpa [h] using pre
        | cases h : clauseTerms false elt <;> simpa [h] using post

/-- Raw lowering preserves clause order and free flags and lowers the corresponding
expression from each source clause. -/
private theorem raw_contract_records (range : SourceRange) (name : String)
    (elements : Array (BooleDDM.SpecElt SourceRange)) {initial final : TranslateState}
    {spec : Core.Procedure.Spec}
    (ran : toCoreSpecElts range name elements initial = .ok (spec, final)) :
    List.Rel₂ IsRawClause (elements.toList.filterMap (clauseTerms true)) spec.preconditions.toList ∧
    List.Rel₂ IsRawClause (elements.toList.filterMap (clauseTerms false)) spec.postconditions.toList := by
  simp only [toCoreSpecElts, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
  split at ran
  · contradiction
  · rename_i accumulated ranLoop
    have equal : _ = spec := congrArg Prod.fst (Except.ok.inj ran)
    rw [← equal]
    have loop : forIn elements.toList ([], []) (rawClauseStep name) initial = .ok accumulated := ranLoop
    obtain ⟨pre, post⟩ := rawClauseLoop_records name elements.toList loop .nil .nil
    exact ⟨by simpa [ListMap.toList] using pre.reverse, by simpa [ListMap.toList] using post.reverse⟩

private def IsSourceClause (scope : Scope) (context : ReadContext)
    (terms : ClauseTerms) (clause : Clause Expression) : Prop :=
  clause.free = terms.2 ∧
    ∃ range, boolean range terms.1 context scope = .ok (clause.condition, scope)

private def sourceClauseStep (outputs : List Binding) (elt : BooleDDM.SpecElt SourceRange)
    (before : Contract Expression) : InterpM (ForInStep (Contract Expression)) := do
  match elt with
  | .requires_spec range label free e =>
    let condition ← boolean range e { requiresOutputs := some (outputs.map Binding.name) }
    pure (.yield { before with requires := before.requires ++
      [⟨sourceLabel range label.val, free.val.isSome, condition⟩] })
  | .ensures_spec range label free e =>
    let condition ← boolean range e
    pure (.yield { before with ensures := before.ensures ++
      [⟨sourceLabel range label.val, free.val.isSome, condition⟩] })
  | .modifies_spec .. => pure (.yield before)

private theorem sourceClauseStep_records (outputs : List Binding)
    (elt : BooleDDM.SpecElt SourceRange) {before : Contract Expression}
    {state final : Scope} {control : ForInStep (Contract Expression)}
    (ran : sourceClauseStep outputs elt before state = .ok (control, final))
    {pres posts : List ClauseTerms}
    (pre : List.Rel₂ (IsSourceClause state { requiresOutputs := some (outputs.map Binding.name) })
      pres before.requires)
    (post : List.Rel₂ (IsSourceClause state {}) posts before.ensures) :
    ∃ after, control = .yield after ∧ final = state ∧
      List.Rel₂ (IsSourceClause state { requiresOutputs := some (outputs.map Binding.name) })
        (pres ++ (clauseTerms true elt).toList) after.requires ∧
      List.Rel₂ (IsSourceClause state {}) (posts ++ (clauseTerms false elt).toList) after.ensures := by
  cases elt
  case' modifies_spec =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj ran)
    exact ⟨before, rfl, rfl, by simpa [clauseTerms] using pre, by simpa [clauseTerms] using post⟩
  all_goals
    simp only [sourceClauseStep, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
    split at ran
    · contradiction
    rename_i result checked
    obtain ⟨condition, next⟩ := result
    have stable := boolean_readOnly _ _ _ _ _ _ checked
    subst next
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj ran)
    refine ⟨_, rfl, rfl, ?_, ?_⟩
  all_goals
    simp only [clauseTerms, Bool.false_eq_true, ite_true, ite_false, Option.toList_some,
      Option.toList_none, List.append_nil]
  all_goals first
    | exact pre
    | exact post
    | (apply List.Rel₂.append
       · first | exact pre | exact post
       · exact .cons ⟨rfl, _, checked⟩ .nil)

private theorem sourceClauseLoop_records (outputs : List Binding)
    (elts : List (BooleDDM.SpecElt SourceRange)) {before after : Contract Expression}
    {initial final : Scope}
    (ran : forIn elts before (sourceClauseStep outputs) initial = .ok (after, final))
    {pres posts : List ClauseTerms}
    (pre : List.Rel₂ (IsSourceClause initial { requiresOutputs := some (outputs.map Binding.name) })
      pres before.requires)
    (post : List.Rel₂ (IsSourceClause initial {}) posts before.ensures) :
    final = initial ∧
    List.Rel₂ (IsSourceClause initial { requiresOutputs := some (outputs.map Binding.name) })
      (pres ++ elts.filterMap (clauseTerms true)) after.requires ∧
    List.Rel₂ (IsSourceClause initial {}) (posts ++ elts.filterMap (clauseTerms false)) after.ensures := by
  induction elts generalizing before initial pres posts with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj ran)
    exact ⟨rfl, by simpa using pre, by simpa using post⟩
  | cons elt rest ih =>
    simp only [List.forIn_cons, bind, StateT.bind, Except.bind, pure] at ran
    cases first : sourceClauseStep outputs elt before initial with
    | error => simp [first] at ran
    | ok result =>
      obtain ⟨control, middle⟩ := result
      obtain ⟨next, rfl, rfl, newPre, newPost⟩ := sourceClauseStep_records outputs elt first pre post
      have tail : forIn rest next (sourceClauseStep outputs) middle = .ok (after, final) := by
        simpa [first] using ran
      obtain ⟨stable, pre, post⟩ := ih tail newPre newPost
      refine ⟨stable, ?_, ?_⟩
      · cases h : clauseTerms true elt <;> simpa [h, List.append_assoc] using pre
      · cases h : clauseTerms false elt <;> simpa [h, List.append_assoc] using post

/-- The Hoare compiler builds its condition functions in source clause order. -/
private theorem source_contract_records
    (range : SourceRange) (elements : Ann (Array (BooleDDM.SpecElt SourceRange)) SourceRange)
    (outputs : List Binding) {initial final : Scope} {spec : Contract Expression}
    (ran : contract (some (.spec_mk range elements)) outputs initial = .ok (spec, final)) :
    List.Rel₂ (IsSourceClause final { requiresOutputs := some (outputs.map Binding.name) })
      (elements.val.toList.filterMap (clauseTerms true)) spec.requires ∧
    List.Rel₂ (IsSourceClause final {})
      (elements.val.toList.filterMap (clauseTerms false)) spec.ensures := by
  simp only [contract, ← Array.forIn_toList, bind, StateT.bind, Except.bind, pure, StateT.pure,
    Except.pure, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet] at ran
  split at ran
  · contradiction
  · rename_i modifies collected
    split at ran
    · contradiction
    · rename_i conditions compiled
      have sameSpec : conditions.1 = spec := congrArg Prod.fst (Except.ok.inj ran)
      have sameScope : conditions.2 = final := congrArg Prod.snd (Except.ok.inj ran)
      subst spec
      subst final
      have loop : forIn elements.val.toList { modifies := modifies.1 }
          (sourceClauseStep outputs) { modifies.2 with modifies := modifies.1 } =
            .ok conditions := compiled
      obtain ⟨same, pre, post⟩ := sourceClauseLoop_records outputs elements.val.toList loop .nil .nil
      exact ⟨same.symm ▸ pre, same.symm ▸ post⟩

private theorem pair_clauses {terms : List ClauseTerms} {source : List (Clause Expression)}
    {raw : RawChecks} {scope : Scope} {context : ReadContext}
    (compiled : List.Rel₂ (IsSourceClause scope context) terms source)
    (lowered : List.Rel₂ IsRawClause terms raw) :
    List.Rel₂ (fun clause check => ∃ term,
      IsSourceClause scope context term clause ∧ IsRawClause term check) source raw := by
  induction compiled generalizing raw with
  | nil =>
    cases lowered
    exact .nil
  | cons compiled tail ih =>
    cases lowered with
    | cons lowered rest =>
      exact .cons ⟨_, compiled, lowered⟩ (ih rest)

/-- Pair the clauses produced by the two compilers through their common Boole
syntax. The pair retains the original expression runs and free flag. -/
private theorem contract_clause_origins
    (range procedureRange : SourceRange) (name : String)
    (elements : Ann (Array (BooleDDM.SpecElt SourceRange)) SourceRange)
    (outputs : List Binding) {entry final : Scope} {source : Contract Expression}
    {rawEntry rawFinal : TranslateState} {raw : Core.Procedure.Spec}
    (compiled : contract (some (.spec_mk range elements)) outputs entry = .ok (source, final))
    (lowered : toCoreSpec procedureRange name (some (.spec_mk range elements)) rawEntry =
      .ok (raw, rawFinal)) :
    List.Rel₂ (fun clause check => ∃ term,
      IsSourceClause final { requiresOutputs := some (outputs.map Binding.name) } term clause ∧
        IsRawClause term check) source.requires raw.preconditions.toList ∧
    List.Rel₂ (fun clause check => ∃ term,
      IsSourceClause final {} term clause ∧ IsRawClause term check)
        source.ensures raw.postconditions.toList := by
  obtain ⟨pre, post⟩ := source_contract_records range elements outputs compiled
  obtain ⟨rawPre, rawPost⟩ := raw_contract_records procedureRange name elements.val
    (by simpa only [toCoreSpec] using lowered)
  exact ⟨pair_clauses pre rawPre, pair_clauses post rawPost⟩

end Strata.Boole.Hoare
