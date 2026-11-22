/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.Iteration
public import StrataBoole.Boole.Interpretation.Denotational.Adequacy.Statements
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Statements
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.SourceState
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.SourceInterface
import all StrataBoole.Boole.Interpretation.Denotational.Adequacy.Lowering
import all StrataBoole.Boole.Interpretation.Legacy.Interp
import all StrataBoole.Boole.Interpretation.Source
import all StrataBoole.Boole.Interpretation.Legacy.Semantics

public section
namespace Strata.Boole

private theorem interpExpr_readOnly (I : Interpretation) (expr : Boole.Expr) :
    ReadOnly (interpExpr I expr) := by
  cases expr
  all_goals rw [interpExpr.eq_def]
  all_goals try simp only [interpTypedUnary, interpTypedBinary]
  all_goals
    repeat' first
      | exact readOnly_pure _
      | exact readOnly_reject _ _
      | exact readOnly_get
      | exact sourceSort_readOnly _
      | exact interpExpr_readOnly I _
      | apply ReadOnly.bind
      | dsimp only
      | (split <;> skip)
      | (intro value)
termination_by sizeOf expr
decreasing_by all_goals simp_all <;> omega

private def Computation.AvoidsLocal (computation : Computation α)
    (name : String) : Prop :=
  ∀ initial outcome, initial.locals.lookup name = none → computation.run initial outcome →
    outcome.state.locals.lookup name = none

private theorem Computation.avoidsLocal_pure (value : α) (name : String) :
    (Computation.pure value).AvoidsLocal name := by
  intro initial outcome absent ran
  obtain rfl := ran
  exact absent

private theorem Computation.avoidsLocal_bind {first : Computation α}
    {next : α → Computation β} {name : String}
    (firstAvoids : first.AvoidsLocal name)
    (nextAvoids : ∀ value, (next value).AvoidsLocal name) :
    (first >>= next).AvoidsLocal name := by
  intro initial outcome absent ran
  rcases (Computation.run_bind first next initial outcome).mp ran with
    ⟨value, middle, firstRan, nextRan⟩ | ⟨label, final, firstRan, rfl⟩ |
    ⟨label, final, firstRan, rfl⟩ | ⟨reason, final, firstRan, rfl⟩
  · exact nextAvoids value middle _ (firstAvoids initial _ absent firstRan) nextRan
  · exact firstAvoids initial _ absent firstRan
  · exact firstAvoids initial _ absent firstRan
  · exact firstAvoids initial _ absent firstRan

private theorem Computation.avoidsLocal_scope {body : Computation Unit}
    {name : String} :
    (Computation.scope body).AvoidsLocal name := by
  intro initial outcome absent ran
  obtain ⟨inner, bodyRan, rfl⟩ := ran
  cases inner <;> simp only [Outcome.mapState, Outcome.state]
  all_goals
    simp only [Store.lookup_restrict]
    simp [absent]

private theorem Computation.avoidsLocal_block {body : Computation Unit}
    {label name : String} (avoids : body.AvoidsLocal name) :
    (Computation.block label body).AvoidsLocal name := by
  intro initial outcome absent ran
  obtain ⟨inner, bodyRan, rfl⟩ := ran
  cases inner with
  | returned value final => exact avoids initial _ absent bodyRan
  | exited found final =>
      have noLocal := avoids initial (.exited found final) absent bodyRan
      by_cases same : found = label
      · subst found
        simp [Outcome.state] at noLocal ⊢
        exact noLocal
      · have different : (found == label) = false := beq_eq_false_iff_ne.mpr same
        simp [different, Outcome.state] at noLocal ⊢
        exact noLocal
  | assertionFailed found final => exact avoids initial _ absent bodyRan
  | stuck reason final => exact avoids initial _ absent bodyRan

private theorem Computation.avoidsLocal_declare (binding : Binding) (initializer : Option Expression)
    (name : String) (different : binding.name ≠ name) :
    (Computation.declare binding initializer).AvoidsLocal name := by
  intro initial outcome absent ran
  unfold Computation.declare StatementSemantics.declare at ran
  rw [Computation.run_get_bind] at ran
  split at ran
  · obtain rfl := ran
    exact absent
  · have write : ∀ value, (if value.sort ≠ binding.sort then Computation.stuck .wrongType
        else Computation.put { initial with locals := initial.locals ++ [(binding.name, value)] }).run
        initial outcome → outcome.state.locals.lookup name = none := by
      intro value wrote
      split at wrote
      · obtain rfl := wrote
        exact absent
      · obtain rfl := wrote
        change (initial.locals ++ [(binding.name, value)]).lookup name = none
        simp [Store.lookup_append, Store.lookup_cons, absent, different]
    cases initializer with
    | none =>
      simp only [Computation.run_bind, Computation.choose, reduceCtorEq, Outcome.returned.injEq,
        and_false, exists_false, false_and, or_false] at ran
      obtain ⟨value, middle, ⟨v, _, rfl, rfl⟩, rest⟩ := ran
      exact write value rest
    | some expression =>
      rw [Computation.run_evaluate_bind] at ran
      cases evaluated : expression initial with
      | error reason =>
        rw [evaluated] at ran
        obtain rfl := ran
        exact absent
      | ok value => rw [evaluated] at ran; exact write value ran

private theorem Computation.avoidsLocal_exit (label name : String) :
    (Computation.exit label).AvoidsLocal name := by
  intro initial outcome absent ran
  obtain rfl := ran
  exact absent

private theorem Computation.avoidsLocal_assign (reference : Variable) (expression : Expression)
    (name : String) : (Computation.assign reference expression).AvoidsLocal name := by
  intro initial outcome absent ran
  unfold Computation.assign StatementSemantics.assign at ran
  rw [Computation.run_get_bind, Computation.run_evaluate_bind] at ran
  unfold Expression.read at ran
  cases slot : initial.lookup reference with
  | none =>
    simp only [slot] at ran
    obtain rfl := ran
    exact absent
  | some previous =>
    simp only [slot] at ran
    rw [Computation.run_evaluate_bind] at ran
    cases evaluated : expression initial with
    | error error =>
      rw [evaluated] at ran
      obtain rfl := ran
      exact absent
    | ok value =>
      rw [evaluated] at ran
      change (if previous.sort ≠ value.sort then Computation.stuck .wrongType
        else Computation.put (initial.update reference value)).run initial outcome at ran
      split at ran
      · obtain rfl := ran
        exact absent
      · obtain rfl := ran
        cases reference with
        | global => exact absent
        | «local» target =>
          by_cases same : name = target
          · subst target
            change initial.locals.lookup name = some previous at slot
            rw [absent] at slot
            contradiction
          · change (initial.locals.update target value).lookup name = none
            rw [Store.lookup_update_other _ _ _ _ same]
            exact absent

private theorem Computation.avoidsLocal_test (condition : Option Expression) (name : String) :
    (Computation.test condition).AvoidsLocal name := by
  intro initial outcome absent ran
  cases condition with
  | none => rcases ran with rfl | rfl <;> exact absent
  | some expression =>
    unfold Computation.test at ran
    rw [Computation.run_evaluate_bind] at ran
    cases evaluated : expression initial with
    | error error =>
      rw [evaluated] at ran
      obtain rfl := ran
      exact absent
    | ok value =>
      rw [evaluated] at ran
      dsimp only at ran
      split at ran <;> obtain rfl := ran <;> exact absent

private theorem Computation.avoidsLocal_loop {guard : Computation Bool}
    {body : Computation Unit} {name : String}
    (guardAvoids : guard.AvoidsLocal name) (bodyAvoids : body.AvoidsLocal name) :
    (Computation.loop guard body).AvoidsLocal name := by
  intro initial outcome absent ran
  rw [Computation.loop_iff_iteration] at ran
  induction ran with
  | next tested ran _ ih => exact ih (bodyAvoids _ _ (guardAvoids _ _ absent tested) ran)
  | bodyExit tested ran | bodyFailure tested ran | bodyStuck tested ran =>
    exact bodyAvoids _ _ (guardAvoids _ _ absent tested) ran
  | stop tested | guardExit tested | guardFailure tested | guardStuck tested =>
    exact guardAvoids _ _ absent tested

private theorem Computation.avoidsLocal_assertion (label : String) (condition : Expression) (name : String) :
    (Computation.assertion label condition).AvoidsLocal name := by
  apply Computation.avoidsLocal_bind (Computation.avoidsLocal_test (some condition) _)
  intro b
  cases b
  · intro _ _ absent ran
    obtain rfl := ran
    exact absent
  · exact Computation.avoidsLocal_pure _ _

private theorem Computation.avoidsLocal_assumption (condition : Expression) (name : String) :
    (Computation.assumption condition).AvoidsLocal name := by
  apply Computation.avoidsLocal_bind (Computation.avoidsLocal_test (some condition) _)
  intro b
  cases b
  · exact fun _ _ _ impossible => False.elim impossible
  · exact Computation.avoidsLocal_pure _ _

private theorem Computation.avoidsLocal_choose (sort : ValueType) (name : String) :
    (Computation.choose sort).AvoidsLocal name := by
  rintro state _ absent ⟨_, _, rfl⟩
  exact absent

private def ForbiddenLocal (scope : Scope) (name : String) : Prop :=
  name.contains ' ' = true ∨ name ∈ scope.globals.map Binding.name

private theorem addLocal_fresh {range : SourceRange} {name : String} {ty : Boole.Type}
    {entry final : Scope} {binding : Binding}
    (added : addLocal range name ty entry = .ok (binding, final)) :
    final.globals = entry.globals ∧ ∀ forbidden, ForbiddenLocal entry forbidden → binding.name ≠ forbidden := by
  unfold addLocal at added
  obtain ⟨sort, middle, resolved, addedRest⟩ := split_run added
  have beforeFresh := sourceSort_readOnly ty _ _ _ resolved
  subst middle
  obtain ⟨trivialValue, afterFresh, checked, installed⟩ := split_run addedRest
  cases trivialValue
  obtain ⟨noSpaces, unused, afterEq⟩ := fresh_names checked
  subst afterFresh
  have bindingEq : (⟨name, sort⟩ : Binding) = binding := congrArg Prod.fst (Except.ok.inj installed)
  have finalEq : { entry with locals := entry.locals ++ [⟨name, sort⟩] } = final :=
    congrArg Prod.snd (Except.ok.inj installed)
  subst binding
  subst final
  refine ⟨rfl, ?_⟩
  intro forbidden disallowed same
  change name = forbidden at same
  subst forbidden
  rcases disallowed with space | global
  · simp_all
  · exact unused (by simp only [List.map_append, List.mem_append]; exact Or.inr global)

private theorem declarations_avoid (declarations : List (BooleDDM.Bind SourceRange))
    (range : SourceRange) (entry final : Scope) (body : Computation Unit)
    (success : (forIn declarations (denotation.skip) (fun (declaration : BooleDDM.Bind SourceRange) (result : Computation Unit) => do
      let .bind_mk _ name _ ty := declaration
      let binding ← addLocal range name.val ty
      pure (.yield (denotation.seq result (denotation.declare binding none)))))
      entry = .ok (body, final)) :
    final.globals = entry.globals ∧ ∀ name, ForbiddenLocal entry name → body.AvoidsLocal name := by
  apply forIn_invariant _ _ (fun scope result => scope.globals = entry.globals ∧
    ∀ name, ForbiddenLocal entry name → result.AvoidsLocal name) _ _ _ _ _ ?_ success
  · intro declaration before state control next kept ran
    cases declaration
    simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
    split at ran
    · contradiction
    · rename_i pair added
      have equal := Except.ok.inj ran
      obtain ⟨stateEq, different⟩ := addLocal_fresh added
      refine ⟨(congrArg (fun result : _ × Scope => result.2.globals) equal).symm.trans
        (stateEq.trans kept.1), ?_⟩
      have bodyEq := congrArg (fun result => result.1.value) equal
      intro name forbidden
      rw [← bodyEq]
      change (before >>= fun _ => Computation.declare pair.1 none).AvoidsLocal name
      have there : ForbiddenLocal state name := by simpa [ForbiddenLocal, kept.1] using forbidden
      exact Computation.avoidsLocal_bind (kept.2 name forbidden)
        (fun _ => Computation.avoidsLocal_declare _ _ _ (different _ there))
  · exact ⟨rfl, fun name _ => Computation.avoidsLocal_pure () name⟩

private theorem condition_readOnly (I : Interpretation) (guard : BooleDDM.ExprOrNondet SourceRange) :
    ReadOnly (condition I guard) := by
  cases guard
  · exact (interpExpr_readOnly I _).bind (fun result => readOnly_pure (some result))
  · exact readOnly_pure none

private theorem checkInvariants_readOnly (I : Interpretation) (invariants : BooleDDM.Invariants SourceRange) :
    ReadOnly (checkInvariants I invariants) := by
  induction invariants with
  | nilInvariants => exact readOnly_pure ()
  | consInvariants _ _ expression rest ih =>
    exact (interpExpr_readOnly I expression).bind (fun _ => ih)

private theorem resolveVariable_readOnly (range : SourceRange) (name : String) (writing : Bool) :
    ReadOnly (resolveVariable range name writing) := by
  unfold resolveVariable
  apply ReadOnly.bind readOnly_get
  intro scope
  repeat' first
    | exact readOnly_pure _
    | exact readOnly_reject _ _
    | (split <;> skip)

private theorem interpBlock_avoidsLocal (block : BooleDDM.Block SourceRange)
    (entry final : Scope) (body : Computation Unit)
    (success : interpBlock denotation block entry = .ok (body, final)) :
    final = entry ∧ ∀ name, body.AvoidsLocal name := by
  obtain ⟨range, ⟨_, statements⟩⟩ := block
  rw [interpBlock] at success
  refine ⟨withScope_restores success, ?_⟩
  obtain ⟨_, inner⟩ := withScope_success success
  simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at inner
  split at inner
  · contradiction
  · have equal : Computation.scope _ = body := congrArg Prod.fst (Except.ok.inj inner)
    rw [← equal]
    exact fun _ => Computation.avoidsLocal_scope

private theorem nestedBlock_avoidsLocal (label : String) (block : BooleDDM.Block SourceRange)
    (entry final : Scope) (body : Computation Unit)
    (success : (withScope do
      modify fun scope => { scope with labels := label :: scope.labels }
      interpBlock denotation block) entry = .ok (body, final)) :
    final = entry ∧ ∀ name, body.AvoidsLocal name := by
  refine ⟨withScope_restores success, ?_⟩
  obtain ⟨_, ran⟩ := withScope_success success
  simp only [modify, modifyGet, MonadStateOf.modifyGet] at ran
  exact (interpBlock_avoidsLocal _ _ _ _ ran).2

set_option maxHeartbeats 800000 in
private theorem interpStmt_avoidsLocal (statement : BooleDDM.Statement SourceRange)
    (entry final : Scope) (body : Computation Unit)
    (success : interpStmt denotation statement entry = .ok (body, final)) :
    final.globals = entry.globals ∧ ∀ name, ForbiddenLocal entry name → body.AvoidsLocal name := by
  have stableExpr (expression : Boole.Expr) (a : Scope) (p : Expression × Scope)
      (ran : interpExpr denotation expression a = .ok p) : p.2 = a :=
    interpExpr_readOnly _ _ _ _ _ ran
  have stableGuard (guard : BooleDDM.ExprOrNondet SourceRange) (a : Scope) (p : Option Expression × Scope)
      (ran : condition denotation guard a = .ok p) : p.2 = a :=
    condition_readOnly _ _ _ _ _ ran
  have stableInvariants (invariants : BooleDDM.Invariants SourceRange) (a : Scope) (p : Unit × Scope)
      (ran : checkInvariants denotation invariants a = .ok p) : p.2 = a :=
    checkInvariants_readOnly _ _ _ _ _ ran
  have stableVar (range : SourceRange) (name : String) (writing : Bool) (a : Scope)
      (p : (Variable × ValueType) × Scope)
      (ran : resolveVariable range name writing a = .ok p) : p.2 = a :=
    resolveVariable_readOnly _ _ _ _ _ _ ran
  have stableBlock (block : BooleDDM.Block SourceRange) (a : Scope)
      (p : Computation Unit × Scope)
      (ran : interpBlock denotation block a = .ok p) : p.2 = a :=
    (interpBlock_avoidsLocal _ _ _ _ ran).1
  have stableLocal (range : SourceRange) (name : String) (ty : Boole.Type)
      (a : Scope) (p : Binding × Scope) (ran : addLocal range name ty a = .ok p) :
      p.2.globals = a.globals ∧ ∀ slot, ForbiddenLocal a slot → p.1.name ≠ slot :=
    addLocal_fresh ran
  cases statement
  case' assign _ _ _ lhs _ => cases lhs
  case' if_statement _ _ _ _ otherwise => cases otherwise
  all_goals rw [interpStmt.eq_def] at success
  case' while_statement _ _ _ decreases _ _ =>
    obtain ⟨_, measure⟩ := decreases
    cases measure
    case' some measure => cases measure
  case' varStatement =>
    first | exact declarations_avoid _ _ _ _ _ success | skip
  all_goals
    repeat' first
      | contradiction
      | simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
          get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet, MonadStateOf.modifyGet,
          reject, throw, throwThe, MonadExceptOf.throw] at success
      | split at success
  all_goals
    have same : _ = body := congrArg Prod.fst (Except.ok.inj success)
    have finalEq : _ = final := congrArg Prod.snd (Except.ok.inj success)
    try simp only [denotation] at same
    rw [← same, ← finalEq]
  case' h_2 =>
    first | exact declarations_avoid _ _ _ _ _ (by assumption) | skip
  all_goals
    constructor
    · first
      | rfl
      | exact (declarations_avoid _ _ _ _ _ (by assumption)).1
      | (rename_i ran; exact congrArg Scope.globals (withScope_restores ran))
      | grind only
    · intro name forbidden
      first
      | exact Computation.avoidsLocal_assign _ _ _
      | exact Computation.avoidsLocal_bind (Computation.avoidsLocal_choose _ _)
          (fun _ => Computation.avoidsLocal_assign _ _ _)
      | exact Computation.avoidsLocal_assertion _ _ _
      | exact Computation.avoidsLocal_assumption _ _
      | exact Computation.avoidsLocal_exit _ _
      | (apply Computation.avoidsLocal_declare
         grind only)
      | (apply Computation.avoidsLocal_loop (Computation.avoidsLocal_test _ _)
         exact (interpBlock_avoidsLocal _ _ _ _ (by assumption)).2 _)
      | (apply Computation.avoidsLocal_bind (Computation.avoidsLocal_test _ _)
         intro taken
         cases taken
         · first | exact Computation.avoidsLocal_pure _ _
                 | exact (interpBlock_avoidsLocal _ _ _ _ (by assumption)).2 _
         · exact (interpBlock_avoidsLocal _ _ _ _ (by assumption)).2 _)
      | (apply Computation.avoidsLocal_block
         exact (nestedBlock_avoidsLocal _ _ _ _ _ (by assumption)).2 _)
      | exact (declarations_avoid _ _ _ _ _ (by assumption)).2 name forbidden

/-- A successfully interpreted list of statements cannot introduce a local
whose name belongs to a visible global or to Core's space-containing namespace. -/
theorem interpStmts_no_new_reserved_local (statements : List (BooleDDM.Statement SourceRange))
    (entry final : Scope) (body : Computation Unit)
    (interpreted : interpStmts denotation statements entry = .ok (body, final))
    (name : String) (reserved : name.contains ' ' = true ∨ name ∈ entry.globals.map Binding.name)
    (initial : State) (outcome : Outcome Unit)
    (absent : initial.locals.lookup name = none) (ran : body.run initial outcome) :
    outcome.state.locals.lookup name = none := by
  induction statements generalizing entry body initial outcome with
  | nil =>
    rw [interpStmts] at interpreted
    obtain rfl := congrArg Prod.fst (Except.ok.inj interpreted)
    exact Computation.avoidsLocal_pure () name initial outcome absent ran
  | cons statement rest ih =>
    rw [interpStmts] at interpreted
    obtain ⟨first, middle, headRan, continued⟩ := split_run interpreted
    obtain ⟨remaining, endScope, tailRan, returned⟩ := split_run continued
    obtain ⟨rfl, sameScope⟩ := Prod.mk.inj (Except.ok.inj returned)
    subst endScope
    obtain ⟨kept, avoids⟩ := interpStmt_avoidsLocal _ _ _ _ headRan
    exact Computation.avoidsLocal_bind (avoids name reserved)
      (fun _ next result missing step => ih middle remaining tailRan (by simpa [kept] using reserved)
        next result missing step) initial outcome absent ran

end Strata.Boole
