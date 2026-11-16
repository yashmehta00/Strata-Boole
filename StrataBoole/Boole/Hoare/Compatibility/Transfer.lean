/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Hoare.Compatibility.Entry
public import Strata.Languages.Core.Logic.ContractToHoareTripleProps
import all StrataBoole.Boole.Hoare.Rules
import all StrataBoole.Boole.Runtime
import Strata.DL.Lambda.LExprDenoteEvalProps

public section

namespace Strata.Boole.Hoare

open Core.Logic Imperative

/-- Lift a predicate on Boole states to Core environments. The relation can
ignore output slots that have yet to be written and Core-only bindings. -/
@[expose] def Lift (rel : State → Env Core.Expression → Prop) (P : Assertion)
    (env : Env Core.Expression) : Prop :=
  ∃ state, rel state env ∧ P state

section
variable {π : String → Option Core.Procedure} {params : InitEnvWFParams}
variable {factory : Lambda.Factory Core.CoreLParams}
variable {entry final : State → Env Core.Expression → Prop}

private theorem restrict_self (store : Store) : store.restrict store = store := by
  apply List.filter_eq_self.mpr
  intro pair member
  have present : (store.lookup pair.1).isSome = true := by
    induction store with
    | nil => simp at member
    | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | later
      · simp [Store.lookup]
      · by_cases same : head.1 = pair.1
        · simp [Store.lookup, same]
        · simpa [Store.lookup, same] using ih later
  exact present

/-- A source procedure with an empty body lowers to Core's empty wrapper. -/
theorem transfer_empty
    (label : String) (Q : Assertion)
    (same : ∀ state env, entry state env → final state env) :
    Core.Logic.Hoare.Triple π params
      (Lift entry ((Transformer.block label (Transformer.scope Transformer.skip)).transform
        (fun _ => Q)))
      [.block "" [] #[]] (Lift final Q) (factory := factory) := by
  apply Core.Logic.Hoare.consequence π params
    (Core.Logic.Hoare.skip (factory := factory) π params "" #[] (Lift final Q))
    _ (fun _ h => h)
  rintro env ⟨state, ready, pre⟩
  exact ⟨state, same state env ready, by
    simpa [Transformer.block, Transformer.scope, Transformer.skip, restrict_self] using pre⟩

open Core.Logic.Hoare in
/-- Assignment only needs a simulation of the successful Core update.
The source transformer supplies the continuation at the updated state. -/
theorem transfer_set
    (target : Variable) (expr : Expression) (x : Core.CoreIdent)
    (e : Core.Expression.Expr) (md : MetaData Core.Expression) (Q : Assertion)
    (update : ∀ state env store value next, entry state env →
      Core.Expression.eval env.factory env.store e = some value →
      UpdateState Core.Expression env.store x value store →
      Transformer.assignState target expr state = .ok next →
      final next { env with store := store }) :
    Core.Logic.Hoare.Triple π params
      (Lift entry ((Transformer.step (Transformer.assignState target expr)).transform (fun _ => Q)))
      [Core.Statement.set x e md] (Lift final Q) (factory := factory) := by
  apply Core.Logic.Hoare.set
  rintro env store value ⟨state, related, pre⟩ eval written
  unfold Transformer.step at pre
  cases run : Transformer.assignState target expr state with
  | error reason => simp [run] at pre
  | ok next => exact ⟨next, update state env store value next related eval written run, by simpa [run] using pre⟩

/-- Assignment preserves the shared payloads and represents an output slot
after its first write. The scope predicate carries lexical freshness. -/
theorem transfer_scalar_assign
    (unwritten : List Core.CoreIdent) (slot : Variable)
    (expr : Expression) (target : Core.Expression.Expr) (md : MetaData Core.Expression) (Q : Assertion)
    (scope : Scope)
    (agrees : ExprAgrees (ScopedStoresAgree scope factory unwritten) expr target)
    (unshadowed : ∀ state, StateFits scope state → SlotUnshadowed state slot)
    (nameValid : (coreIdent slot).name.contains ' ' = false) :
    Core.Logic.Hoare.Triple π params
      (Lift (ScopedStoresAgree scope factory unwritten)
        ((Transformer.step (Transformer.assignState slot expr)).transform (fun _ => Q)))
      [Core.Statement.set (coreIdent slot) target md]
      (Lift (ScopedStoresAgree scope factory (unwritten.filter (· != coreIdent slot))) Q)
      (factory := factory) := by
  apply transfer_set
  intro state env store value next related evaluated updated assigned
  exact ⟨related.1.assign slot (fun value => agrees state env value related) evaluated updated
    assigned (unshadowed state related.2) (fun name _ _ => coreIdent_ne_old_of_no_space nameValid name),
    related.2.assign assigned⟩

/-- Local declaration extends the related stores before continuing. -/
theorem transfer_init
    (binding : Binding) (expr : Expression) (x : Core.CoreIdent)
    (ty : Core.Expression.Ty) (e : Core.Expression.Expr)
    (md : MetaData Core.Expression) (Q : Assertion)
    (declare : ∀ state env store value next, entry state env →
      Core.Expression.eval env.factory env.store e = some value →
      InitState Core.Expression env.store x value store →
      Transformer.initState binding expr state = .ok next →
      final next { env with store := store }) :
    Core.Logic.Hoare.Triple π params
      (Lift entry ((Transformer.step (Transformer.initState binding expr)).transform (fun _ => Q)))
      [Core.Statement.init x ty (.det e) md] (Lift final Q) (factory := factory) := by
  apply Core.Logic.Hoare.init
  rintro env store value ⟨state, related, pre⟩ eval written
  unfold Transformer.step at pre
  cases run : Transformer.initState binding expr state with
  | error reason => simp [run] at pre
  | ok next => exact ⟨next, declare state env store value next related eval written run,
      by simpa [run] using pre⟩

/-- A successful initializer grows the lexical scope and both stores. -/
theorem transfer_scalar_init
    (unwritten : List Core.CoreIdent) (scope : Scope) (binding : Binding)
    (expr : Expression) (target : Core.Expression.Expr) (ty : Core.Expression.Ty)
    (md : MetaData Core.Expression) (Q : Assertion)
    (agrees : ExprAgrees (ScopedStoresAgree scope factory unwritten) expr target) :
    Core.Logic.Hoare.Triple π params
      (Lift (ScopedStoresAgree scope factory unwritten)
        ((Transformer.step (Transformer.initState binding expr)).transform (fun _ => Q)))
      [Core.Statement.init ⟨binding.name, ()⟩ ty (.det target) md]
      (Lift (ScopedStoresAgree {scope with locals := scope.locals ++ [binding]} factory
        (unwritten.filter (· != ⟨binding.name, ()⟩))) Q) (factory := factory) := by
  apply transfer_init
  intro state env store value next related evaluated updated initialized
  exact ⟨related.1.declare binding (fun value => agrees state env value related)
    evaluated updated initialized, related.2.init initialized⟩

open Core.Logic.Hoare in
/-- Compose with the second transform at the intermediate state. The first
statement list has no escaping exits in the compatibility fragment. -/
theorem transfer_seq
    {middle : State → Env Core.Expression → Prop}
    {first second : Transformer} {firstStmts secondStmts : Core.Statements} (Q : Assertion)
    (firstTriple : Core.Logic.Hoare.Triple π params
      (Lift entry (first.transform (fun
        | none => second.transform (fun _ => Q)
        | some _ => Q)))
      firstStmts (Lift middle (second.transform (fun _ => Q))) (factory := factory))
    (secondTriple : Core.Logic.Hoare.Triple π params
      (Lift middle (second.transform (fun _ => Q))) secondStmts (Lift final Q) (factory := factory))
    (closed : Block.exitsCoveredByBlocks (P := Core.Expression) (CmdT := Core.Command) [] firstStmts) :
    Core.Logic.Hoare.Triple π params
      (Lift entry ((Transformer.seq first second).transform (fun _ => Q)))
      (firstStmts ++ secondStmts) (Lift final Q) (factory := factory) :=
  seq π params firstTriple secondTriple closed

open Core.Logic.Hoare in
/-- A source assertion obliges the corresponding Core check to hold. -/
theorem transfer_assert
    (sourceLabel coreLabel : String) (expr : Expression) (e : Core.Expression.Expr)
    (md : MetaData Core.Expression) (Q : Assertion)
    (ambient : ∀ state env, entry state env → env.factory.factory = factory)
    (check : ∀ state env, entry state env → Holds expr state →
      Core.Expression.eval env.factory env.store e = some (HasBool.ttVal env.factory)) :
    Core.Logic.Hoare.Triple π params
      (Lift entry ((Transformer.assertion sourceLabel expr).transform (fun _ => Q)))
      [Core.Statement.assert coreLabel e md] (Lift entry Q) (factory := factory) := by
  apply consequence π params (assert_eval (factory := factory) π params coreLabel e md
    (Lift entry ((Transformer.assertion sourceLabel expr).transform (fun _ => Q))) ?_ ?_) (fun _ h => h)
  · rintro env ⟨state, related, pre⟩
    exact ⟨state, related, pre.2⟩
  · rintro env ⟨state, related, _⟩
    exact ambient state env related
  · rintro env ⟨state, related, pre⟩
    exact check state env related pre.1

/-- A transformer test already guarantees that the source guard evaluated to
a Boolean. Forward evaluation agreement suffices to identify that Boolean. -/
private theorem guard_of_eval
    {guard : Expression} {e : Core.Expression.Expr} {state : State}
    {env : Env Core.Expression} {yes no : Prop} {b : Bool}
    (agreement : ∀ k : Bool, guard state = .ok (.bool k) →
      Core.Expression.eval env.factory env.store e = some (.ofBool env.factory.model.tcInterp k))
    (tested : test (some guard) state yes no)
    (evaluated : Core.Expression.eval env.factory env.store e = some (.ofBool env.factory.model.tcInterp b)) :
    guard state = .ok (.bool b) := by
  change (match guard state with
    | .ok (.bool k) => if k then yes else no
    | _ => False) at tested
  split at tested
  · rename_i k returned
    have same := Lambda.SemValue.ofBool_injective
      (Option.some.inj ((agreement k returned).symm.trans evaluated))
    exact same ▸ returned
  · exact False.elim tested

open Core.Logic.Hoare in
/-- A passing Core assumption selects the continuing branch of the transformer. -/
theorem transfer_assume
    (label : String) (expr : Expression) (e : Core.Expression.Expr)
    (md : MetaData Core.Expression) (Q : Assertion)
    (ambient : ∀ state env, entry state env → env.factory.factory = factory)
    (check : ∀ state env, entry state env → ∀ b : Bool,
      expr state = .ok (.bool b) →
      Core.Expression.eval env.factory env.store e = some (.ofBool env.factory.model.tcInterp b)) :
    Core.Logic.Hoare.Triple π params
      (Lift entry ((Transformer.assumption expr).transform (fun _ => Q)))
      [Core.Statement.assume label e md] (Lift entry Q) (factory := factory) := by
  apply assume_eval
  · rintro env ⟨state, related, _⟩
    exact ambient state env related
  · rintro env ⟨state, related, pre⟩ passed
    have evaluates := guard_of_eval (b := true) (check state env related) pre passed
    exact ⟨state, related, by simpa [Transformer.assumption, test, Value.bool, evaluates] using pre⟩

open Core.Logic.Hoare in
theorem transfer_branch
    {yes no : Transformer} {guard : Expression} {e : Core.Expression.Expr}
    {tss ess : Core.Statements} {md : MetaData Core.Expression} (Q : Assertion)
    (check : ∀ state env, entry state env → ∀ b : Bool,
      guard state = .ok (.bool b) →
      Core.Expression.eval env.factory env.store e = some (.ofBool env.factory.model.tcInterp b))
    (thenTriple : Core.Logic.Hoare.Triple π params (Lift entry (yes.transform (fun _ => Q)))
      tss (Lift final Q) (factory := factory))
    (elseTriple : Core.Logic.Hoare.Triple π params (Lift entry (no.transform (fun _ => Q)))
      ess (Lift final Q) (factory := factory))
    (thenScope : Imperative.Logic.Hoare.PostWF tss (Lift final Q))
    (elseScope : Imperative.Logic.Hoare.PostWF ess (Lift final Q)) :
    Core.Logic.Hoare.Triple π params
      (Lift entry ((Transformer.branch (some guard) yes no).transform (fun _ => Q)))
      [.ite (.det e) tss ess md] (Lift final Q) (factory := factory) := by
  apply ite π params _ _ thenScope elseScope
  · apply consequence π params thenTriple _ (fun _ h => h)
    rintro env ⟨⟨state, related, pre⟩, cond⟩
    have evaluates := guard_of_eval (b := true) (check state env related) pre cond
    exact ⟨state, related, by simpa [Transformer.branch, test, Value.bool, evaluates] using pre⟩
  · apply consequence π params elseTriple _ (fun _ h => h)
    rintro env ⟨⟨state, related, pre⟩, cond⟩
    have evaluates := guard_of_eval (b := false) (check state env related) pre cond
    exact ⟨state, related, by simpa [Transformer.branch, test, Value.bool, evaluates] using pre⟩


open Core.Logic.Hoare in
/-- Scope both sides of the body proof with the locals visible on entry.
The body triple can forget block-local slots when proving its postcondition. -/
theorem transfer_scope
    (body : Transformer) (ss : Core.Statements)
    (label : String) (md : MetaData Core.Expression) (Q : Assertion)
    (bodyTriple : ∀ initial, Core.Logic.Hoare.Triple π params
      (fun env => entry initial env ∧
        body.transform (fun _ state =>
          Q { state with locals := state.locals.restrict initial.locals }) initial)
      ss (Lift final Q) (factory := factory))
    (project : Imperative.Logic.Hoare.PostWF ss (Lift final Q)) :
    Core.Logic.Hoare.Triple π params
      (Lift entry ((Transformer.block label (Transformer.scope body)).transform (fun _ => Q)))
      [.block label ss md] (Lift final Q) (factory := factory) := by
  intro env finalEnv trace ⟨initial, related, pre⟩ wf run
  have ready : body.transform (fun _ state =>
      Q { state with locals := state.locals.restrict initial.locals }) initial := by
    apply body.monotone _ _ pre
    intro control state h
    exact h
  exact Core.Logic.Hoare.block π params
    (bodyTriple initial) project env finalEnv trace ⟨related, ready⟩ wf run

/-- The states obtained by changing only the listed slots, to values of the
listed types. The order matches `withChanges`. -/
def InWriteFrame : List (Variable × ValueType) → State → State → Prop
  | [], anchor, state => state = anchor
  | (slot, sort) :: rest, anchor, state =>
      ∃ v : sort.denote .builtins, InWriteFrame rest (anchor.update slot ⟨sort, v⟩) state

theorem InWriteFrame.apply {writes : List (Variable × ValueType)}
    {anchor state : State} {P : Assertion}
    (frame : InWriteFrame writes anchor state) (all : withChanges writes anchor P) : P state := by
  induction writes generalizing anchor with
  | nil => cases frame; exact all
  | cons slot rest ih =>
    obtain ⟨v, frame⟩ := frame
    exact ih frame (all v)

private theorem state_update_overwrite (state : State) (slot : Variable) (old new : Value) :
    (state.update slot old).update slot new = state.update slot new := by
  have overwrite (store : Store) (name : String) :
      (store.update name old).update name new = store.update name new := by
    simp only [Store.update, List.map_map, Function.comp_def]
    congr 1
    funext item
    obtain ⟨key, value⟩ := item
    by_cases h : key == name <;> simp [h]
  cases slot <;> simp [State.update, overwrite]

set_option linter.unusedSimpArgs false in
private theorem state_update_commute (state : State) (left right : Variable) (a b : Value)
    (different : left ≠ right) :
    (state.update left a).update right b = (state.update right b).update left a := by
  have commute (store : Store) (first second : String) (distinct : first ≠ second) :
      (store.update first a).update second b = (store.update second b).update first a := by
    simp only [Store.update, List.map_map, Function.comp_def]
    congr 1
    funext item
    obtain ⟨key, value⟩ := item
    by_cases firstEq : key = first
    · subst key
      simp [show (first == second) = false from beq_eq_false_iff_ne.mpr distinct]
    · simp [show (key == first) = false from beq_eq_false_iff_ne.mpr firstEq]
  cases left <;> cases right <;> simp_all [State.update, commute]

theorem InWriteFrame.refl (writes : List (Variable × ValueType)) (state : State)
    (identity : ∀ slot sort, (slot, sort) ∈ writes →
      ∃ v : sort.denote .builtins, state.update slot ⟨sort, v⟩ = state) :
    InWriteFrame writes state state := by
  induction writes with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨slot, sort⟩ := head
    obtain ⟨v, same⟩ := identity slot sort List.mem_cons_self
    refine ⟨v, ?_⟩
    rw [same]
    exact ih (fun slot sort mem => identity slot sort (List.mem_cons_of_mem _ mem))

private theorem InWriteFrame.update_outside {writes : List (Variable × ValueType)}
    {anchor state : State} (frame : InWriteFrame writes anchor state)
    (slot : Variable) (value : Value) (outside : slot ∉ writes.map Prod.fst) :
    InWriteFrame writes (anchor.update slot value) (state.update slot value) := by
  induction writes generalizing anchor with
  | nil =>
    have same : state = anchor := frame
    change state.update slot value = anchor.update slot value
    rw [same]
  | cons head rest ih =>
    obtain ⟨v, represented⟩ := frame
    have disjoint : slot ≠ head.1 ∧ slot ∉ rest.map Prod.fst := by
      simpa [List.mem_cons] using outside
    refine ⟨v, ?_⟩
    rw [state_update_commute anchor slot head.1 _ _ disjoint.1]
    exact ih represented disjoint.2

theorem InWriteFrame.update {writes : List (Variable × ValueType)}
    {anchor state : State} (frame : InWriteFrame writes anchor state)
    (unique : (writes.map Prod.fst).Nodup)
    {slot : Variable} {sort : ValueType} (written : (slot, sort) ∈ writes)
    (value : sort.denote .builtins) :
    InWriteFrame writes anchor (state.update slot ⟨sort, value⟩) := by
  induction writes generalizing anchor with
  | nil => simp at written
  | cons head rest ih =>
    obtain ⟨v, represented⟩ := frame
    have whole : (head.1 :: rest.map Prod.fst).Nodup := unique
    obtain ⟨disjoint, restUnique⟩ := List.nodup_cons.mp whole
    rcases List.mem_cons.mp written with equal | later
    · subst head
      refine ⟨value, ?_⟩
      have moved := represented.update_outside slot ⟨sort, value⟩ disjoint
      rwa [state_update_overwrite] at moved
    · exact ⟨v, ih represented restUnique later⟩

open Core.Logic.Hoare in
/-- Use the Boole loop obligations as a Core invariant, retaining the state
at loop entry so each iteration can use the original write frame. -/
theorem transfer_loop
    (writes : List (Variable × ValueType)) (guard : Expression)
    (invariant : Assertion) (measure : Option Expression) (body : Transformer)
    (e : Core.Expression.Expr) (m : Option Core.Expression.Expr)
    (inv : List (String × Core.Expression.Expr)) (ss : Core.Statements)
    (md : MetaData Core.Expression) (Q : Assertion)
    (check : ∀ state env, entry state env → ∀ b : Bool,
      guard state = .ok (.bool b) →
      Core.Expression.eval env.factory env.store e = some (.ofBool env.factory.model.tcInterp b))
    (frameRefl : ∀ state env, entry state env → InWriteFrame writes state state)
    (bodyTriple : ∀ (anchor : State) (onExit : String → Assertion), Core.Logic.Hoare.Triple π params
      (Lift entry (fun state => InWriteFrame writes anchor state ∧
        body.transform (fun
          | none => Transformer.loopHead invariant measure
          | some label => onExit label) state))
      ss (Lift entry (fun state =>
        InWriteFrame writes anchor state ∧ Transformer.loopHead invariant measure state))
      (factory := factory))
    (closed : Block.exitsCoveredByBlocks (P := Core.Expression) (CmdT := Core.Command) [] ss)
    (project : ∀ P : Assertion, Imperative.Logic.Hoare.PostWF ss (Lift entry P)) :
    Core.Logic.Hoare.Triple π params
      (Lift entry ((Transformer.loop writes (some guard) invariant measure body).transform (fun _ => Q)))
      [.loop (.det e) m inv ss md] (Lift entry Q) (factory := factory) := by
  let loopPre := (Transformer.loop writes (some guard) invariant measure body).transform (fun _ => Q)
  let Inv : Assertion := fun state => ∃ anchor, loopPre anchor ∧ InWriteFrame writes anchor state ∧
    Transformer.loopHead invariant measure state
  apply consequence π params (while_rule π params (Inv := Lift entry Inv) ?_ closed (project Inv))
  · intro env h
    obtain ⟨state, related, pre⟩ := h
    exact ⟨state, related, state, pre, frameRefl state env related, pre.1⟩
  · rintro env ⟨⟨state, related, anchor, pre, frame, head⟩, cond⟩
    have branch := (frame.apply pre.2) head
    have evaluates := guard_of_eval (b := false) (check state env related) branch cond
    exact ⟨state, related, by simpa [test, Value.bool, evaluates] using branch⟩
  · intro env finalEnv trace ⟨⟨state, related, anchor, pre, frame, head⟩, cond⟩ wf run
    have branch := (frame.apply pre.2) head
    have evaluates := guard_of_eval (b := true) (check state env related) branch cond
    simp only [test, evaluates, Value.bool, ↓reduceIte] at branch
    have preserve := body.monotone (Q := fun
        | none => Transformer.loopHead invariant measure
        | some _ => Q) (by
      intro control after holds
      cases control with
      | none => exact holds.1
      | some _ => exact holds) state branch
    obtain ⟨valid, result⟩ := bodyTriple anchor (fun _ => Q) env finalEnv trace
      ⟨state, related, frame, preserve⟩ wf run
    refine ⟨valid, fun reachable => ?_⟩
    obtain ⟨after, related, frame, head⟩ := result reachable
    exact ⟨after, related, anchor, pre, frame, head⟩

end

end Strata.Boole.Hoare
