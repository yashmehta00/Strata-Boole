/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Runtime
import all StrataBoole.Boole.Runtime
public import Std.Internal.Do
public meta import Std.Tactic.Do

/-! Predicate transformers over Boole's state. A command may continue normally
or exit to a label. Failed checks and invalid evaluations make its precondition
false. A blocked assumption has no continuation to check. -/

public section
namespace Strata.Boole.Hoare

open Std.Internal.Do

abbrev Assertion := State → Prop

/-- `none` is normal continuation and `some label` is a labelled exit. -/
abbrev Control := Option String

/-- Turn a postcondition for each exit into a precondition. Monotonicity
allows a proof to weaken the postcondition. -/
structure Transformer where
  transform : (Control → Assertion) → Assertion
  monotone : ∀ {P Q}, (∀ c s, P c s → Q c s) → ∀ s, transform P s → transform Q s

/-- Retain source labels in the generated formula. -/
def Obligation (_label : String) (condition : Prop) : Prop := condition

/-- A missing guard denotes demonic choice between true and false. -/
def test (guard : Option Expression) (state : State) (yes no : Prop) : Prop :=
  match guard with
  | none => yes ∧ no
  | some expression =>
    match expression state with
    | .ok (.bool value) => if value then yes else no
    | _ => False

def Holds (expression : Expression) (state : State) : Prop :=
  test (some expression) state True False

private theorem test_mono (guard : Option Expression) (s : State)
    (hy : yes → yes') (hn : no → no') : test guard s yes no → test guard s yes' no' := by
  cases guard with
  | none => exact fun h => ⟨hy h.1, hn h.2⟩
  | some e =>
    simp only [test]
    split
    · split
      · exact hy
      · exact hn
    · exact id

/-- Universally choose new values for the selected slots, preserving the rest
of the entry state and the old snapshots. -/
def withChanges (writes : List (Variable × ValueType)) (state : State) (post : Assertion) : Prop :=
  match writes with
  | [] => post state
  | (slot, sort) :: rest =>
    ∀ v : sort.denote, withChanges rest (state.update slot ⟨sort, v⟩) post

private theorem withChanges_mono (writes : List (Variable × ValueType)) (state : State)
    (h : ∀ s, P s → Q s) : withChanges writes state P → withChanges writes state Q := by
  induction writes generalizing state with
  | nil => exact h _
  | cons slot rest ih => exact fun hp v => ih _ (hp v)

namespace Transformer

def skip : Transformer :=
  ⟨fun Q => Q none, fun h s => h none s⟩

def seq (first second : Transformer) : Transformer where
  transform Q := first.transform (fun
    | none => second.transform Q
    | some label => Q (some label))
  monotone h := first.monotone (fun c s => match c with
    | none => second.monotone h s
    | some label => h (some label) s)

def exit (label : String) : Transformer :=
  ⟨fun Q => Q (some label), fun h s => h (some label) s⟩

def block (label : String) (body : Transformer) : Transformer where
  transform Q := body.transform (fun c => Q (if c == some label then none else c))
  monotone h := body.monotone (fun _ _ => h _ _)

def scope (body : Transformer) : Transformer where
  transform Q entry := body.transform (fun c final =>
    Q c { final with locals := final.locals.restrict entry.locals }) entry
  monotone h entry := body.monotone (fun _ _ => h _ _) entry

/-- A deterministic state update must succeed. -/
def step (run : State → Except RuntimeError State) : Transformer where
  transform Q s := match run s with
    | .ok t => Q none t
    | .error _ => False
  monotone h s := by
    split
    · exact h _ _
    · exact id

def assignState (target : Variable) (expression : Expression) (s : State) :
    Except RuntimeError State := do
  let previous ← Expression.read target s
  let value ← expression s
  if previous.sort = value.sort then .ok (s.update target value) else .error .wrongType

def initState (binding : Binding) (expression : Expression) (s : State) :
    Except RuntimeError State := do
  if (s.locals.lookup binding.name).isSome then
    throw (.duplicateLocal binding.name)
  let value ← expression s
  if value.sort = binding.sort then .ok { s with locals := s.locals ++ [(binding.name, value)] }
  else .error .wrongType

/-- An uninitialized local or a havoc ranges over its full source carrier. -/
def arbitrary (body : α → Transformer) : Transformer where
  transform Q s := ∀ value, (body value).transform Q s
  monotone h s hp value := (body value).monotone h s (hp value)

def assertion (label : String) (expression : Expression) : Transformer where
  transform Q s := Obligation label (Holds expression s) ∧ Q none s
  monotone h s hp := ⟨hp.1, h none s hp.2⟩

def assumption (expression : Expression) : Transformer where
  transform Q s := test (some expression) s (Q none s) True
  monotone h s := test_mono _ _ (h none s) id

def branch (guard : Option Expression) (yes no : Transformer) : Transformer where
  transform Q s := test guard s (yes.transform Q s) (no.transform Q s)
  monotone h s := test_mono _ _ (yes.monotone h s) (no.monotone h s)

def loopHead (invariant : Assertion) (measure : Option Expression) (s : State) : Prop :=
  invariant s ∧ match measure with
  | none => True
  | some e => ∃ n : Int, e s = .ok (.int n) ∧ 0 ≤ n

def decreases (measure : Option Expression) (before after : State) : Prop :=
  match measure with
  | none => True
  | some e => ∃ m n : Int, e before = .ok (.int m) ∧ e after = .ok (.int n) ∧ n < m

def loop (writes : List (Variable × ValueType)) (guard : Option Expression)
    (invariant : Assertion) (measure : Option Expression) (body : Transformer) : Transformer where
  transform Q entry :=
    loopHead invariant measure entry ∧
      withChanges writes entry (fun before =>
        loopHead invariant measure before →
          test guard before
            (body.transform (fun
              | none => fun after => loopHead invariant measure after ∧ decreases measure before after
              | some label => Q (some label)) before)
            (Q none before))
  monotone h entry hp := by
    refine ⟨hp.1, withChanges_mono writes entry (fun before hb hi => ?_) hp.2⟩
    apply test_mono guard before _ (h none before) (hb hi)
    apply body.monotone
    intro c s
    cases c with
    | none => exact id
    | some label => exact h (some label) s

/- Compiler reduction stops at these command combinators. Lean's `vcgen`
sees their heads and applies the registered specifications below. -/
attribute [cbv_opaque] skip seq exit block scope step assignState initState arbitrary
  assertion assumption branch loop

end Transformer

instance : WP Transformer Control Assertion Prop where
  wpTrans command := ⟨fun post _ => command.transform post⟩
  wp_trans_monotone command := by
    intro post post' exceptional exceptional' _ hpost
    exact command.monotone hpost

theorem wp_eq (command : Transformer) (Q : Control → Assertion) (E : Prop) :
    wp command Q E = command.transform Q := rfl

abbrev Triple (P : Assertion) (command : Transformer) (Q : Control → Assertion) : Prop :=
  Std.Internal.Do.Triple command P Q False

@[spec] theorem skip_spec (Q : Control → Assertion) :
    Triple (Q none) Transformer.skip Q := ⟨fun _ h => h⟩

@[spec] theorem exit_spec (label : String) (Q : Control → Assertion) :
    Triple (Q (some label)) (Transformer.exit label) Q := ⟨fun _ h => h⟩

@[spec] theorem seq_spec (first second : Transformer) (Q : Control → Assertion) :
    Triple (wp first (fun
      | none => wp second Q False
      | some label => Q (some label)) False) (Transformer.seq first second) Q :=
  ⟨fun _ h => h⟩

@[spec] theorem block_spec (label : String) (body : Transformer) (Q : Control → Assertion) :
    Triple (wp body (fun c => Q (if c == some label then none else c)) False)
      (Transformer.block label body) Q := ⟨fun _ h => h⟩

@[spec] theorem scope_spec (body : Transformer) (Q : Control → Assertion) :
    Triple (fun entry => wp body (fun c final =>
      Q c { final with locals := final.locals.restrict entry.locals }) False entry)
      (Transformer.scope body) Q := ⟨fun _ h => h⟩

@[spec] theorem step_spec (run : State → Except RuntimeError State) (Q : Control → Assertion) :
    Triple (fun s => match run s with
      | .ok t => Q none t
      | .error _ => False) (Transformer.step run) Q := ⟨fun _ h => h⟩

@[spec] theorem arbitrary_spec (body : α → Transformer)
    (Q : Control → Assertion) :
    Triple (fun s => ∀ v, wp (body v) Q False s)
      (Transformer.arbitrary body) Q := ⟨fun _ h => h⟩

@[spec] theorem assertion_spec (label : String) (e : Expression) (Q : Control → Assertion) :
    Triple (fun s => Obligation label (Holds e s) ∧ Q none s)
      (Transformer.assertion label e) Q := ⟨fun _ h => h⟩

@[spec] theorem assumption_spec (e : Expression) (Q : Control → Assertion) :
    Triple (fun s => test (some e) s (Q none s) True)
      (Transformer.assumption e) Q := ⟨fun _ h => h⟩

@[spec] theorem branch_spec (guard : Option Expression) (yes no : Transformer)
    (Q : Control → Assertion) :
    Triple (fun s => test guard s (wp yes Q False s) (wp no Q False s))
      (Transformer.branch guard yes no) Q := ⟨fun _ h => h⟩

@[spec] theorem loop_spec (writes : List (Variable × ValueType)) (guard : Option Expression)
    (invariant : Assertion) (measure : Option Expression) (body : Transformer)
    (Q : Control → Assertion) :
    Triple (fun entry => Transformer.loopHead invariant measure entry ∧
      withChanges writes entry (fun before => Transformer.loopHead invariant measure before →
        test guard before
          (wp body (fun
            | none => fun after => Transformer.loopHead invariant measure after ∧
                Transformer.decreases measure before after
            | some label => Q (some label)) False before)
          (Q none before)))
      (Transformer.loop writes guard invariant measure body) Q := ⟨fun _ h => h⟩

end Strata.Boole.Hoare
