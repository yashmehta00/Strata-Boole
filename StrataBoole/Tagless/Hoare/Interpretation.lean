/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.Tagless.Interface

/-! Hoare meanings: native values and definedness for expressions, monotone
predicate transformers for commands. No source traversal or new Exec relation.
The original-Core proof boundary is recorded in Guarantees/Soundness.lean.
The WP framework adapter is separate, in Rules.lean. -/

namespace Strata.Tagless.Hoare

/-- Logical values for each supported type. Static scope and type checks select
the live names and the appropriate slot; this is not another Core store AST. -/
@[ext] structure State where
  ints : String → Int
  bools : String → Bool
  deriving Inhabited

def State.read (σ : State) : (ty : Ty) → String → ty.denote
  | .int, x => σ.ints x
  | .bool, x => σ.bools x

def State.write (σ : State) : (ty : Ty) → String → ty.denote → State
  | .int, x, v => { σ with ints := fun y => if y = x then v else σ.ints y }
  | .bool, x, v => { σ with bools := fun y => if y = x then v else σ.bools y }

def State.restore (locals : List String) (entry final : State) : State := {
  ints := fun x => if x ∈ locals then entry.ints x else final.ints x
  bools := fun x => if x ∈ locals then entry.bools x else final.bools x
}

/-- Arbitrary values only for names the loop body may write. -/
def State.havoc (entry : State) (writes : List String) (arbitrary : State) : State := {
  ints := fun x => if x ∈ writes then arbitrary.ints x else entry.ints x
  bools := fun x => if x ∈ writes then arbitrary.bools x else entry.bools x
}

/-- A transparent label for proof-goal presentation; it adds no assumption. -/
def Obligation (_label : String) (condition : Prop) : Prop := condition

/-- Definedness is necessary for partial built-ins such as integer division.
Keeping it alongside the value avoids a second expression AST or evaluator. -/
structure Expr (ty : Ty) where
  value : State → ty.denote
  defined : State → Prop

instance : CoeFun (Expr ty) (fun _ => State → ty.denote) := ⟨Expr.value⟩

namespace Expr

def total (value : State → ty.denote) : Expr ty := ⟨value, fun _ => True⟩

def unary (f : a.denote → b.denote) (e : Expr a) : Expr b :=
  ⟨fun σ => f (e σ), e.defined⟩

def binary (f : a.denote → b.denote → c.denote) (x : Expr a) (y : Expr b) : Expr c :=
  ⟨fun σ => f (x σ) (y σ), fun σ => x.defined σ ∧ y.defined σ⟩

def divide (x y : Expr .int) : Expr .int :=
  ⟨fun σ => x σ / y σ, fun σ => x.defined σ ∧ y.defined σ ∧ y σ ≠ 0⟩

def modulo (x y : Expr .int) : Expr .int :=
  ⟨fun σ => x σ % y σ, fun σ => x.defined σ ∧ y.defined σ ∧ y σ ≠ 0⟩

def ite (guard : Expr .bool) (yes no : Expr ty) : Expr ty :=
  ⟨fun σ => if guard σ then yes σ else no σ,
   fun σ => guard.defined σ ∧ if guard σ then yes.defined σ else no.defined σ⟩

/-- Checks require a defined, true expression. -/
def Holds (e : Expr .bool) (σ : State) : Prop := e.defined σ ∧ e σ = true

/-- An undefined assumption is conservatively ignored, as in Deep.MayHold.
It cannot be used to make an otherwise reachable obligation disappear. -/
def MayHold (e : Expr .bool) (σ : State) : Prop := e.defined σ → e σ = true

end Expr

/-- Generated requirements for an arbitrary postcondition. Monotonicity lets
the separate WP adapter use these requirements in Lean's verification framework;
Core soundness is established separately for successfully embedded programs. -/
structure Transformer where
  transform : (State → Prop) → State → Prop
  monotone : ∀ P Q, (∀ σ, P σ → Q σ) → ∀ σ, transform P σ → transform Q σ

namespace Transformer

def skip : Transformer where
  transform := fun Q => Q
  monotone := by intro P Q h σ hp; exact h σ hp

def seq (first second : Transformer) : Transformer where
  transform := fun Q => first.transform (second.transform Q)
  monotone := by
    intro P Q h σ hp
    exact first.monotone _ _ (second.monotone _ _ h) σ hp

def assign (ty : Ty) (x : String) (e : Expr ty) : Transformer where
  transform := fun Q σ => e.defined σ ∧ Q (σ.write ty x (e σ))
  monotone := by intro P Q h σ hp; exact ⟨hp.1, h _ hp.2⟩

def havoc (ty : Ty) (x : String) : Transformer where
  transform := fun Q σ => ∀ v : ty.denote, Q (σ.write ty x v)
  monotone := by intro P Q h σ hp v; exact h _ (hp v)

def assert (info : ClauseInfo) (e : Expr .bool) : Transformer where
  transform := fun Q σ => Obligation info.label (e.Holds σ) ∧ Q σ
  monotone := by intro P Q h σ hp; exact ⟨hp.1, h σ hp.2⟩

def assume (_info : ClauseInfo) (e : Expr .bool) : Transformer where
  transform := fun Q σ => e.MayHold σ → Q σ
  monotone := by intro P Q h σ hp he; exact h σ (hp he)

def branch (guard : Expr .bool) (yes no : Transformer) : Transformer where
  transform := fun Q σ => guard.defined σ ∧
    if guard σ then yes.transform Q σ else no.transform Q σ
  monotone := by
    intro P Q h σ hp
    refine ⟨hp.1, ?_⟩
    by_cases hg : guard σ = true
    · simpa [hg] using yes.monotone _ _ h σ (by simpa [hg] using hp.2)
    · simpa [hg] using no.monotone _ _ h σ (by simpa [hg] using hp.2)

def choice (yes no : Transformer) : Transformer where
  transform := fun Q σ => yes.transform Q σ ∧ no.transform Q σ
  monotone := by
    intro P Q h σ hp
    exact ⟨yes.monotone _ _ h σ hp.1, no.monotone _ _ h σ hp.2⟩

def block (locals : List String) (body : Transformer) : Transformer where
  transform := fun Q entry =>
    body.transform (fun final => Q (State.restore locals entry final)) entry
  monotone := by
    intro P Q h σ hp
    exact body.monotone _ _ (fun final => h _) σ hp

def invariantsHold (invariants : List (ClauseInfo × Expr .bool)) (σ : State) : Prop :=
  ∀ clause ∈ invariants, Obligation clause.1.label (clause.2.Holds σ)

def measureBound (measure : Option (Expr .int)) (σ : State) : Prop :=
  match measure with
  | none => True
  | some e => Obligation "measure_bound" (e.defined σ ∧ 0 ≤ e σ)

def measureDrops (measure : Option (Expr .int)) (before after : State) : Prop :=
  match measure with
  | none => True
  | some e => Obligation "measure_decrease"
      (e.defined before ∧ e.defined after ∧ e after < e before)

def loopHead (invariants : List (ClauseInfo × Expr .bool))
    (measure : Option (Expr .int)) (σ : State) : Prop :=
  invariantsHold invariants σ ∧ measureBound measure σ

/-- Framed invariant VCs. Unwritten variables keep their entry values at every
arbitrary loop head. The body must re-establish invariants and the measure bound;
an optional measure must decrease. No termination claim follows merely from this
operation's definition. -/
def loop (writes : List String) (guard : Expr .bool)
    (invariants : List (ClauseInfo × Expr .bool))
    (measure : Option (Expr .int)) (body : Transformer) : Transformer where
  transform := fun Q entry =>
    loopHead invariants measure entry ∧
    ∀ arbitrary,
      let before := entry.havoc writes arbitrary
      loopHead invariants measure before →
      guard.defined before ∧
      (guard before = true →
        body.transform (fun after => loopHead invariants measure after ∧
          measureDrops measure before after) before) ∧
      (guard before = false → Q before)
  monotone := by
    intro P Q h σ hp
    refine ⟨hp.1, fun arbitrary hi => ?_⟩
    have hb := hp.2 arbitrary hi
    exact ⟨hb.1, hb.2.1, fun hg => h _ (hb.2.2 hg)⟩

end Transformer

/-- Both ordinary and free requires are body assumptions. -/
def requiresClause (_info : ClauseInfo) (e : Expr .bool) : State → Prop := e.MayHold

/-- Free ensures are not guarantees established by body verification. -/
def ensuresClause (info : ClauseInfo) (e : Expr .bool) : State → Prop :=
  if info.attr = .Default then fun σ => Obligation info.label (e.Holds σ) else fun _ => True

def interpretation : Interpretation := {
  Expr := Expr
  Cmd := Transformer
  Pred := State → Prop
  intLiteral := fun n => Expr.total (fun _ => n)
  boolLiteral := fun b => Expr.total (fun _ => b)
  read := fun ty x => Expr.total (fun σ => σ.read ty x)
  neg := Expr.unary (- ·)
  not := Expr.unary (! ·)
  add := Expr.binary (· + ·)
  sub := Expr.binary (· - ·)
  mul := Expr.binary (· * ·)
  div := Expr.divide
  mod := Expr.modulo
  lt := Expr.binary (fun x y => decide (x < y))
  le := Expr.binary (fun x y => decide (x ≤ y))
  gt := Expr.binary (fun x y => decide (x > y))
  ge := Expr.binary (fun x y => decide (x ≥ y))
  and := Expr.binary (· && ·)
  or := Expr.binary (· || ·)
  implies := Expr.binary (fun x y => !x || y)
  equiv := Expr.binary (· == ·)
  eq := fun ty => match ty with
    | .int => Expr.binary (fun x y => decide (x = y))
    | .bool => Expr.binary (· == ·)
  ite := Expr.ite
  skip := Transformer.skip
  seq := Transformer.seq
  assign := Transformer.assign
  havoc := Transformer.havoc
  assert := Transformer.assert
  assume := Transformer.assume
  branch := Transformer.branch
  choice := Transformer.choice
  block := Transformer.block
  loop := Transformer.loop
  truePred := fun _ => True
  andPred := fun P Q σ => P σ ∧ Q σ
  requiresClause := requiresClause
  ensuresClause := ensuresClause
}

def interpret (recipes : PredRecipe × CmdRecipe × PredRecipe) :
    (State → Prop) × Transformer × (State → Prop) :=
  (recipes.1 interpretation, recipes.2.1 interpretation, recipes.2.2 interpretation)

end Strata.Tagless.Hoare
