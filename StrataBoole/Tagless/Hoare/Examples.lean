/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import StrataBoole.Deep.Reflect
import StrataBoole.Tagless.Hoare.Certificate

/-! # Core programs verified through the tagless Hoare interpretation

Each example is written in Strata Core syntax, including its contract.
`#core_reflect` is Stephanie's existing front end: it translates and type-checks
that source, then defines the named procedure as a Lean `Core.Procedure`.
The proofs below use the tagless Hoare route, not Deep.Exec or core_vcgen.

`Hoare.Verified p` asserts that embedding succeeds and the interpreted contract
holds. Correspondence to Core's operational semantics remains to be proved.
-/

open StrataDDM (Program)

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace Strata.Tagless.Examples

-- Choose either input, and prove that it is their maximum.
def max2Pgm :=
#strata
program Core;

procedure max2(x : int, y : int, out m : int)
spec {
  ensures (int.ge(m, x));
  ensures (int.ge(m, y));
  ensures (m == x || m == y);
}
{
  if (int.ge(x, y)) {
    m := x;
  } else {
    m := y;
  }
};
#end

#core_reflect max2Pgm

theorem max2_correct : Hoare.Verified max2 := by
  unfold max2
  tagless_vcgen <;> grind

-- A nonnegative input becomes a positive output.
def incrementPgm :=
#strata
program Core;

procedure increment(n : int, out r : int)
spec {
  requires (int.ge(n, 0));
  ensures (int.gt(r, 0));
}
{
  r := int.add(n, 1);
};
#end

#core_reflect incrementPgm

theorem increment_correct : Hoare.Verified increment := by
  unfold increment
  tagless_vcgen <;> grind

/-- The worked example's embedded requires, ensures, and transformed ensures
are exactly the displayed native predicates. This checks the intermediate
formulas used in the internal brief against the actual reflected Core program. -/
theorem increment_conditions :
    ∃ recipes, embedCore increment = .ok recipes ∧
      let (P, command, Q) := Hoare.interpret recipes
      (∀ σ, P σ ↔ 0 ≤ σ.ints "n") ∧
      (∀ σ, Q σ ↔ 0 < σ.ints "r") ∧
      (∀ σ, command.transform Q σ ↔ 0 < σ.ints "n" + 1) := by
  unfold increment
  tagless_embed
  dsimp only [Hoare.interpret, Hoare.interpretation]
  tagless_lift
  simp [Hoare.Obligation]

-- A local variable can carry an intermediate result.
def withLocalPgm :=
#strata
program Core;

procedure withLocal(n : int, out r : int)
spec {
  requires (int.ge(n, 0));
  ensures (int.gt(r, 0));
}
{
  var temp : int := int.add(n, 1);
  r := temp;
};
#end

#core_reflect withLocalPgm

theorem withLocal_correct : Hoare.Verified withLocal := by
  unfold withLocal
  tagless_vcgen <;> grind

-- The postcondition compares the result with the entry value of g.
def incrementInoutPgm :=
#strata
program Core;

procedure incrementInout(inout g : int)
spec {
  ensures (g == int.add(old(g), 1));
}
{
  g := int.add(g, 1);
};
#end

#core_reflect incrementInoutPgm

theorem incrementInout_correct : Hoare.Verified incrementInout := by
  unfold incrementInout
  tagless_vcgen <;> grind

-- The invariant proves partial correctness without a decrease annotation.
def countUpPgm :=
#strata
program Core;

procedure countUp(n : int, out i : int)
spec {
  requires (int.ge(n, 0));
  ensures (i == n);
}
{
  i := 0;
  while (int.lt(i, n))
    invariant int.le(0, i)
    invariant int.le(i, n)
  {
    i := int.add(i, 1);
  }
};
#end

#core_reflect countUpPgm

theorem countUp_correct : Hoare.Verified countUp := by
  unfold countUp
  tagless_vcgen <;> grind

-- The same loop additionally generates bound and decrease obligations.
def measuredCountUpPgm :=
#strata
program Core;

procedure measuredCountUp(n : int, out i : int)
spec {
  requires (int.ge(n, 0));
  ensures (i == n);
}
{
  i := 0;
  while (int.lt(i, n))
    decreases int.sub(n, i)
    invariant int.le(0, i)
    invariant int.le(i, n)
  {
    i := int.add(i, 1);
  }
};
#end

#core_reflect measuredCountUpPgm

theorem measuredCountUp_correct : Hoare.Verified measuredCountUp := by
  unfold measuredCountUp
  tagless_vcgen <;> grind

-- A free ensures is not a guarantee established by checking this body.
def togglePgm :=
#strata
program Core;

procedure toggle(b : bool, out r : bool)
spec {
  ensures (r == !b);
  free ensures (false);
}
{
  r := !b;
};
#end

#core_reflect togglePgm

theorem toggle_correct : Hoare.Verified toggle := by
  unfold toggle
  tagless_vcgen <;> grind

-- An impossible assumption discards its path, so this postcondition is permitted.
def unreachablePgm :=
#strata
program Core;

procedure unreachable()
spec {
  ensures (false);
}
{
  assume false;
};
#end

#core_reflect unreachablePgm

theorem unreachable_correct : Hoare.Verified unreachable := by
  unfold unreachable
  tagless_vcgen <;> grind

-- An impossible assertion, in contrast, must not verify.
def failingAssertionPgm :=
#strata
program Core;

procedure failingAssertion()
spec {
  ensures (true);
}
{
  assert false;
};
#end

#core_reflect failingAssertionPgm

theorem failingAssertion_refuted : ¬ Hoare.Verified failingAssertion := by
  unfold failingAssertion Hoare.Verified
  tagless_embed
  dsimp only [Hoare.interpret, Hoare.interpretation]
  rw [Hoare.triple_iff]
  intro h
  have bad := h ⟨fun _ => 0, fun _ => false⟩ trivial
  simp [Hoare.Transformer.seq, Hoare.Transformer.skip,
    Hoare.Transformer.block, Hoare.Transformer.assert, Hoare.Obligation,
    Hoare.Expr.Holds, Hoare.Expr.total] at bad

end Strata.Tagless.Examples
