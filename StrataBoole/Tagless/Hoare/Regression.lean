/- Semantic regression examples, written in actual Core syntax. -/
import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import StrataBoole.Deep.Reflect
import StrataBoole.Tagless.Hoare.Certificate

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Strata.Tagless.Regression

-- A fixed counterexample state suffices for these deliberately bad programs.
macro "refute_tagless" : tactic => `(tactic| (
  unfold Hoare.Verified
  tagless_embed
  dsimp only [Hoare.interpret, Hoare.interpretation]
  rw [Hoare.triple_iff]
  intro h
  have bad := h ⟨fun _ => 0, fun _ => false⟩ (by tagless_lift)
  tagless_lift
  all_goals simp_all [Hoare.Obligation]))

-- Crucially, r = 7 is established before the loop, not repeated in an invariant.
def framedLoopPgm :=
#strata
program Core;
procedure framedLoop(n : int, out i : int, out r : int)
spec {
  requires int.ge(n, 0);
  ensures [finished]: i == n;
  ensures [preserved]: r == 7;
}
{
  r := 7;
  i := 0;
  while (int.lt(i, n))
    invariant int.le(0, i)
    invariant int.le(i, n)
  {
    var next : int := int.add(i, 1);
    i := next;
  }
};
#end
#core_reflect framedLoopPgm

theorem framedLoop_verified : Hoare.Verified framedLoop := by
  unfold framedLoop
  tagless_vcgen <;> grind

-- Nested loops retain unchanged inputs and the outer counter through the inner loop.
def nestedLoopsPgm :=
#strata
program Core;
procedure nestedLoops(n : int, m : int, out i : int, out j : int)
spec {
  requires int.ge(n, 0);
  requires int.ge(m, 0);
  ensures i == n;
}
{
  i := 0;
  while (int.lt(i, n))
    invariant int.le(0, i)
    invariant int.le(i, n)
  {
    j := 0;
    while (int.lt(j, m))
      invariant int.le(0, j)
      invariant int.le(j, m)
    {
      j := int.add(j, 1);
    }
    i := int.add(i, 1);
  }
};
#end
#core_reflect nestedLoopsPgm

theorem nestedLoops_verified : Hoare.Verified nestedLoops := by
  unfold nestedLoops
  tagless_vcgen <;> grind

-- old(g) is an entry snapshot throughout the loop.
def oldLoopPgm :=
#strata
program Core;
procedure oldLoop(n : int, inout g : int)
spec {
  requires int.le(g, n);
  ensures g == n;
  ensures int.le(old(g), g);
}
{
  while (int.lt(g, n))
    decreases int.sub(n, g)
    invariant int.le(old(g), g)
    invariant int.le(g, n)
  {
    g := int.add(g, 1);
  }
};
#end
#core_reflect oldLoopPgm

theorem oldLoop_verified : Hoare.Verified oldLoop := by
  unfold oldLoop
  tagless_vcgen <;> grind

-- Division and remainder generate a nonzero-divisor obligation.
def quotientRemainderPgm :=
#strata
program Core;
procedure quotientRemainder(n : int, d : int, out q : int, out r : int)
spec {
  requires d != 0;
  ensures q == int.div(n, d);
  ensures r == int.mod(n, d);
}
{
  q := int.div(n, d);
  r := int.mod(n, d);
};
#end
#core_reflect quotientRemainderPgm

theorem quotientRemainder_verified : Hoare.Verified quotientRemainder := by
  unfold quotientRemainder
  tagless_vcgen <;> grind

-- Havoc is universal, and assume restricts subsequent obligations.
def havocAssumePgm :=
#strata
program Core;
procedure havocAssume(out r : int)
spec { ensures int.ge(r, 0); }
{
  havoc r;
  assume int.ge(r, 0);
  assert [nonnegative]: int.ge(r, 0);
};
#end
#core_reflect havocAssumePgm

theorem havocAssume_verified : Hoare.Verified havocAssume := by
  unfold havocAssume
  tagless_vcgen <;> grind

-- Fresh nondeterministic declarations work at both supported types.
def localHavocPgm :=
#strata
program Core;
procedure localHavoc(out r : int)
spec { ensures int.ge(r, 0); }
{
  var chosen : int;
  var flag : bool;
  assume flag;
  assume int.ge(chosen, 0);
  r := chosen;
};
#end
#core_reflect localHavocPgm

theorem localHavoc_verified : Hoare.Verified localHavoc := by
  unfold localHavoc
  tagless_vcgen <;> grind

-- A free requires remains an assumption of the body's verification.
def freeRequiresPgm :=
#strata
program Core;
procedure freeRequires(n : int, out r : int)
spec { free requires int.ge(n, 0); ensures int.ge(r, 0); }
{ r := n; };
#end
#core_reflect freeRequiresPgm

theorem freeRequires_verified : Hoare.Verified freeRequires := by
  unfold freeRequires
  tagless_vcgen <;> grind

-- Partial correctness does not require this infinite loop to establish false.
def divergingPgm :=
#strata
program Core;
procedure diverging()
spec { ensures false; }
{ while (true) {} };
#end
#core_reflect divergingPgm

theorem diverging_verified : Hoare.Verified diverging := by
  unfold diverging
  tagless_vcgen <;> grind

-- But an earlier assertion must hold even when execution subsequently diverges.
def assertThenDivergePgm :=
#strata
program Core;
procedure assertThenDiverge()
spec { ensures true; }
{ assert [before_loop]: false; while (true) {} };
#end
#core_reflect assertThenDivergePgm

theorem assertThenDiverge_refuted : ¬ Hoare.Verified assertThenDiverge := by
  unfold assertThenDiverge
  refute_tagless

def assertThenAssumePgm :=
#strata
program Core;
procedure assertThenAssume()
spec { ensures true; }
{ assert false; assume false; };
#end
#core_reflect assertThenAssumePgm

theorem assertThenAssume_refuted : ¬ Hoare.Verified assertThenAssume := by
  unfold assertThenAssume
  refute_tagless

def assumeThenAssertPgm :=
#strata
program Core;
procedure assumeThenAssert()
spec { ensures false; }
{ assume false; assert false; };
#end
#core_reflect assumeThenAssertPgm

theorem assumeThenAssert_verified : Hoare.Verified assumeThenAssert := by
  unfold assumeThenAssert
  tagless_vcgen <;> grind

def zeroDivisorPgm :=
#strata
program Core;
procedure zeroDivisor(out r : int)
spec { ensures true; }
{ r := int.div(1, 0); };
#end
#core_reflect zeroDivisorPgm

theorem zeroDivisor_refuted : ¬ Hoare.Verified zeroDivisor := by
  unfold zeroDivisor
  refute_tagless

-- Undefined assumptions are ignored, not treated as impossible paths.
def undefinedAssumptionPgm :=
#strata
program Core;
procedure undefinedAssumption()
spec { ensures true; }
{ assume int.div(1, 0) == 0; assert false; };
#end
#core_reflect undefinedAssumptionPgm

theorem undefinedAssumption_refuted : ¬ Hoare.Verified undefinedAssumption := by
  unfold undefinedAssumption
  refute_tagless

def badInvariantPgm :=
#strata
program Core;
procedure badInvariant(out i : int)
spec { ensures true; }
{
  i := 0;
  while (false) invariant int.lt(i, 0) {}
};
#end
#core_reflect badInvariantPgm

theorem badInvariant_refuted : ¬ Hoare.Verified badInvariant := by
  unfold badInvariant
  refute_tagless

-- Entry is valid here; it is the body that breaks the invariant.
def brokenPreservationPgm :=
#strata
program Core;
procedure brokenPreservation(out i : int)
spec { ensures true; }
{
  i := 0;
  while (int.lt(i, 1)) invariant i == 0 { i := 1; }
};
#end
#core_reflect brokenPreservationPgm

theorem brokenPreservation_refuted : ¬ Hoare.Verified brokenPreservation := by
  unfold brokenPreservation Hoare.Verified
  tagless_embed
  dsimp only [Hoare.interpret, Hoare.interpretation]
  rw [Hoare.triple_iff]
  intro h
  have bad := h ⟨fun _ => 0, fun _ => false⟩ (by tagless_lift)
  tagless_lift
  simp only [Hoare.Obligation] at bad
  have badAtZero := bad.2 ⟨fun _ => 0, fun _ => false⟩
  simp at badAtZero

-- Body assertions remain obligations even when the loop never exits.
def assertionInLoopPgm :=
#strata
program Core;
procedure assertionInLoop()
spec { ensures true; }
{ while (true) invariant true { assert [inside_loop]: false; } };
#end
#core_reflect assertionInLoopPgm

theorem assertionInLoop_refuted : ¬ Hoare.Verified assertionInLoop := by
  unfold assertionInLoop
  refute_tagless

def negativeMeasurePgm :=
#strata
program Core;
procedure negativeMeasure()
spec { ensures true; }
{ while (false) decreases int.neg(1) {} };
#end
#core_reflect negativeMeasurePgm

theorem negativeMeasure_refuted : ¬ Hoare.Verified negativeMeasure := by
  unfold negativeMeasure
  refute_tagless

def unchangedMeasurePgm :=
#strata
program Core;
procedure unchangedMeasure()
spec { ensures true; }
{ while (true) decreases 0 {} };
#end
#core_reflect unchangedMeasurePgm

theorem unchangedMeasure_refuted : ¬ Hoare.Verified unchangedMeasure := by
  unfold unchangedMeasure
  refute_tagless

-- A nondeterministic branch requires both alternatives to establish the contract.
def choicePgm :=
#strata
program Core;
procedure choice(out r : int)
spec { ensures r == 1 || r == 2; }
{ if * { r := 1; } else { r := 2; } };
#end
#core_reflect choicePgm

theorem choice_verified : Hoare.Verified choice := by
  unfold choice
  tagless_vcgen <;> grind

-- Unsupported source is diagnosed before vcgen attempts to prove a triple.
def coveragePgm :=
#strata
program Core;
procedure coverage()
spec { ensures true; }
{ cover [unhandled]: true; };
#end
#core_reflect coveragePgm

/-- error: tagless embedding failed: "coverage checks are not supported" -/
#guard_msgs in
example : Hoare.Verified coverage := by
  unfold coverage
  tagless_vcgen

-- Naming a VC is presentation only; the underlying obligation remains P.
example (P : Prop) (h : P) : Hoare.Obligation "source_clause" P := by
  tagless_label
  case source_clause => exact h

end Strata.Tagless.Regression
