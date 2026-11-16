/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

import all StrataBoole.Boole.Hoare.Certificate
import all StrataBoole.Boole.Hoare.Compile
import all StrataBoole.Boole.Hoare.Rules
import all StrataBoole.Boole.Runtime
import all StrataBoole.Boole.Interp
import all StrataBoole.Boole.Types
import all StrataDDM.AST
import StrataDDM.Integration.Lean.HashCommands
import StrataBoole.Boole.Hoare.Reflect
meta import StrataBoole.Boole.Hoare.Reflect
meta import StrataBoole.Grammar

namespace Strata.Boole.Hoare.Examples

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option mvcgen.warning false

def maximum :=
#strata
program Boole;
procedure max2(x : int, y : int) returns (r : int)
spec {
  ensures [bounds]: r >= x && r >= y;
  ensures [chosen]: r == x || r == y;
}
{
  if (x >= y) { r := x; } else { r := y; }
};
#end

theorem max2_correct : VerifiedSource (boole% maximum) "max2" := by
  boole_vcgen <;> grind

def counting :=
#strata
program Boole;
procedure count(n : int) returns (r : int)
spec { requires n >= 0; ensures r == n; }
{
  r := 0;
  while (r < n)
    decreases n - r
    invariant 0 <= r
    invariant r <= n
  { r := r + 1; }
};
#end

theorem counting_correct : VerifiedSource (boole% counting) "count" := by
  boole_vcgen <;> grind

def framed :=
#strata
program Boole;
var g : int;
procedure inc(n : int) returns (r : int)
spec {
  modifies g;
  requires n >= 0;
  ensures g == old(g) + 1 && r == n;
}
{
  g := g + 1;
  r := 0;
  while (r < n)
    invariant r <= n
  {
    var next : int := r + 1;
    r := next;
  }
};
#end

theorem framed_correct : VerifiedSource (boole% framed) "inc" := by
  boole_vcgen <;> grind

def nestedLoops :=
#strata
program Boole;
procedure nested(n : int) returns (r : int)
spec { requires n >= 0; ensures r == n; }
{
  r := 0;
  while (r < n)
    invariant r <= n
  {
    var j : int := 0;
    while (j < 1)
      invariant j <= 1
    { j := j + 1; }
    r := r + j;
  }
};
#end

theorem nestedLoops_correct : VerifiedSource (boole% nestedLoops) "nested" := by
  boole_vcgen
  constructor
  · assumption
  intro r inv
  split
  · constructor
    · trivial
    intro j invJ
    split <;> omega
  · omega

def scopedProgram :=
#strata
program Boole;
procedure scoped(x : int) returns (r : int)
spec { ensures r == x + 1; }
{
  r := x;
  inner: {
    var temporary : int;
    temporary := x + 1;
    r := temporary;
    exit inner;
    assert false;
  }
  exit scoped;
  assert false;
};
#end

theorem scoped_correct : VerifiedSource (boole% scopedProgram) "scoped" := by
  boole_vcgen <;> grind

def nondeterministic :=
#strata
program Boole;
procedure pick() returns (r : int)
spec { ensures r >= 0; }
{
  havoc r;
  if * { assume r >= 0; } else { r := 0; }
  while *
    invariant r >= 0
  { exit pick; }
};
#end

theorem nondeterministic_correct : VerifiedSource (boole% nondeterministic) "pick" := by
  boole_vcgen <;> grind

def toggle :=
#strata
program Boole;
procedure toggle(b : bool) returns (r : bool)
spec { ensures r == !b; free ensures false; }
{ r := !b; };
#end

theorem toggle_correct : VerifiedSource (boole% toggle) "toggle" := by
  boole_vcgen <;> grind

def add8 :=
#strata
program Boole;
procedure add8(a : bv W8, b : bv W8) returns (r : bv W8)
spec { ensures r == b + a; }
{ r := a + b; };
#end

theorem add8_correct : VerifiedSource (boole% add8) "add8" := by
  boole_vcgen <;> simp [BitVec.add_comm]

def natAddition :=
#strata
program Boole;
procedure natAddition() returns (r : int)
spec { ensures r == 5; }
{ r := nat_toInt(nat_add(nat_fromInt(2), nat_fromInt(3))); };
#end

theorem natAddition_correct : VerifiedSource (boole% natAddition) "natAddition" := by
  boole_vcgen <;> decide

def localChoice :=
#strata
program Boole;
procedure localChoice() returns (r : int)
spec { ensures r >= 0; }
{
  var n : int;
  assume n >= 0;
  r := n;
};
#end

theorem localChoice_correct : VerifiedSource (boole% localChoice) "localChoice" := by
  boole_vcgen <;> grind

def unreachable :=
#strata
program Boole;
procedure unreachable()
spec { ensures false; }
{
  assume false;
  assert false;
};
#end

theorem unreachable_correct : VerifiedSource (boole% unreachable) "unreachable" := by
  boole_vcgen

def invalidBodies :=
#strata
program Boole;
procedure beforeLoop() { assert false; while (true) {} };
procedure beforeAssume() { assert false; assume false; };
procedure badInvariant() { while (false) invariant false {} };
procedure badMeasure() { while (true) decreases 0 {} };
#end

local macro "refute_closed_certificate" : tactic => `(tactic| (
  intro h
  cbv at h
  simp only [checked, Prepared.Valid, forValues] at h
  have failure := (h True.intro).le_wp _ rfl
  boole_lift
  all_goals simp [Obligation] at failure))

theorem assertionBeforeLoop_rejected : ¬ VerifiedSource (boole% invalidBodies) "beforeLoop" := by
  refute_closed_certificate

theorem assertionBeforeAssume_rejected : ¬ VerifiedSource (boole% invalidBodies) "beforeAssume" := by
  refute_closed_certificate

theorem badInvariant_rejected : ¬ VerifiedSource (boole% invalidBodies) "badInvariant" := by
  refute_closed_certificate

theorem badMeasure_rejected : ¬ VerifiedSource (boole% invalidBodies) "badMeasure" := by
  refute_closed_certificate

private def inputWrite :=
#strata
program Boole;
procedure invalid(x : int) { x := 0; };
#end

private def outputRequires :=
#strata
program Boole;
procedure invalid() returns (r : int)
spec { requires r == 0; }
{ r := 0; };
#end

private def oldRequires :=
#strata
program Boole;
var g : int;
procedure invalid()
spec { modifies g; requires old(g) == 0; }
{ g := 0; };
#end

private def callProgram :=
#strata
program Boole;
procedure callee() { };
procedure caller() { call callee(); };
#end

#guard !(prepareSource (boole% inputWrite) "invalid").isOk
#guard !(prepareSource (boole% outputRequires) "invalid").isOk
#guard !(prepareSource (boole% oldRequires) "invalid").isOk
#guard !(prepareSource (boole% callProgram) "caller").isOk
#guard !(prepareSource (boole% maximum) "missing").isOk

end Strata.Boole.Hoare.Examples
