# Proving Boole contracts in Lean

A **predicate transformer** answers a question about a command. If I want a
certain fact to hold **after** the command, what do I need to establish
**before** it?

Take `max2`. Its postcondition says that the returned value `r` is at least as
large as both inputs.

```text
if x ≥ y then r := x else r := y
ensures r ≥ x ∧ r ≥ y
```

Start at the end and work backward. Before `r := x`, the postcondition becomes
`x ≥ x ∧ x ≥ y`, because the assignment will give `r` the value of `x`.
Likewise, before `r := y`, it becomes `y ≥ x ∧ y ≥ y`. The conditional tells
us when we need each fact, so the precondition of the whole body is equivalent
to these two goals:

```text
x ≥ y  →  x ≥ x ∧ x ≥ y
x < y  →  y ≥ x ∧ y ≥ y
```

Both follow by arithmetic. For a procedure with a `requires` clause, you may
use that clause as an assumption when proving the condition for its body.

## Running the verifier

```lean
import StrataDDM.Integration.Lean.HashCommands
import StrataBoole.Boole.Hoare.Reflect

open Strata.Boole.Hoare

def maximum :=
#strata
program Boole;
procedure max2(x : int, y : int) returns (r : int)
spec { ensures r >= x && r >= y; }
{ if (x >= y) { r := x; } else { r := y; } };
#end

theorem maximum_correct : VerifiedSource (boole% maximum) "max2" := by
  boole_vcgen <;> grind
```

`boole%`, defined in [Reflect.lean](Reflect.lean), quotes the parsed Boole AST
and its name context into Lean. [Compile.lean](Compile.lean) walks that AST,
resolves names, and builds the procedure's transformer. It builds a branch
from the guard and the two assignment transformers in the example above.
By the time `vcgen` runs, it has a transformer over Boole states to work with.

[Rules.lean](Rules.lean) defines what each transformer does and registers the
rules `vcgen` applies. A sequence works backward through its commands.
An assertion adds a goal at that point, while an assumption limits the paths
that continue past it. Havoc checks the continuation for every value it can
choose. For a loop, the compiler records the variables the body may write.
The loop rule checks the invariant at entry and after an iteration, and uses
the invariant with the false guard to prove the condition after the loop.
A supplied measure adds obligations for nonnegativity and decrease.

[Certificate.lean](Certificate.lean) states the procedure-level goal as
`VerifiedSource`. It asks whether the body's transformer, applied to the
ordinary ensures, holds at every typed entry that satisfies the requires.
The `boole_vcgen` tactic reduces the compiler application and hands its
transformer to Lean's `vcgen`. In the example, `grind` finishes the arithmetic.
[Examples.lean](Examples.lean) includes loops, `old` values, and
nondeterministic choices.

## Scope

The verifier supports scalar expressions, structured procedures, local
variables, assignments, global `modifies` and `old`, assertions, assumptions,
havoc, conditionals, while loops, and labelled exits. Calls, for loops,
choose, cover, quantifiers, compound types, and integer division and remainder
are outside the current fragment.

The Core compatibility theorem aims to show that a Boole certificate implies
Strata's `contractTriple` for the checked Core lowering. The first proof
fragment is narrower than the verifier's. The standalone Boole soundness
statement is about Boole's own denotation. See the
[proof plan](Compatibility/ProofPlan.md) for the details.
