# Proving Boole contracts directly with Hoare

### Weakest-precondition transformers

This folder builds Hoare logic directly from the Boole AST. The aim is to
let Boole develop as its own language while reusing its state and
expression definitions, without adding an execution semantics for commands.

A **predicate transformer** answers the question we start with in a Hoare
proof. If we want a fact to hold **after** a command, what must hold
**before** it? The compiler builds the transformer recursively from the AST.  
Applying it to a postcondition computes the weakest precondition (WP).  
Plugging this into Lean's `vcgen`, with the registered Hoare rules, exposes the proof obligations.

In line with Dijkstra's healthiness conditions, each transformer comes with a proof of monotonicity. If postcondition  
`P` implies `Q` at every exit, then the weakest precondition for `P`
implies the weakest precondition for `Q`.

### Example

The body of `max2` assigns the larger of its two inputs to `r`.

```text
if x ≥ y then r := x else r := y
ensures r ≥ x ∧ r ≥ y
```

The compiler builds up the overall Transformer object as follows:

```text
xExpr       := Expression.read (.local "x")
yExpr       := Expression.read (.local "y")
guard       := binary .ge xExpr yExpr
assignX     := Transformer.step (Transformer.assignState (.local "r") xExpr)
assignY     := Transformer.step (Transformer.assignState (.local "r") yExpr)
thenBranch  := Transformer.scope assignX
elseBranch  := Transformer.scope assignY
conditional := Transformer.branch (some guard) thenBranch elseBranch
body        := Transformer.block "max2" (Transformer.scope conditional)
```

Let `Q` require `r ≥ x ∧ r ≥ y` on normal completion, and let `s` be a
typed entry state. The scopes introduce no locals and the body has no
labelled exits. The block and scope wrappers therefore leave the
condition unchanged for this example. Unfolding the branch rule gives
the nested transformer calls.

```text
body.transform Q s
  ↔ conditional.transform Q s
  ↔ test (some guard) s
      (thenBranch.transform Q s)
      (elseBranch.transform Q s)
```

Here `test` evaluates the guard in `s` and selects the corresponding
precondition. On the then branch, the assignment requires
`Q none (s[r ↦ x])`. On the else branch, it requires
`Q none (s[r ↦ y])`. The two guarded obligations are therefore

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

[Compatibility.lean](Compatibility.lean) states the intended guarantee
for the Core bridge fragment. A Boole certificate implies Strata's
`contractTriple` for the checked Core lowering. The bridge fragment is
narrower than the verifier's supported language.

## Sources

- Weakest preconditions, monotonicity, and the derivation of a maximum-of-two
  program in §§3–4. [E. W. Dijkstra, *Guarded Commands, Nondeterminacy and Formal Derivation of Programs* (1975)](https://www.cs.utexas.edu/~EWD/transcriptions/EWD04xx/EWD472.html)
- A small imperative verifier built with a `WP` instance and `@[spec]`
  rules. [Ilya Sergey’s `vcgen` tutorial](https://github.com/ilyasergey/lean-vcgen-tutorial)
