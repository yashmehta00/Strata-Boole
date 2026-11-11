# Tagless Core verification: internal brief

## Purpose and status

The goal is a Lean backend whose certificates imply correctness under Strata
Core's existing semantics, with little additional trusted machinery. The current
prototype generates and proves conditions for a structured integer/Boolean
fragment. Its verification rules and example certificates are proved; the Core
soundness theorem and seven other source-facing proofs still contain `sorry`.

The following example follows the actual `increment` procedure in
[Hoare/Examples.lean](Hoare/Examples.lean). Its `increment_conditions` theorem
checks the displayed precondition, postcondition, and transformed postcondition
against the implementation. This is a walkthrough of what exists, not a proposed
second pipeline.

## A small example through every step

### 1. Start with Core source, including its specification

```text
procedure increment(n : int, out r : int)
spec {
  requires int.ge(n, 0);
  ensures int.gt(r, 0);
}
{
  r := int.add(n, 1);
};
```

The contract asks us to show that a nonnegative input produces a positive
output. `n` is read-only; `r` is an output and may be assigned.

### 2. Obtain the typed Core AST

The existing `#core_reflect` frontend translates and type-checks the source and
creates `increment : Core.Procedure`. In a readable summary of that AST:

```text
header:   input n : int; output r : int
requires: Int.Ge(read n, integer 0)
body:     set r (Int.Add(read n, integer 1))
ensures:  Int.Gt(read r, integer 0)
```

This is data, with type annotations on variable/operator occurrences. Our
current source guarantee starts at this `Core.Procedure`; correctness of parsing,
Boole translation, and the reflection implementation is outside that guarantee.

### 3. embedCore creates three recipes

```lean
embedCore increment : Except String (PredRecipe × CmdRecipe × PredRecipe)
```

`Embed.lean` checks the supported types, annotations, scope, and assignments. It
then produces functions waiting for an `Interpretation`. A readable rendering of
this example's recipes is below. `preInfo` and `postInfo` stand for the captured
source clause labels/attributes/metadata, not additional semantic objects.

```lean
let requiresRecipe : PredRecipe := fun I =>
  I.andPred
    (I.requiresClause preInfo (I.ge (I.read .int "n") (I.intLiteral 0)))
    I.truePred

let programRecipe : CmdRecipe := fun I =>
  I.seq
    (I.seq (I.havoc .int "r") I.skip)  -- output initialization
    (I.block []                       -- no body-local variables
      (I.seq
        (I.assign .int "r" (I.add (I.read .int "n") (I.intLiteral 1)))
        I.skip))

let ensuresRecipe : PredRecipe := fun I =>
  I.andPred
    (I.ensuresClause postInfo (I.gt (I.read .int "r") (I.intLiteral 0)))
    I.truePred
```

The output starts arbitrary because an `out` parameter has no particular initial
value. The body subsequently overwrites it. The `skip` and block wrappers above
are retained to show the structure the implementation actually creates.

A recipe is not another AST and does not yet choose what addition or assignment
means: those calls go through `I`. This is a final-style representation of the
accepted fragment; the original input remains deeply represented Core syntax.
That distinction follows the tagless-final literature. [1]

### 4. The Hoare interpretation supplies the meanings

Applying `Hoare.interpret` to the three recipes produces:

```lean
P       : State → Prop
command : Transformer
Q       : State → Prop
```

`State` has native integer and Boolean slots for variable names. The predicates
for this example simplify to:

```lean
P := fun σ => 0 ≤ σ.ints "n"
Q := fun σ => 0 < σ.ints "r"
```

The command is neither a final state nor another list of statements. Its main
field has type:

```lean
command.transform : (State → Prop) → State → Prop
```

Its other field proves monotonicity, as required by the WP adapter: if one
postcondition implies another, its generated requirement implies the other's.

It accepts an arbitrary desired final condition `R` and describes the initial
states sufficient to establish it. In this example its meaning simplifies to:

```lean
command.transform R σ ↔
  ∀ r₀ : Int,
    R ((σ.write .int "r" r₀).write .int "r" (σ.ints "n" + 1))
```

The first write represents output initialization; the second represents the
assignment. Since the second overwrites the first, this is equivalent to:

```lean
R (σ.write .int "r" (σ.ints "n" + 1))
```

Expression values use Lean arithmetic. Their separate definedness predicates
ensure that partial operations, such as division by zero, cannot be silently
justified by Lean's total arithmetic conventions. This example uses only total
operations, so those side conditions simplify to `True`.

### 5. transform is applied to the actual ensures

Substitute `Q` for the arbitrary `R`:

```lean
command.transform Q σ ↔ 0 < σ.ints "n" + 1
```

This is what the transform step produces: the condition needed before running
the procedure to establish its postcondition. It does not yet use `P`.

Sequencing explains how the backwards reasoning happens:

```lean
(first.seq second).transform Q = first.transform (second.transform Q)
```

`embedStmts` traverses the source structurally and constructs the sequence;
transformer composition sends the requested postcondition backwards through it.
No operational execution is performed backwards.

### 6. vcgen helps prove that requires establishes that condition

Our WP instance exposes `.transform` to Lean's verification framework. The goal
`Triple P command Q` therefore means:

```lean
∀ σ, P σ → command.transform Q σ
```

For this example, after checked normalization, the obligation is:

```lean
∀ σ, 0 ≤ σ.ints "n" → 0 < σ.ints "n" + 1
```

The actual certificate is proved with:

```lean
theorem increment_correct : Hoare.Verified increment := by
  unfold increment
  tagless_vcgen <;> grind
```

`tagless_vcgen` first retains a proved equation for successful embedding. It then
calls `vcgen` on the framework triple, using the proved `@[spec]` operation
rules, and simplifies the resulting predicates with `tagless_lift`. The
attribute registers rules for lookup; it does not prove them or establish their
meaning in Core. Nested loop-body WPs can also be normalized by `tagless_lift`.
The WP-plus-rules interface is described in the vcgen tutorial. [2]

Thus `Verified increment` contains both the checked embedding equation and the
interpreted contract proof. There is no additional manually maintained
per-program unfolding theorem.

### 7. The universal source theorem supplies the Core conclusion

Once `verified_implies_core_correct` is proved, this certificate will imply that
Core execution satisfies all encountered assertions and, on normal completion,
the original `ensures int.gt(r, 0)` under the run's assumptions.

This last connection is still unfinished. The example certificate currently
proves the interpreted contract; it does not yet establish the Core conclusion
without the admitted source theorem. Neither conclusion asserts termination.

## What changes compared with the deep experiment prototype?

The comparison is with the implementation in `StrataBoole/Deep/`, not with an
imagined unverified alternative.

| Part | Deep experiment prototype | Tagless Hoare route |
|---|---|---|
| Expressions | `eval` traverses Core expressions into `Option Val` | Embedding creates typed expression recipes; interpretation supplies native values and definedness |
| Command meaning | A separate `Exec` relation with normal/failure outcomes | Compositional predicate transformers |
| Contract meaning | `semWP` quantifies over `Exec` outcomes | `P` implies the command's generated requirement for `Q` |
| Proof automation | `core_vcgen` applies `wp_set`, `wp_loop`, etc. | Lean `vcgen` applies registered transformer rules, followed by simplification |
| Required source proof | Relate the experiment's semantics/contracts to original Core | Relate generated requirements/contracts directly to original Core |

The deep experiment's [Exec.lean](../Deep/Exec.lean) defines outcomes, supported
forms, assignment/failure cases, branching, loop checks, and framing. Its
[Spec.lean](../Deep/Spec.lean) proves rules using those execution constructors.
That is a sound standard organization relative to its `Exec`; it is not
unnecessary mathematics. It gives triples an independent operational meaning
and provides an execution relation that other developments can reuse.

For this project's verification route, however, Core already supplies the
execution semantics we ultimately want. Defining an additional `Exec` creates
another semantic description to maintain and relate to that target. Our
transformer operations describe the conditions we need directly. Assignment,
for example, has one formula for definedness and the updated postcondition;
its registered rule follows from that formula. The substantial proof is then
against existing Core execution, not against another newly defined execution
relation first.

The recipe has a specific role in that design: it separates source processing
from condition construction. `Embed.lean` handles syntax, scopes, type checks,
output initialization, snapshots, and clause structure. The Hoare interpretation
handles native expression meanings and logical requirements. The Hoare route
does real condition construction; it does not rebuild a Core AST and hand it
back to the deep experiment verifier.

The current typed expressions and typed havoc also avoid the deep experiment's
single `Val` type and value projections in the resulting goals. That is a benefit
of this implementation's typed semantic interface, not a property exclusive to
tagless encodings; a deep implementation could adopt it too.

**Recommendation.** For a backend whose immediate job is to produce conditions
and prove them sound against existing Core, this direct transformer organization
is a reasonable fit. It avoids a second execution relation and a bespoke rule
application tactic while keeping source handling separate from the logic. The
recipe layer additionally allows that source handling to be reused by other
interpretations.

**Limits of the comparison.** A direct recursive transformer over Core could
obtain many of the same verification benefits without recipes. Recipes cost an
interface and a specialization step; they are justified by this separation and
reuse, not by a correctness theorem that only tagless encodings can have. We
have not established fewer proof lines, faster verification, or a smaller TCB
than a completed deep experiment backend. Its existing proofs are useful design
references. Our direct Core proof might be harder in places than proving rules
about its simpler `Exec`.

Both designs can have one overall source soundness theorem. Removing `Exec`
changes the intermediate obligations; it does not make source correspondence
free. In particular, our transformer triple has its intended execution meaning
only after the source soundness proof is completed. An error in a transformer
could be consistent with its own proved rules and still fail that proof.

## Guarantees and proof organization

Source-facing guarantees live in `Hoare/Guarantees/`:

- **`Soundness.lean`** contains `verified_implies_core_correct` and its supporting
  typing, expression, statement, contract, assertion, and framing facts. The main
  statement names actual Core traces, every consistent Core factory model, and
  admitted entry environments. It checks every finite prefix, so a failed
  assertion before an infinite loop is not hidden by nontermination.
- **`EntryAdmission.lean`** contains `satisfying_inputs_admit_core_entry_state`.
  Every defined native input satisfying requires must have an admissible Core
  entry environment representing those same inputs. This is independent of a
  `Verified` certificate and guards against accidental vacuity in the entry gate;
  it does not say every contract has a satisfying input.
- **`CoreState.lean`** holds their shared entry parameters and store-denotation
  relation. It introduces no new execution semantics or admitted theorem.

Existence of a consistent Core model is already established upstream by
`Core.factoryInterp_nonempty` in `Strata.Languages.Core.Logic.FactoryInterp`;
we reuse that result rather than create a duplicate theorem. Its dependencies
need the same trust review as the final source guarantee.

No-stuck execution is a separate possible guarantee, not a consequence of the
current theorem. For example, verification discards everything following
`assume false`, whereas Core event execution records that assumption and can
continue to commands such as division by zero. A progress statement must account
for feasible assumptions, rather than quantify unconditionally over all such
syntactic execution prefixes. It must also distinguish a normal `.terminal`
configuration from a stuck one. Source-text correspondence needs a specified frontend relation;
native execution correspondence needs an executable interpretation. Neither is
invented as a placeholder theorem over unspecified components here. Termination
and completeness are likewise outside the present claim.

## Boundaries and next work

The working fragment includes structured, call-free integer/Boolean procedures,
locals, assignment, havoc, assertions/assumptions, scoped blocks, deterministic
or nondeterministic branches, contracts, old snapshots, and deterministic loops.
Loops generate invariant entry/preservation/exit obligations, preserve facts
about unwritten variables, and check optional measures. These are sufficient
conditions based on supplied invariants, not exact semantic weakest liberal
preconditions for arbitrary loops. Inadequate invariants can block verification
of a correct program, including in a verifier based on semantic WP. [3]

Unsupported types, calls, CFGs, maps, quantifiers, coverage, exits, and local type
declarations are rejected. Boolean binary operations currently impose conservative
strict definedness; conditional expressions require only the selected branch.
Ordinary/free requires are body assumptions; ordinary ensures are obligations;
free ensures are not proved guarantees. Undefined requires/assumptions supply no
information and cannot discard a path. Global axioms are not used as assumptions.

Next: complete the source proofs, pass the final dependency audit, and demonstrate
an example ending in the Core conclusion. Existing backend entry points have not
been replaced. Integrating them requires matching their correctness property,
factory/entry assumptions, and verification mode to the proved guarantee.

The intended trust benefit is checked proofs from Core certificates, not the
word “tagless.” Lean checks generated proof terms; a verified deep embedding can
have the same trust boundary. The kernel and accepted foundational axioms remain
in the logical trust basis, and the specification still needs to describe the
intended language. [4]

One inherited issue remains: Core's factory uses `native_decide`, whose generated
axiom occurs in the source theorem dependencies. This adds compiler trust. [5]
The audit permits only `sorryAx` and that explicitly named inherited axiom for
the eight listed source theorems while admitted. Completed theorems, including
rules and program certificates, permit only the standard foundational axioms.
A finished source theorem must meet that same strict policy; the current
prototype is not yet a backend with no additional evaluation axioms.

## Reading map and references

`Interface.lean` defines operations; `Embed.lean` builds recipes.
`Hoare/Interpretation.lean` defines meanings; `Hoare/Rules.lean` connects them to
WP; `Hoare/Certificate.lean` provides certificates/tactics. Start with
`Hoare/Examples.lean` for programs and the checked walkthrough equations.

1. [Kiselyov, Tagless-final style](https://okmij.org/ftp/tagless-final/).
2. [Sergey, lean-vcgen-tutorial: implementation guide](https://github.com/ilyasergey/lean-vcgen-tutorial/blob/master/docs/Verifier.md),
   especially semantic versus syntactic WP and registered rules. Our adapter uses
   the pinned Lean 4.34.0 `Std.Internal.Do` API.
3. [Software Foundations, Hoare Logic, Part II](https://softwarefoundations.cis.upenn.edu/plf-current/Hoare2.html).
4. [Lean reference: the kernel](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/#the-kernel).
5. [Lean reference: native_decide](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#native_decide).
