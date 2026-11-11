# Tagless Core embedding

For the design rationale, trust boundary, and remaining work, read
[internal-brief.md](internal-brief.md).

Start with [Hoare/Examples.lean](Hoare/Examples.lean), then
[Hoare/Regression.lean](Hoare/Regression.lean). Programs use real
`#strata program Core; … #end` syntax, with contracts and adjacent Lean proofs.
Stephanie's existing `#core_reflect` front end supplies the typed Core AST.

**Current guarantee:** `Hoare.Verified p` certifies successful embedding and the
interpreted transformer contract. **The universal theorem connecting that
certificate to original Core execution is not proved yet.** Its exact statement
and supporting lemmas are in `Hoare/Guarantees/Soundness.lean`. The main theorem,
`verified_implies_core_correct`, follows its supporting lemmas in Lean declaration order;
unfinished proofs use `sorry`. Verifier rules and program certificates remain
independent of those proof placeholders.

## Files and pipeline

Shared infrastructure stays directly in `Tagless/`; backend files stay in `Hoare/`.

- `Interface.lean`: supported types and the operations supplied by a backend.
- `Embed.lean`: Core traversal for recipe construction, static checks, contracts and procedure setup.
- `Hoare/Interpretation.lean`: native expression values with definedness predicates,
  logical states, and monotone predicate transformers.
- `Hoare/Rules.lean`: proved transformer rules and the adapter to Lean's `WP` interface.
- `Hoare/Certificate.lean`: `Verified`, embedding diagnostics, clause-based goal names,
  and the thin `tagless_vcgen` tactic.
- `Hoare/Guarantees/Soundness.lean`: proved typing/transformer lemmas and the explicit remaining
  original-Core correspondence statements.
- `Hoare/Guarantees/EntryAdmission.lean`: the independent statement that defined,
  satisfying native inputs admit corresponding Core procedure-entry environments.
- `Hoare/Guarantees/CoreState.lean`: entry parameters and store-denotation definitions
  shared by those two guarantees; no additional execution semantics.
- `Hoare/Examples.lean`: introductory examples, including max2 and measured loops.
- `Hoare/Regression.lean`: framing, nesting, snapshots, partial arithmetic,
  nondeterminism, assertion ordering, and deliberately invalid annotations.
- `Hoare/Audit.lean`: checks every theorem in this namespace for unexpected axioms.
- `Tests.lean`: deliberately malformed ASTs and static rejection checks.

```lean
embedCore p : Except String (PredRecipe × CmdRecipe × PredRecipe)
--                            requires     program     ensures
```

The recipes are functions waiting for an `Interpretation`, not another AST.
For example, the recipe for `r := n + 1` is essentially:

```lean
fun I => I.assign .int "r" (I.add (I.read .int "n") (I.intLiteral 1))
```

Applying `Hoare.interpret` gives `(P, command, Q)`. A command is a transformer:
`command.transform Q` describes sufficient conditions for establishing `Q` while
passing the program's checks. The public certificate packages successful embedding
and `∀ σ, P σ → command.transform Q σ` through Lean's `Triple` interface.

```lean
theorem max2_correct : Hoare.Verified max2 := by
  unfold max2
  tagless_vcgen <;> grind
```

`tagless_vcgen` diagnoses embedding failures, specializes the recipes using
kernel-checked equations, invokes Lean `vcgen`, and simplifies the resulting state
formulas. Source clause labels name remaining goals before their transparent
wrappers are removed. A goal containing several clauses takes the first label;
this is not yet one separate goal per source clause.

Loop VCs contain nested body WPs; their remaining transformer equations are
normalized by `tagless_lift`. The Hoare interpretation does not traverse the Core
AST. There is no new execution relation, external SMT solver, or replacement
implementation of `vcgen`.

A future native backend supplies another `Interpretation` to these same recipes.
It does not import Hoare states, transformers, or proof rules. That backend is
outside this increment.

## Supported fragment and checks

The fragment is structured, monomorphic, call-free Core with integer and Boolean
parameters, locals, assignments, havoc, assert/assume, scoped blocks, deterministic
or nondeterministic branches, and deterministic annotated loops.

Arithmetic includes addition, subtraction, multiplication, negation, division,
remainder, comparisons, Boolean operations, equality, and conditional expressions.
Division/remainder require a nonzero divisor when their values are needed.
Boolean binary operators use conservative strict definedness, matching Deep's
current evaluator; conditional expressions require only the selected branch.

Embedding rejects missing/mismatched variable/operator annotations, bad operand
types, unbound variables, duplicate parameters, snapshot collisions, writes to
input-only parameters or snapshots, and locals escaping their scopes. Lambda's
existing annotated type checker is reused once per complete expression, and its
successful result is proved to imply Core's declarative `HasTypeA` judgment.

Unsupported types/functions/quantifiers/maps, CFGs, calls, coverage checks, exits,
local type declarations and nondeterministic loop guards are rejected explicitly.
These are also outside Deep's statement/expression fragment, except that our
route additionally supports nondeterministic branches.

## Specs, assertions, and scopes

Ordinary and free requires are assumptions of body verification. Ordinary ensures
are obligations; free ensures are retained but not claimed as proved guarantees.
An undefined assumption/requires is conservatively ignored, following Deep's
`MayHold`; it cannot eliminate a path merely because evaluation is undefined.
An assertion/ordinary ensures requires a defined, true expression.

Output-only parameters receive arbitrary typed values before the body. Inout
parameters receive read-only `old` snapshots. Input-only parameters are read-only.
Requires see inputs; the body/postconditions also see outputs and snapshots.
Blocks restore local slots on exit. This follows Core's scoping convention;
Deep's current Exec instead leaves locals in its state after a block.

Assertions generate their condition at their position in the program, plus the
continuation requirement. Tests prove that `assert false` is rejected even before
an infinite loop or a later `assume false`. Reversing the assertion/assumption order
correctly discards the impossible path.

## Loops

The shared embedding reuses Core's `Block.modifiedOrDefinedVars` analysis to pass
a conservative write set to the interpretation, including nested/local writes.
At an arbitrary loop head, only those names receive arbitrary values; every other
name keeps its loop-entry value. Facts established before the loop therefore
remain usable without being repeated in invariants.

Generated obligations are:

1. Invariants are defined and true on entry; an optional measure is defined and nonnegative.
2. At every framed head satisfying those checks, the guard is defined.
3. If the guard is true, the body passes its checks and re-establishes the invariants
   and measure bound; the optional measure strictly decreases.
4. If the guard is false, the requested continuation/postcondition holds.

Nested loops, body-local declarations, old snapshots, multiple invariants, and
loops without measures are exercised by proved Core examples. Negative tests
refute a false entry invariant, a body breaking a valid entry invariant, an
assertion inside a nonterminating loop, a negative measure, and a non-decreasing measure.

These are invariant-based sufficient VCs, not exact semantic weakest preconditions.
The loop-frame equations and a one-step unrolling theorem are proved in Soundness.
The unrolling theorem explicitly requires the body's framing property; the universal
connection of generated bodies and loops to original Core remains pending.

The guarantee remains partial correctness, as in Deep. A supplied measure generates
checks; a general source termination theorem is not claimed. Original Core runtime
loop rules ignore these annotations: do not confuse the extra verification
obligations with operational assertion-failure events.

## Proof status and remaining work

Proved: every registered `vcgen` rule about the transformer model; successful
expression embedding implies original annotated AST typing; CFGs cannot embed;
the exact formula certified by `Verified`; assertion-ordering facts; loop framing
and conditional unrolling facts; positive and negative program certificates.

Theorems with proof placeholders in `Hoare/Guarantees/Soundness.lean`:

- `verified_implies_core_correct`: the overall soundness theorem for original Core execution.
- `embedded_expression_denotes_core_value`: native expression values agree with Core denotation.
- `interpreted_statements_preserve_core_assertions_and_postcondition`: interpreted
  requirements imply Core-prefix assertion validity and the requested normal-result condition.
- `core_block_preserves_unwritten_variables`: Core executions preserve variables outside
  the selected write set.
- `output_initialization_covers_core_entry_states`: setup covers permitted outputs and snapshots.
- `core_requires_imply_interpreted_precondition`: Core requires imply interpreted assumptions.
- `interpreted_postcondition_implies_core_ensures`: interpreted ensures imply Core guarantees.

The separate `Hoare/Guarantees/EntryAdmission.lean` contains
`satisfying_inputs_admit_core_entry_state`: defined, satisfying native inputs admit
Core entry states. It does not assume `Verified` and is not the source soundness
implication. The dependency already supplies `Core.factoryInterp_nonempty` for
existence of a consistent model; no duplicate theorem or model is introduced here.

The overall theorem quantifies over all Core models and all admitted initial states,
checks every finite execution prefix, and appends ordinary ensures at normal
completion. It explicitly fixes the Core factory and concrete entry parameters.
No arbitrary semantic-compatibility or interpreter-soundness assumption is hidden
in its statement.

Deep currently proves its rules against its separate `Exec`; it does not provide
the original-Core bridge either. Our implementation covers its supported runtime
constructs and arithmetic, but the above source proof work is still necessary.
Completeness/exact WP, termination, a certified source-text-to-AST frontend, and a
native execution backend are separate claims.

There is also a dependency-level trust issue to resolve before claiming a
kernel-only soundness result: the current Core factory definition uses
`native_decide`, and its generated axiom appears among the dependencies of
`verified_implies_core_correct`. The limited allowance for admitted source theorems
does not establish that their eventual proofs will meet the strict axiom policy.
The final Core theorem must pass that policy after its proof is completed.

## Check

```sh
python3 StrataBoole/Tagless/check.py
```

The checker uses the pinned toolchain and installed dependencies. It builds missing
semantic modules in the ignored `Tagless/.build` overlay; it does not update
packages, modify dependency sources, or run repository-management commands.
Override the dependency checkout with `STRATA_BOOLE_REPO` if necessary.

`StrataBooleTest/tagless.lean` imports the audit and examples for the normal project
test target. The audit allows only Lean's standard `propext`, `Classical.choice`,
and `Quot.sound` axioms for completed theorems. The eight explicitly listed
source-facing theorems may additionally use only `sorryAx` and that single named
inherited factory axiom while their proofs still contain `sorry`; once completed
they receive the full audit automatically. Even pending theorems reject other
unexpected axioms. Verifier rules, program certificates, and all other theorems
remain subject to the full audit, which rejects `sorryAx` and additional axioms.
The frontend is reused unchanged
in this increment: theorems concern the reflected Core AST, not a certified parse of the source text.
