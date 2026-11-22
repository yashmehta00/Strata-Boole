# Boole semantics

## Motivation

Boole programs have traditionally acquired their meaning through `toCoreProgram`
and Strata Core. A language with its own semantics can also serve as a
translation target. For example, a Verus-to-Boole translation can state what
behavior it preserves using a definition of Boole itself.

This development defines the meaning of Boole directly in Lean. It follows the
compositional approach in Cornell's denotational semantics notes. Each syntactic
category has a mathematical domain, and the meaning of a compound phrase is
defined from the meanings of its immediate parts. An integer expression denotes
a state-dependent integer. A command denotes a relation on states and
completions. Lean's `Int`, functions and propositions express these mathematical
objects directly.

## A small example

```boole
program Boole;

procedure max2(x : int, y : int) returns (r : int)
spec {
  ensures [bounds]: r >= x && r >= y;
}
{
  if (x >= y) { r := x; } else { r := y; }
};
```

The parser supplies the Boole syntax tree. The interpretation resolves `x`,
`y` and `r` to their local slots and checks the type of each expression. The
guard becomes a function from a state to a Boolean result. The contract clause
becomes another Boolean expression, with its label `bounds` attached. The
procedure body composes the meanings of the guard and the two assignments.

For inputs `x = 3` and `y = 8`, the body relates the entry state to a normal
completion whose state has `r = 8`. Every typed initial value of `r` gives this
same final value. Evaluating the `bounds` clause on that final state yields
`true`. The clause remains available separately for specification checking.

## Types and expressions

[Types.lean](../Types.lean) assigns a carrier to each Boole type. An integer
denotes a Lean `Int`, a natural denotes a `Nat`, and a bitvector of width `w`
denotes a `BitVec w`. A map denotes a total function from its key carrier to
its value carrier. A sequence denotes a list and a set denotes a predicate.
The current model gives `real` the rational carrier `Rat`.

[Runtime.lean](../Runtime.lean) represents a state with a global store, a local
store, and snapshots of the globals listed in the procedure's `modifies`
clause. The stores can hold values of several types. Each slot pairs its type
with a value of that carrier. This pairing is needed at the store boundary.

[Expressions.lean](../Expressions.lean) defines the indexed expression domain
and the mathematical operations used to combine expression meanings.

```lean
abbrev Expr (t : ValueType) := State → Except RuntimeError t.denote
```

For example, the two children of integer addition produce native Lean
integers. The rule lifts Lean's integer addition over these two functions.
At a state where `x = 3`, evaluating `x + 2` reads the integer `3`, obtains
`2` from the literal, and returns `.ok 5`. This lifting also propagates a
missing or mismatched store entry.

[Interp.lean](../Interp.lean) contains `interpExpr`, which walks the expression
syntax, resolves variables and checks operand types before combining meanings.
For integer addition it constructs an `Expr .int` for each child and combines
them with `Expr.zip Int.add`. The latter defines how the two functions are
evaluated at a state and how their resulting integers are added. Source type
checks happen during construction; reading variable values and adding them
happen when the constructed function is applied to a state.

The intermediate `SomeExpr` pairs a discovered source type with its meaning.
It and its type-checking operation `expect` live beside the source traversal
in `Interp.lean`. The resulting integer expression returns a Lean `Int` and
propagates an error from either operand. Map update similarly calls
`Expr.mapSet` to construct the updated mathematical function.

Map lookup is function application, sequence append is list append, and an
expression conditional evaluates the selected arm. `old(e)` evaluates `e`
with the snapshots taking precedence over the current values of modified
globals. Local variables and read-only globals retain their current values.
The mathematical interpretation uses classical equality where a carrier
requires it, including equality of functions.

## Commands and procedures

[Interp.lean](../Interp.lean) declares the operations for combining
command meanings and defines the shared traversal over Boole syntax.
Expressions already have their typed denotations by the time the command
operations receive them. The traversal combines immediate meanings and uses
[Source.lean](../Source.lean) to resolve bindings and source types. A block
restores the lexical environment while the fold builds a meaning, and its
command meaning removes block-local slots at execution.

[Semantics.lean](Semantics.lean) supplies the mathematical command domain.

```lean
abbrev Result  := Completion × State
abbrev Command := Set (State × Result)
```

A completion records normal return, a named exit, assertion failure or a
runtime error. Membership `(initial, final) ∈ command` says that the command
admits this finite outcome from the initial state. The command equations are
written with named components, for example skip preserves the state.

```lean
def skip : Command :=
  { (initial, final) | final = (.normal, initial) }
```

Boole's nondeterministic commands can admit several outcomes from a given
initial state. The command rules compose these sets of pairs.

| Boole construct | Meaning at an initial state |
| --- | --- |
| `x := e` | Evaluate `e` and update the resolved slot with the result. |
| `c₁; c₂` | Find a normal intermediate state from `c₁` and run `c₂` from it, or propagate an early completion of `c₁`. |
| `havoc x` | Include the update for every value in the carrier of `x`. |
| `if *` | Include outcomes of either arm. A Boolean guard selects one arm. |
| `assume false` | Admit no outcomes from this state. |
| `assert false` | Admit an assertion-failure outcome carrying its label and state. |
| `exit label` | Carry the exit through sequencing and scopes until the corresponding labelled block consumes it. |

Loops use the union of finite unfoldings. Start with the empty
relation. Each next approximation tests the guard, stops if it is false, or
composes the body with the previous approximation if it is true. The loop
denotes the union of the approximations.

```text
unroll₀       = the empty relation
unrollₙ₊₁    = branch guard (body ; unrollₙ) skip
meaning(loop) = ⋃ₙ unrollₙ
```

This is the relational form of the least-fixed-point construction in the
Cornell notes. It accounts for every finite terminating execution, and also
for an early exit or assertion failure reached after finitely many iterations.
It models finite outcomes, so an infinite path contributes no result of its
own. The relation alone cannot distinguish an infinite path from a blocked path
when both contribute no finite outcomes.

At the procedure boundary, `Denotational.denoteProgram` builds the procedure
meanings and `Denotational.runs` relates an invocation to a finite outcome.
Invocation supplies typed globals and inputs in declaration order. Outputs
start with arbitrary values of their declared types. Requires and ensures
are retained as typed Boolean expressions with names and `free` attributes.
The body runner does not assume requires or check ensures automatically.
A `modifies` clause permits writes to the named globals and provides the
entry snapshots for `old`. Loop invariants and measures are checked for
supported syntax during construction (invariants must be Boolean).
They do not affect which outcomes the loop admits.

## Executing a meaning

[Computational/Native.lean](../Computational/Native.lean) supplies a second
command algebra to the same fold. It uses the same typed expression functions,
assignment updates, scope projection, and entry state. Its commands take a
configuration and state and compute a single result. A choice policy supplies
values for `havoc`, uninitialized slots and nondeterministic guards. A bound
limits recursive loop unfolding. Blocking, exhausted fuel and unavailable
choices are runner results distinct from assertion failure.

`Strata.Boole.nativeProgram` constructs the executable program and
`Native.run` runs a chosen procedure. The runner currently accepts primitive
carriers. The relational semantics can talk about all possible function and
map values, including choices and equalities a general executable runner
cannot compute.

## Scope and relationship to Core (IGNORE, this is changed)

The source interpretation covers structured procedure bodies, globals, local
declarations, assignments, assertions, assumptions, havoc, branching, loops,
and named exits. Expression coverage includes primitive operations, function
application, and selected map and sequence operations. Procedure calls,
polymorphic procedures, and unsupported operators are rejected during
construction. See [Examples.lean](../Examples.lean) for parsed examples and
checks of both interpretations.

Semantic agreement with Core compares the meaning of a Boole program with the
Core operational meaning of its lowering.

```text
Boole source ── denoteProgram ─────────────────► Boole meaning
     │                                                │
     └── toCoreProgram ──► Core program ── semantics ─┘
```

The [existing adequacy development](Adequacy/README.md) states and develops that
comparison for the previous representation, retained under
[Legacy](../Legacy). Those proofs have yet to be transferred to the typed
expression interface. The existing `toCoreProgram` pipeline remains available.

## References

- Cornell CS 4110, [Denotational Semantics](https://www.cs.cornell.edu/courses/cs4110/2020fa/lectures/lecture07.pdf).
State-dependent meanings, composition, and approximation for while loops.
- Cornell CS 4110, [Denotational Semantics Examples](https://www.cs.cornell.edu/courses/cs4110/2020fa/lectures/lecture08.pdf).
Ordering of meanings and least fixed points.
- Cornell CS 6110, [Powerdomains](https://www.cs.cornell.edu/courses/cs6110/2025sp/lectures/powerdomains.pdf).
Relational meanings for nondeterministic imperative programs and the choice
of what to observe about termination.
