# From the Boole transformer to Core’s Hoare triple

```lean
-- CoreCompatibility
∀ source names name checked params,
  checkedCoreProgram source names = .ok checked →
  CoreBridgeFragment source names checked name →
  Verified source names name →
  Core.Logic.Hoare.Procedure.contractTriple checked params name
```

A Lean proof of the Boole certificate establishes the contract of the checked
Core lowering of the same procedure. For each completed Core run, assertions
must hold when their preceding assumptions hold. If the whole run's
assumptions hold, the ordinary ensures must hold on return.

## Direct proof

[Core.lean](Core.lean) uses the certificate to obtain the procedure's
transformer condition at a typed Boole entry. The entry state and the Core
environment agree on the source values the procedure can read. Core can
also have bindings that the procedure ignores, including an output-only
slot whose initial value is irrelevant until the procedure writes it.

The proof follows the compiler and lowering for the selected procedure.
[Transfer.lean](Transfer.lean) gives the individual steps:

- Assignment and declaration use the successful Core store update to
  justify the continuation in the corresponding Boole state.
- Assertion turns a transformer obligation into truth of the Core check.
  Assumption restricts the continuation to executions where the check holds.
- Sequencing passes the continuation through the preceding command. A
  branch selects the transformer condition using the truth of the Core guard.
- The loop rule keeps the original Boole entry and its write frame in the
  Core invariant. A body triple preserves the invariant and the frame. The
  false guard supplies the final continuation. The transformer checks any
  supplied decreases annotation, and the Core result is partial correctness.

On return, the lifted continuation supplies the ordinary Boole ensures at
a state related to the actual final Core store. Evaluating the corresponding
checked Core clauses gives the final postcondition. This proof uses Core's
proved Hoare rules and the Boole transformer. The standalone guarantee in
[Soundness.lean](Soundness.lean) can be proved independently.

## What remains

`core_compatibility_of_wellTyped` consumes two facts from Strata about the
checked output. The annotated program satisfies `ProgramWellTyped`, and
erasing annotations recovers the raw procedure syntax. The typing adapter
selects the procedure's `ProcWellTyped` derivation and uses it to prove
`contractChecksTyped`. `core_compatibility` takes the checker-to-spec bridge
for the scalar fragment as a premise and concludes the original
`CoreCompatibility` proposition. The proof uses the declarative facts
without unfolding the Core typechecker.

The remaining admitted lemma is `compiled_contract_lowering`.
[`annotated_origin`](Origin.lean) already identifies the common Boole declaration
and recovers the raw procedure behind the selected annotated procedure. The proof needs three facts about
those outputs.

- **Interface.** `prepare_integer_globals` gives the prepared integer globals
  in declaration order. Match them and explicit formals, outputs, and
  `modifies` names to the Core header. [Entry.lean](Entry.lean) already
  constructs the canonical typed entry from a Core store once those header
  facts are available. The output-only check ensures that the first write
  establishes the representation before any read.
- **Expressions and clauses.** Use the declared sorts and matching readable
  slots to relate the compiled expression evaluator to the annotated Core
  expression. The existing [scalar laws](ScalarEval.lean) apply in the Core
  entry's own model. Pair ordinary ensures with ordinary ensures and use
  the same entry snapshots for `old` on return.
- **Body.** Instantiate the proved transfer rules by induction on the
  shared source body and its corresponding Core statements. Carry the
  compiler's lexical scope and the set of unwritten output slots. The loop
  step uses the existing write-frame lemmas to show that changes stay inside
  the compiler's frame. Scope exit preserves the enclosing bindings on both
  sides. The top-level proof already consumes the certificate and assembles
  the resulting Core triple.

Store correspondence alone allows missing or shadowed source bindings.
The procedure bridge therefore uses a canonical source entry and a well-formed
return with its saved values still present. The body induction must preserve
the corresponding lexical facts at intermediate points.
