# Boole adequacy

[`denotation_agrees_with_core`](Theorem.lean) compares two meanings of the same
Boole program. One comes from `denoteProgram`, which interprets Boole directly.
The other comes from running the result of `checkedCoreProgram` under Strata
Core’s operational semantics. The latter uses the existing `toCoreProgram`
lowering, the nat preamble when applicable, and Core’s type checker.

## What the theorem states

The source program must pass `inConcreteCoreFragment`, produce a Boole
denotation, and lower and type-check successfully in Core. For every
invocation accepted by the Boole interface, the theorem compares two
predicates on observations. Their equality means each observation is possible
on either side exactly when it is possible on the other.

- A normal return records the final values of globals in declaration order
  and the final values of explicit outputs in parameter order.
- An assertion failure records that a false assertion can be reached after a
  prefix in which all earlier assumptions and assertions pass. The program
  may diverge after that point.

The theorem also compares requires and ensures on well-typed interface states.
These predicates describe the declared contract. Contract validity and total
correctness are separate properties.

The fragment is a syntactic restriction on Boole constructs and types.
The proof represents the admitted scalars as Core semantic values under
Strata’s built-in model. A Core choice at a represented scalar sort can
be decoded to the exact Boole value. The
observation and interface definitions are in [CoreReference.lean](../CoreReference.lean).

## How the proof is organized

1. [Typing.lean](Typing.lean) finds each lowered procedure in the annotated
   program. It uses the declarative typing derivation and equality of the
   procedure syntax after erasing expression type annotations.
2. [DeclarativeEntry.lean](DeclarativeEntry.lean) establishes the correspondence
   between a Boole procedure interface and its Core header. Given this layout,
   [Entry.lean](Entry.lean) proves call-frame agreement, including initial
   output choices and the entry snapshots of modified globals.
3. [DeclarativeAdequacy.lean](DeclarativeAdequacy.lean) applies the
   [statement-list induction](Execution.lean) to the actual Boole body and
   the actual chunks emitted by lowering. Declarative typing determines
   the scopes at each chunk and ensures that all exit labels are in scope.
   The induction composes finite returns, exits, and failing assertion
   prefixes. The procedure proof then projects away body-local variables
   and lifts the result through Core’s outer blocks.
4. [Contracts.lean](Contracts.lean) pairs requires and ensures clauses by
   position and compares their truth on well-typed interface states.
   [Observations.lean](Observations.lean) assembles the entry, execution, and
   contract results into program adequacy.
5. [Theorem.lean](Theorem.lean) preserves the checker-facing statement.
   Its two checker lemmas supply declarative well-typedness and preservation
   of procedure syntax after erasing expression annotations. The semantic
   argument takes those facts directly.

## Proof status

The end-to-end composition typechecks with seven admitted lemmas.

### Boole proof obligations

Five lemmas remain to be proved in the Boole adequacy argument.

- `lowered_inputs_match_source` and `lowered_outputs_match_source` match
  the legacy lowerer’s generated formals to the interpreted Boole interface.
  Source-level distinctness and freshness of snapshot names are proved.
- `procedure_block_entry` relates the initial lexical scope and lowering
  state for the actual body. It must establish the execution invariant,
  including Core’s typed store and the alignment of saved in-out names.
- `procedure_nonexit_statement_execution` is the remaining semantic
  induction step. The direct exit case is proved. Other cases require
  supplying the expression and state premises of the existing command
  rules and completing replay for loop exits and failures.
- `declarative_clause_truth` relates an interpreted Boole clause to
  evaluation of the corresponding annotated Core expression. Clause
  counts and same-position annotation preservation are proved separately.

### Strata checker guarantees deferred to upstream

The declarative theorem takes these two facts as premises. We defer their
proofs to the Strata checker integration, so the Boole adequacy proof can use
the declarative typing specification.

- `checked_lowering_wellTyped` says a successful checker result satisfies
  Core's `ProgramWellTyped` judgment. Strata's checker soundness theorem is
  intended to supply this guarantee.
- `checked_lowering_preserves_procedureSyntax` says the checker preserves
  procedure headers, bodies, and contracts after expression annotations are
  erased. This requires a preservation guarantee connecting the checker
  input and output. Well-typedness of the result alone does not imply it.

Both guarantees remain admitted in the checker-facing wrapper in
[Theorem.lean](Theorem.lean).

```sh
lake build StrataBoole.Boole.Semantics.Adequacy.Theorem
```

`#print axioms Strata.Boole.denotation_agrees_with_core` reports
`sorryAx` while these obligations are open.
