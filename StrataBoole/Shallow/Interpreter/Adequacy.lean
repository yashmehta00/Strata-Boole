/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Shallow.Interpreter.Adequacy.Statements

/-!
# Interpreter adequacy (WIP)

## Goal

For supported Core procedures and corresponding initial values, prove that:

1. Every successful Core execution has a successful `interpProc` result with
   corresponding final values.
2. Every successful `interpProc` result has a successful Core execution with
   corresponding final values.
3. A source assertion failure is reachable if and only if `interpProc` permits
   the failure outcome `none`.

Here, success means normal completion with passing assumptions and assertions.
The result concerns final values and assertion failure, not termination of every
run, equality of intermediate traces, or execution cost.

## Proof structure

    Successful statement correspondence       Statement failure correspondence
                    |                                    |
                    v                                    v
    Successful procedure correspondence       Procedure failure iff
                    |                                    |
                    +-----------------+------------------+
                                      v
                                   adequacy

`Adequacy/Statements.lean` contains the two successful statement-execution goals
and their conjunction, `statement_success_correspondence`. They compare the
imported `Core.CoreStepStarE` relation with `interpStmts` on the same Core AST.
Both directional proofs contain `sorry`; their conjunction inherits those gaps.
The procedure and assertion-failure theorems are not yet declared.

The procedure proofs will use the statement lemmas and account for parameter
initialization, arbitrary outputs, `old` snapshots, and local-variable scope.
The current `interpProc` does not check preconditions or postconditions, so body
correspondence must be distinguished from full call/contract correspondence.
Failure correspondence is a separate argument: a failure may occur before later
nontermination or an impossible assumption.

## Input conditions and open questions

`CheckedStatementInput` collects the comparison's data and proposed hypotheses.
It uses existing Core typing and well-formedness judgments, with local contexts
and initialization policies existentially quantified. It contains no assumption
that statement executions correspond.

The contract is provisional; the current hypotheses have not been shown
sufficient for the two proofs. In particular:

* **Expressions.** `ChecksPass` requires Core's evaluator to return literal
  `true`, whereas the interpreter uses `LExpr.denote`. A quantified Boolean
  formula can have a denotation without reducing to a Boolean literal.
  Evaluator soundness alone does not supply the completeness needed for the
  reverse direction. Restrict the expression fragment with proved completeness
  facts, or justify a different source observation. Core's `DenoteBasedInterp`
  for trace conditions would not alone settle assignments and branch guards.
* **Value domains.** `SupportedStatements` checks statement forms, not expression
  or type support. Native havoc choices also need corresponding Core values;
  typing alone does not establish this for arbitrary Lean function/map values.
* **Factories.** The target fixes the execution factory to `Core.Factory`, and
  `typedEntry` requires the local typing factory to match. Program-defined
  functions need a corresponding extended factory and model. The proof should
  also establish which typing/initialization conditions are actually needed.
* **Failures.** Define source failure from the reference semantics, independently
  of the interpreter. Terminating traces alone cannot capture a failure followed
  by divergence. Since `none` also represents interpreter errors, those errors
  must be excluded before identifying `none` with source assertion failure.

## Trust dependencies

At the current pinned Strata revision, `#print axioms` for
`statement_success_correspondence` reports `propext`, `Classical.choice`,
`Quot.sound`, `sorryAx`, and a generated `native_decide` axiom under
`Core.WFFactory`. The last dependency comes from the imported built-in factory.

Completing the two proofs removes the admitted gaps. A strictly kernel-reduced
proof chain would also require addressing the upstream native proof. Recheck
these dependencies when updating Strata. This WIP module is kept outside the
production public import.

## Build

`lake build StrataBoole.Shallow.Interpreter.Adequacy` checks both adequacy files.
The two `sorry` warnings are expected. CI builds this target explicitly.
-/
