/- Build and trust-boundary checks for the Hoare prototype. -/
import StrataBoole.Tagless.Tests
import StrataBoole.Tagless.Hoare.Examples
import StrataBoole.Tagless.Hoare.Regression
import StrataBoole.Tagless.Hoare.Guarantees.Soundness
import StrataBoole.Tagless.Hoare.Guarantees.EntryAdmission
import Lean.Util.CollectAxioms

-- Only the listed source-correspondence theorems may currently contain sorry.
-- All other theorems, including verifier rules and program certificates, must
-- remain independent of sorryAx and project-specific axioms. In particular,
-- using one of these placeholders in a certificate makes the audit fail.
open Lean Elab Command in
run_cmd do
  let namespaceRoot : Name := `Strata.Tagless
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  -- The one known inherited axiom in the current source theorem types. It is
  -- permitted only while a listed source proof is admitted, never in a finished
  -- theorem. Do not exempt admitted declarations from all dependency checks.
  let factoryNativeAxiom :=
    Name.num `_private.Strata.Languages.Core.Factory 0 ++
      `Core.WFFactory._native.native_decide.ax_1
  let pendingOnly : Array Name := #[``sorryAx, factoryNativeAxiom]
  let proofPlaceholders : Array Name := #[
    ``Strata.Tagless.Hoare.verified_implies_core_correct,
    ``Strata.Tagless.Hoare.embedded_expression_denotes_core_value,
    ``Strata.Tagless.Hoare.interpreted_statements_preserve_core_assertions_and_postcondition,
    ``Strata.Tagless.Hoare.core_block_preserves_unwritten_variables,
    ``Strata.Tagless.Hoare.output_initialization_covers_core_entry_states,
    ``Strata.Tagless.Hoare.satisfying_inputs_admit_core_entry_state,
    ``Strata.Tagless.Hoare.core_requires_imply_interpreted_precondition,
    ``Strata.Tagless.Hoare.interpreted_postcondition_implies_core_ensures
  ]
  for (name, info) in (← getEnv).constants.toList do
    if namespaceRoot.isPrefixOf name then
      if let .thmInfo _ := info then
        let assumptions ← collectAxioms name
        -- Completed source theorems receive exactly the same strict policy as
        -- certificates. Pending proofs may use only the two named exceptions.
        let isProofPlaceholder := proofPlaceholders.contains name && assumptions.contains ``sorryAx
        for assumptionName in assumptions do
          unless allowed.contains assumptionName ||
              (isProofPlaceholder && pendingOnly.contains assumptionName) do
            throwError "{name} depends on unapproved axiom {assumptionName}"
