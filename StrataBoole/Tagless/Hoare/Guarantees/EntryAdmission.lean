/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.Tagless.Hoare.Guarantees.CoreState

/-! # Native inputs admit Core procedure-entry environments

This guarantee rules out accidental loss of satisfying inputs through Core's
entry gate. It is independent of verification soundness and does not assume
`Verified p`. It also does not claim that an arbitrary contract is satisfiable.

Existence of a consistent factory model is a distinct, existing upstream result:
`Core.factoryInterp_nonempty`, in
`Strata.Languages.Core.Logic.FactoryInterp`. Reuse that theorem rather than
introducing a duplicate model or an additional model-consistency axiom here.
-/

namespace Strata.Tagless.Hoare

/-- For a successfully embedded procedure, every native input state whose
requires clauses are defined and satisfied has a corresponding admissible Core
entry environment. That environment represents the same inputs in every Core
model and valuation, so the entry conditions do not exclude such inputs. -/
theorem satisfying_inputs_admit_core_entry_state
    (p : Core.Procedure) (recipes : PredRecipe × CmdRecipe × PredRecipe)
    (header : HeaderContext)
    (hembed : embedCore p = .ok recipes)
    (hheader : embedHeader p.header = .ok header)
    (inputs : State)
    (hrequires : (interpret recipes).1 inputs)
    (hdefined : ∀ label check, (label, check) ∈ p.spec.preconditions.toList →
      ∃ expression, embedBool header.before check.expr = .ok expression ∧
        (expression interpretation).defined inputs) :
    ∃ initial, initial.factory = Core.Factory ∧
      Core.Specification.ProcEnvWF entryParams p initial ∧
      ∀ (model : Lambda.Interp Core.Factory) (world : Core.Logic.DenoteValuation model),
        StoreDenotes model world header.before initial.store inputs := by
  sorry

end Strata.Tagless.Hoare
