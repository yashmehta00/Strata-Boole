/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Hoare.Certificate
public import StrataBoole.Boole.Semantics.Semantics

/-! Soundness of the transformer against Boole’s own denotational semantics. -/

public section
namespace Strata.Boole.Hoare

open StrataDDM

/-- The ordinary source postconditions at a returned state. -/
abbrev OrdinaryEnsures (proc : ProcedureMeaning) (state : State) : Prop :=
  ∀ clause ∈ proc.contract.ensures, clause.free = false → clause.holds state

/-- A source contract governs all finite outcomes from well-typed entries
satisfying the requires. Every ordinary ensures must hold on return. -/
@[expose] def DenotationalContract (meaning : ProgramMeaning) (name : String) : Prop :=
  ∃ procedure, meaning.findProcedure name = some procedure ∧
    ∀ (globals arguments outputs : List Value),
      valuesMatch meaning.globals globals = true →
      valuesMatch procedure.inputs arguments = true →
      valuesMatch procedure.outputs outputs = true →
      let entry := initialState meaning.globals procedure ⟨name, globals, arguments⟩ outputs
      procedure.requiresHold entry →
      ∀ outcome, procedure.body.run entry outcome →
        match outcome with
        | .returned () final => OrdinaryEnsures procedure final
        | .exited .. | .assertionFailed .. | .stuck .. => False

/-- Successful verification must also establish that the source has a denotation
in the admitted fragment. -/
def BooleSoundness : Prop :=
  ∀ source names name, Verified source names name →
    ∃ meaning, denoteProgram source names = .ok meaning ∧ DenotationalContract meaning name

/-- Soundness for a procedure whose source denotation has been constructed. -/
theorem denotationalContract_of_verified
    {source : Boole.Program} {names : GlobalContext} {name : String} {meaning : ProgramMeaning}
    (verified : Verified source names name)
    (denoted : denoteProgram source names = .ok meaning) :
    DenotationalContract meaning name := by
  sorry

end Strata.Boole.Hoare
