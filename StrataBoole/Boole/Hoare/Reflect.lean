/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Lean.ToExpr
public import StrataDDM.Integration.Lean.ToExpr
public import StrataBoole.Boole.Hoare.Certificate
public meta import Lean
meta import Lean.Elab.Deriving.ToExpr
meta import Lean.Util.FoldConsts
public meta import StrataDDM.Util.SourceRange
public meta import StrataBoole.Boole
public meta import StrataDDM.Integration.Lean.ToExpr

/-! Quote the generated Boole AST at elaboration time. The generated DDM
decoder is partial, so its computation belongs at the syntax boundary.
The verification goal names the resulting Boole constructors. -/

public section
namespace Strata.Boole.Hoare

open Lean Elab Command StrataDDM

/-- Derive quotation for the generated AST in dependency order, using one
derivation for each mutually inductive group. -/
private meta partial def deriveQuoters (name : Name) : StateT NameSet CommandElabM Unit := do
  if (← get).contains name || !(`Strata.BooleDDM).isPrefixOf name then return
  let env ← getEnv
  let some (.inductInfo info) := env.find? name | return
  modify fun seen => info.all.foldl (·.insert ·) seen
  for ind in info.all do
    for ctor in (← getConstInfoInduct ind).ctors do
      for dependency in (← getConstInfoCtor ctor).type.getUsedConstants do
        deriveQuoters dependency
  let names := info.all.toArray.map mkIdent
  liftM (elabCommand (← `(deriving instance Lean.ToExpr for $names:ident,*)))

meta section
run_cmd (deriveQuoters ``Strata.BooleDDM.Program).run' {}
deriving instance ToExpr for GlobalKind
end

open Lean.Parser in
private meta def readAst (source : StrataDDM.Program) : Except String Boole.Program :=
  BooleDDM.Program.ofAst
    { ann := default, name := q`Boole.prog,
      args := #[.seq default .spacePrefix (source.commands.map ArgF.op)] }

/-- Use `boole% program` in a theorem over a concrete `#strata` program. -/
syntax (name := booleSource) "boole% " term:max : term

@[term_elab booleSource] meta unsafe def elabBooleSource : Term.TermElab := fun stx _ => do
  let source ← Term.elabTermEnsuringType stx[1] (mkConst ``StrataDDM.Program)
  Term.synthesizeSyntheticMVarsNoPostponing
  let source ← instantiateMVars source
  let program ← Meta.evalExpr StrataDDM.Program (mkConst ``StrataDDM.Program) source
  let ast ← match readAst program with
    | .ok ast => pure ast
    | .error msg => throwError "Boole AST decoding failed: {msg}"
  let context := program.globalContext
  let nameMap ← Meta.mkAppM ``Std.HashMap.ofList #[toExpr context.nameMap.toList]
  let names := mkApp2 (mkConst ``GlobalContext.mk) nameMap (toExpr context.vars)
  return mkApp2 (mkConst ``Source.mk) (toExpr ast) names

end Strata.Boole.Hoare
