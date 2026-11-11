/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Languages.Core.Procedure

/-! # Shared interface for Core recipes

This file has no Hoare, WP, or native-interpreter dependency. A recipe is a
function accepting an interpretation, not another statement AST. The initial
fragment has integer and Boolean values. Extending it starts here.
-/

@[expose] public section

namespace Strata.Tagless

inductive Ty where
  | int | bool
  deriving DecidableEq

abbrev Ty.denote : Ty → Type
  | .int => Int
  | .bool => Bool

/-- The corresponding monomorphic Core type. -/
def Ty.core : Ty → Lambda.LMonoTy
  | .int => .tcons "int" []
  | .bool => .tcons "bool" []

/-- Source information survives embedding, including on free clauses. -/
structure ClauseInfo where
  label : String
  attr : Imperative.CheckAttr := .Default
  metadata : Imperative.MetaData Core.Expression := #[]

/-- The same interface is used by both routes. No field mentions a Hoare triple,
WP, source execution relation, or a native store representation. -/
structure Interpretation where
  Expr : Ty → Type
  Cmd : Type
  Pred : Type
  intLiteral : Int → Expr .int
  boolLiteral : Bool → Expr .bool
  read : (ty : Ty) → String → Expr ty
  neg : Expr .int → Expr .int
  not : Expr .bool → Expr .bool
  add : Expr .int → Expr .int → Expr .int
  sub : Expr .int → Expr .int → Expr .int
  mul : Expr .int → Expr .int → Expr .int
  div : Expr .int → Expr .int → Expr .int
  mod : Expr .int → Expr .int → Expr .int
  lt : Expr .int → Expr .int → Expr .bool
  le : Expr .int → Expr .int → Expr .bool
  gt : Expr .int → Expr .int → Expr .bool
  ge : Expr .int → Expr .int → Expr .bool
  and : Expr .bool → Expr .bool → Expr .bool
  or : Expr .bool → Expr .bool → Expr .bool
  implies : Expr .bool → Expr .bool → Expr .bool
  equiv : Expr .bool → Expr .bool → Expr .bool
  eq : (ty : Ty) → Expr ty → Expr ty → Expr .bool
  ite : Expr .bool → Expr a → Expr a → Expr a
  skip : Cmd
  seq : Cmd → Cmd → Cmd
  assign : (ty : Ty) → String → Expr ty → Cmd
  havoc : (ty : Ty) → String → Cmd
  assert : ClauseInfo → Expr .bool → Cmd
  assume : ClauseInfo → Expr .bool → Cmd
  branch : Expr .bool → Cmd → Cmd → Cmd
  choice : Cmd → Cmd → Cmd
  /-- Execute the body with the listed names scoped to this block. -/
  block : List String → Cmd → Cmd
  loop : List String → Expr .bool → List (ClauseInfo × Expr .bool) → Option (Expr .int) → Cmd → Cmd
  truePred : Pred
  andPred : Pred → Pred → Pred
  requiresClause : ClauseInfo → Expr .bool → Pred
  ensuresClause : ClauseInfo → Expr .bool → Pred

abbrev ExprRecipe (ty : Ty) :=
  (I : Interpretation) → I.Expr ty

abbrev CmdRecipe := (I : Interpretation) → I.Cmd
abbrev PredRecipe := (I : Interpretation) → I.Pred

end Strata.Tagless
