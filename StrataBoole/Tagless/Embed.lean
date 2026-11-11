/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataBoole.Tagless.Interface
import all Strata.Languages.Core.Identifiers

/-! # Core AST → interpretation-independent recipes

All source matching and supported-fragment checks happen here. This module does
not import the Hoare interpretation. In particular no expression evaluator or
source AST traversal is left inside an expression recipe.
-/

@[expose] public section

namespace Strata.Tagless

/-- An exported equation allows clients to normalize snapshots without importing
Core's private implementation bodies or trusting native evaluation. -/
@[simp] theorem oldName_eq (name : String) :
    (Core.CoreIdent.mkOld name).name = "old " ++ name := rfl

/-- Recipes quantify over types and therefore live in Type 1. Lift ordinary
validation results when binding them inside a recipe-producing Except computation. -/
def liftCheck {α : Type} (result : Except String α) :
    Except String (ULift.{1} α) := result.map ULift.up

/-- Static information used while embedding, not a runtime store entry.
Procedure parameters start read-only; outputs and declared locals become writable. -/
structure Binding where
  name : String
  ty : Ty
  writable : Bool := false

def findBinding (context : List Binding) (name : String) : Except String Binding :=
  match context.find? (fun b => b.name == name) with
  | some b => .ok b
  | none => .error s!"unbound variable: {name}"

def embedTy : Lambda.LMonoTy → Except String Ty
  | .tcons "int" [] => .ok .int
  | .tcons "bool" [] => .ok .bool
  | _ => .error "only int and bool are supported in the initial tagless fragment"

def embedDeclaredTy (ty : Core.Expression.Ty) : Except String Ty :=
  match ty with
  | .forAll [] mono => embedTy mono
  | _ => .error "polymorphic local declarations are not supported"

def expect (wanted : Ty) (found : (ty : Ty) × ExprRecipe ty) :
    Except String (ExprRecipe wanted) :=
  if h : found.1 = wanted then .ok (h ▸ found.2)
  else .error "expression type mismatch"

/-- Check a supplied operator annotation against its built-in signature.
Annotations are required: Core denotation needs the original AST to be typed,
not merely a typed interpretation of an unannotated AST. -/
def checkOperatorAnnotation (annotation : Option Lambda.LMonoTy)
    (arguments : List Ty) (result : Ty) : Except String Unit := do
  let expected := arguments.foldr (fun arg rest => .tcons "arrow" [arg.core, rest]) result.core
  match annotation with
  | none => throw "operator annotation is missing; use the type-checked Core AST"
  | some actual =>
    unless actual = expected do throw "operator annotation disagrees with its built-in signature"

/-- Infer and embed a Core expression. Reads are resolved against the live context,
not merely trusted because a source type annotation is present. -/
def embedExprRaw (context : List Binding) : Core.Expression.Expr →
    Except String ((ty : Ty) × ExprRecipe ty)
  | .const _ (.intConst n) => pure ⟨.int, fun I => I.intLiteral n⟩
  | .const _ (.boolConst b) => pure ⟨.bool, fun I => I.boolLiteral b⟩
  | .fvar _ x annotation => do
    let ⟨binding⟩ ← liftCheck (findBinding context x.name)
    let ⟨ty⟩ ← liftCheck (match annotation with
      | some ty => .ok ty
      | none => .error "variable annotation is missing; use the type-checked Core AST")
    let ⟨annotated⟩ ← liftCheck (embedTy ty)
    unless annotated = binding.ty do throw "variable annotation disagrees with its declaration"
    pure ⟨binding.ty, fun I => I.read binding.ty x.name⟩
  | .app _ (.app _ (.op _ op annotation) left) right => do
    let binary (arg result : Ty)
        (operation : (I : Interpretation) → I.Expr arg → I.Expr arg → I.Expr result) := do
      let _ ← liftCheck (checkOperatorAnnotation annotation [arg, arg] result)
      let left ← embedExprRaw context left >>= expect arg
      let right ← embedExprRaw context right >>= expect arg
      pure ⟨result, fun I => operation I (left I) (right I)⟩
    match op.name with
    | "Int.Add" => binary .int .int (fun I => I.add)
    | "Int.Sub" => binary .int .int (fun I => I.sub)
    | "Int.Mul" => binary .int .int (fun I => I.mul)
    | "Int.Div" => binary .int .int (fun I => I.div)
    | "Int.Mod" => binary .int .int (fun I => I.mod)
    | "Int.Lt" => binary .int .bool (fun I => I.lt)
    | "Int.Le" => binary .int .bool (fun I => I.le)
    | "Int.Gt" => binary .int .bool (fun I => I.gt)
    | "Int.Ge" => binary .int .bool (fun I => I.ge)
    | "Bool.And" => binary .bool .bool (fun I => I.and)
    | "Bool.Or" => binary .bool .bool (fun I => I.or)
    | "Bool.Implies" => binary .bool .bool (fun I => I.implies)
    | "Bool.Equiv" => binary .bool .bool (fun I => I.equiv)
    | name => throw s!"unsupported binary operation: {name}"
  | .app _ (.op _ op annotation) arg => do
    match op.name with
    | "Int.Neg" =>
      let _ ← liftCheck (checkOperatorAnnotation annotation [.int] .int)
      let arg ← embedExprRaw context arg >>= expect .int
      pure ⟨.int, fun I => I.neg (arg I)⟩
    | "Bool.Not" =>
      let _ ← liftCheck (checkOperatorAnnotation annotation [.bool] .bool)
      let arg ← embedExprRaw context arg >>= expect .bool
      pure ⟨.bool, fun I => I.not (arg I)⟩
    | name => throw s!"unsupported unary operation: {name}"
  | .eq _ left right => do
    let ⟨ty, left⟩ ← embedExprRaw context left
    let right ← embedExprRaw context right >>= expect ty
    pure ⟨.bool, fun I => I.eq ty (left I) (right I)⟩
  | .ite _ cond left right => do
    let cond ← embedExprRaw context cond >>= expect .bool
    let ⟨ty, left⟩ ← embedExprRaw context left
    let right ← embedExprRaw context right >>= expect ty
    pure ⟨ty, fun I => I.ite (cond I) (left I) (right I)⟩
  | _ => throw "unsupported expression (functions, quantifiers, maps, or another value type)"

/-- Reuse Lambda's annotated type checker once per complete expression. The raw
worker handles recursion, so this does not repeatedly type-check every subtree. -/
def embedExpr (context : List Binding) (e : Core.Expression.Expr) :
    Except String ((ty : Ty) × ExprRecipe ty) := do
  let result ← embedExprRaw context e
  unless Lambda.LExpr.typeCheck [] e = some result.1.core do
    throw "source expression is not well typed at its inferred Core type"
  pure result

def embedBool (context : List Binding) (e : Core.Expression.Expr) :
    Except String (ExprRecipe .bool) :=
  embedExpr context e >>= expect .bool

def writableBinding (context : List Binding) (name : String) : Except String Binding := do
  let b ← findBinding context name
  unless b.writable do throw s!"assignment to a read-only input or snapshot: {name}"
  pure b

mutual
  /-- A statement returns the live context as well as its recipe, so a following
  statement may read a newly declared local. Nested blocks discard that extension. -/
  def embedStmt (context : List Binding) : Core.Statement →
      Except String (CmdRecipe × List Binding)
    | .cmd (.cmd (.set x rhs _)) => do
      let ⟨b⟩ ← liftCheck (writableBinding context x.name)
      let command : CmdRecipe ← match rhs with
        | .nondet => pure (fun I => I.havoc b.ty x.name)
        | .det e => do
          let e ← embedExpr context e >>= expect b.ty
          pure (fun I => I.assign b.ty x.name (e I))
      pure (command, context)
    | .cmd (.cmd (.init x sourceTy rhs _)) => do
      if context.any (fun b => b.name == x.name) then
        throw s!"declaration is not fresh: {x.name}"
      let ⟨ty⟩ ← liftCheck (embedDeclaredTy sourceTy)
      let command : CmdRecipe ← match rhs with
        | .nondet => pure (fun I => I.havoc ty x.name)
        | .det e => do
          let e ← embedExpr context e >>= expect ty
          pure (fun I => I.assign ty x.name (e I))
      pure (command, context ++ [⟨x.name, ty, true⟩])
    | .cmd (.cmd (.assert label e md)) => do
      let e ← embedBool context e
      pure ((fun I => I.assert ⟨label, .Default, md⟩ (e I)), context)
    | .cmd (.cmd (.assume label e md)) => do
      let e ← embedBool context e
      pure ((fun I => I.assume ⟨label, .Default, md⟩ (e I)), context)
    | .cmd (.cmd (.cover ..)) => throw "coverage checks are not supported"
    | .cmd (.call ..) => throw "procedure calls are not supported"
    | .block _ ss _ => do
      let body ← embedBlock context ss
      pure (body, context)
    | .ite condition yes no _ => do
      let yes ← embedBlock context yes
      let no ← embedBlock context no
      let body : CmdRecipe ← match condition with
        | .nondet => pure (fun I => I.choice (yes I) (no I))
        | .det e => do
          let e ← embedBool context e
          pure (fun I => I.branch (e I) (yes I) (no I))
      pure (body, context)
    | .loop (.det guard) measure invariants ss _ => do
      let guard ← embedBool context guard
      let measure : Option (ExprRecipe .int) ← match measure with
        | none => pure none
        | some e => do pure (some (← embedExpr context e >>= expect .int))
      let invariants : List (ClauseInfo × ExprRecipe .bool) ← invariants.mapM fun (label, e) => do
        pure (⟨label, .Default, #[]⟩, ← embedBool context e)
      let body ← embedBlock context ss
      -- Reuse Core's write-set analysis. Include local definitions conservatively.
      let writes := (Imperative.Block.modifiedOrDefinedVars ss false).map (·.name)
      pure ((fun I => I.loop writes (guard I)
        (invariants.map fun (info, e) => (info, e I))
        (measure.map fun e => e I) (body I)), context)
    | .loop .nondet .. => throw "nondeterministic loop guards are not supported"
    | .exit .. => throw "early/labelled exits are not supported"
    | .typeDecl .. => throw "local type declarations are not supported"
    termination_by s => (sizeOf s, 0)

  def embedStmts (context : List Binding) : List Core.Statement →
      Except String (CmdRecipe × List Binding)
    | [] => pure ((fun I => I.skip), context)
    | s :: ss => do
      let (first, afterFirst) ← embedStmt context s
      let (rest, afterRest) ← embedStmts afterFirst ss
      pure ((fun I => I.seq (first I) (rest I)), afterRest)
    termination_by ss => (sizeOf ss, 0)

  def embedBlock (context : List Binding) (ss : List Core.Statement) : Except String CmdRecipe := do
    let (body, afterBody) ← embedStmts context ss
    let locals := (afterBody.drop context.length).map (·.name)
    pure (fun I => I.block locals (body I))
    termination_by (sizeOf ss, 1)
end

def parameters (signature : @Lambda.LMonoTySignature Unit) : Except String (List Binding) :=
  (show List _ from signature).mapM fun (id, ty) => do pure ⟨id.name, ← embedTy ty, false⟩

/-- Header validation and static contexts, shared by both routes. -/
structure HeaderContext where
  outputOnly : List Binding
  inout : List Binding
  before : List Binding
  inside : List Binding

def embedHeader (header : Core.Procedure.Header) : Except String HeaderContext := do
  unless header.typeArgs.isEmpty do throw "polymorphic procedures are not supported"
  let inputs ← parameters header.inputs
  let outputs ← parameters header.outputs
  unless (inputs.map (·.name)).eraseDups.length = inputs.length do
    throw "duplicate input parameter"
  unless (outputs.map (·.name)).eraseDups.length = outputs.length do
    throw "duplicate output parameter"
  if outputs.any (fun output => (inputs.find? (fun p => p.name == output.name)).any
      (fun input => input.ty != output.ty)) then
    throw "inout parameter types disagree"
  let outputOnly := outputs.filter fun p => !(inputs.any fun i => i.name == p.name)
  let inout := inputs.filter fun p => outputs.any fun o => o.name == p.name
  let params := inputs ++ outputOnly
  let names := params.map (·.name)
  if inout.any (fun p => names.contains (Core.CoreIdent.mkOld p.name).name) then
    throw "old snapshot name collides with a parameter"
  let before := inputs
  let inside := params.map fun p => { p with writable := outputs.any fun o => o.name == p.name }
  let snapshots := inout.map fun p =>
    Binding.mk (Core.CoreIdent.mkOld p.name).name p.ty false
  pure ⟨outputOnly, inout, before, inside ++ snapshots⟩

def outputInitialization (header : HeaderContext) : CmdRecipe := fun I =>
  let snapshots := header.inout.foldr (fun p rest =>
    I.seq (I.assign p.ty (Core.CoreIdent.mkOld p.name).name
      (I.read p.ty p.name)) rest) I.skip
  header.outputOnly.foldr (fun p rest => I.seq (I.havoc p.ty p.name) rest) snapshots

/-- Shared worker for an already-checked procedure header. Both entry points
below use it, so setup and body embedding have one implementation. -/
def embedProcWithHeader (header : HeaderContext) : Core.Procedure.Body →
    Except String CmdRecipe
  | .structured statements => do
    let body ← embedBlock header.inside statements
    let setup := outputInitialization header
    pure (fun I => I.seq (setup I) (body I))
  | .cfg _ => .error "CFG bodies are not supported"

def embedProc (p : Core.Procedure) : Except String CmdRecipe := do
  let ⟨header⟩ ← liftCheck (embedHeader p.header)
  embedProcWithHeader header p.body

def embedClauses (context : List Binding)
    (clauses : List (String × Core.Procedure.Check)) (isPost : Bool) :
    Except String PredRecipe := do
  let clauses : List (ClauseInfo × ExprRecipe .bool) ← clauses.mapM fun (label, check) => do
    let e ← embedBool context check.expr
    pure (ClauseInfo.mk label check.attr check.md, e)
  pure (fun I => clauses.foldr (fun (info, e) rest =>
    I.andPred
      (if isPost then I.ensuresClause info (e I)
       else I.requiresClause info (e I)) rest) I.truePred)

def embedRequires (context : List Binding)
    (clauses : List (String × Core.Procedure.Check)) : Except String PredRecipe :=
  embedClauses context clauses false

def embedEnsures (context : List Binding)
    (clauses : List (String × Core.Procedure.Check)) : Except String PredRecipe :=
  embedClauses context clauses true

/-- Exactly three interpretation-independent results: requires, whole procedure,
and ensures. Preconditions may read only inputs; postconditions may also
read outputs and the read-only old snapshots. No obligation is proved here. -/
def embedCore (p : Core.Procedure) :
    Except String (PredRecipe × CmdRecipe × PredRecipe) := do
  let ⟨header⟩ ← liftCheck (embedHeader p.header)
  let pre ← embedRequires header.before p.spec.preconditions
  let program ← embedProcWithHeader header p.body
  let post ← embedEnsures header.inside p.spec.postconditions
  pure (pre, program, post)

/-- Specialize a concrete embedding using checked defining equations.
Unfold the source program's definitions before invoking this tactic. -/
macro "tagless_embed" : tactic => `(tactic|
  simp [embedCore, embedProc, embedProcWithHeader, embedHeader, embedRequires, embedEnsures, embedClauses,
    parameters, outputInitialization, embedBlock, embedStmts, embedStmt, embedBool,
    embedExpr, embedExprRaw, Lambda.LExpr.typeCheck, Lambda.LConst.ty, Lambda.LMonoTy.bool, Lambda.LMonoTy.int, Lambda.LMonoTy.arrow, Lambda.LMonoTy.isArrow, Option.bind, guard, checkOperatorAnnotation, Ty.core, expect, findBinding, writableBinding, embedTy, embedDeclaredTy,
    liftCheck, Except.isOk, Except.toBool,
    bind, pure, Except.bind, Except.pure, Except.map,
    Imperative.Block.modifiedOrDefinedVars, Imperative.Block.modifiedVars,
    Imperative.Block.definedVars, Imperative.Stmt.modifiedVars, Imperative.Stmt.definedVars,
    Core.Command.modifiedVars, Core.Command.definedVars, Imperative.Cmd.modifiedVars,
    Imperative.Cmd.definedVars, Imperative.HasVarsImp.modifiedVars, Imperative.HasVarsImp.definedVars,
    List.mapM, List.mapM.loop, List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop, List.find?])

end Strata.Tagless
