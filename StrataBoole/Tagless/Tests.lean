/- Low-level rejection tests deliberately construct invalid Core ASTs.
Readable, type-checked Core programs and proofs are in Hoare/Examples.lean. -/
import StrataBoole.Tagless.Embed

namespace Strata.Tagless.Tests

def intTy : Lambda.LMonoTy := .tcons "int" []
def boolTy : Lambda.LMonoTy := .tcons "bool" []
def ident (name : String) : Core.CoreIdent := ⟨name, ()⟩
def int (n : Int) : Core.Expression.Expr := .const () (.intConst n)
def bool (b : Bool) : Core.Expression.Expr := .const () (.boolConst b)
def read (name : String) (ty : Lambda.LMonoTy := intTy) : Core.Expression.Expr :=
  .fvar () (ident name) (some ty)
def binary (name : String) (x y : Core.Expression.Expr) : Core.Expression.Expr :=
  let arg := if name.startsWith "Bool." then boolTy else intTy
  let result := if ["Int.Add", "Int.Sub", "Int.Mul", "Int.Div", "Int.Mod"].contains name
    then intTy else boolTy
  .app () (.app () (.op () (ident name)
    (some (.tcons "arrow" [arg, .tcons "arrow" [arg, result]]))) x) y
def eq (x y : Core.Expression.Expr) : Core.Expression.Expr := .eq () x y
def set (name : String) (e : Core.Expression.Expr) : Core.Statement :=
  .set (ident name) e #[]
def check (e : Core.Expression.Expr) (attr : Imperative.CheckAttr := .Default) :
    Core.Procedure.Check := ⟨e, attr, #[]⟩

def increment : Core.Procedure := {
  header := {
    name := ident "increment", typeArgs := [],
    inputs := [(ident "n", intTy)], outputs := [(ident "r", intTy)]
  }
  spec := {
    preconditions := [("nonnegative", check (binary "Int.Ge" (read "n") (int 0)))],
    postconditions := [("positive", check (binary "Int.Gt" (read "r") (int 0)))]
  }
  body := .structured [set "r" (binary "Int.Add" (read "n") (int 1))]
}

def incrementInout : Core.Procedure := {
  header := {
    name := ident "incrementInout", typeArgs := [],
    inputs := [(ident "g", intTy)], outputs := [(ident "g", intTy)]
  }
  spec := {
    preconditions := [],
    postconditions := [("uses_old", check (eq (read "g")
      (binary "Int.Add" (read (Core.CoreIdent.mkOld "g").name) (int 1))))]
  }
  body := .structured [set "g" (binary "Int.Add" (read "g") (int 1))]
}

def withLocal : Core.Procedure := {
  increment with
  body := .structured [
    Core.Statement.init (ident "temp") (.forAll [] intTy)
      (.det (binary "Int.Add" (read "n") (int 1))) #[],
    set "r" (read "temp")]
}

-- The compiler must not turn unknown constructs into skip or True.
#guard !(embedCore { increment with
  body := .structured [set "r" (read "missing")] }).isOk

#guard !(embedCore { increment with
  body := .structured [set "r" (bool true)] }).isOk

#guard !(embedCore { increment with
  body := .structured [set "n" (int 4)] }).isOk

#guard !(embedCore { increment with
  body := .structured [set "r" (read "n" boolTy)] }).isOk

#guard !(embedCore { increment with
  body := .structured [set "r" (binary "Unknown.Op" (int 1) (int 2))] }).isOk

#guard !(embedCore { increment with
  body := .structured [Core.Statement.cover "coverage" (bool true) #[]] }).isOk

#guard !(embedCore { increment with
  body := .structured [Core.Statement.call "other" [] #[]] }).isOk

#guard !(embedCore { increment with
  body := .structured [.loop .nondet none [] [] #[]] }).isOk

-- A precondition cannot read an output-only parameter.
#guard !(embedCore { increment with
  spec := { increment.spec with preconditions := [("invalid_pre", check (eq (read "r") (int 0)))] }
}).isOk

-- Locals do not escape a nested block or enter the postcondition scope.
#guard !(embedCore { increment with
  body := .structured [
    .block "inner" [Core.Statement.init (ident "temp") (.forAll [] intTy) (.det (int 1)) #[]] #[],
    set "r" (read "temp")] }).isOk

#guard !(embedCore { withLocal with
  spec := { withLocal.spec with postconditions := [("invalid_post", check (eq (read "temp") (int 0)))] }
}).isOk

-- Old snapshots are available only inside/post, and cannot be assigned.
#guard !(embedCore { incrementInout with
  body := .structured [set (Core.CoreIdent.mkOld "g").name (int 7)] }).isOk

#guard !(embedCore { incrementInout with
  spec := { incrementInout.spec with preconditions := [
    ("invalid_old", check (eq (read (Core.CoreIdent.mkOld "g").name) (int 0)))] }
}).isOk

-- Original annotations must agree with the built-in signature.
#guard !(embedExpr [] (.app () (.op () (ident "Int.Neg") (some boolTy)) (int 1))).isOk
#guard !(embedExpr [] (.app () (.op () (ident "Int.Neg") none) (int 1))).isOk
#guard !(embedExpr [⟨"n", .int, false⟩] (.fvar () (ident "n") none)).isOk
#guard !(embedExpr [] (.app () (.app () (.op () (ident "Int.Add")
  (some (.tcons "arrow" [intTy, .tcons "arrow" [intTy, boolTy]]))) (int 1)) (int 2))).isOk

-- Partial arithmetic is supported; its definedness becomes a Hoare obligation.
#guard (embedExpr [] (binary "Int.Div" (int 1) (int 0))).isOk
#guard (embedExpr [] (binary "Int.Mod" (int 5) (int 2))).isOk

-- Header ambiguity is rejected, rather than resolved using list order.
#guard !(embedCore { increment with header := { increment.header with
  inputs := [(ident "n", intTy), (ident "n", intTy)] } }).isOk
#guard !(embedCore { incrementInout with header := { incrementInout.header with
  outputs := [(ident "g", boolTy)] } }).isOk
#guard !(embedCore { incrementInout with header := { incrementInout.header with
  inputs := [(ident "g", intTy), (ident "old g", intTy)] } }).isOk

-- Guard/invariant/measure contexts do not include body-local declarations.
#guard !(embedCore { increment with body := .structured [
  .loop (.det (bool true)) none [("bad", eq (read "temp") (int 0))]
    [Core.Statement.init (ident "temp") (.forAll [] intTy) (.det (int 0)) #[]] #[]] }).isOk
#guard !(embedCore { increment with body := .structured [
  .loop (.det (bool true)) (some (bool true)) [] [] #[]] }).isOk

-- Core's write-set analysis is reused, including writes nested in a branch.
#guard ((Imperative.Block.modifiedOrDefinedVars
  [set "r" (int 0), .ite (.det (bool true)) [set "r" (int 1)] [] #[]] false).map
    (fun x : Core.CoreIdent => x.name)) = ["r", "r"]

end Strata.Tagless.Tests
