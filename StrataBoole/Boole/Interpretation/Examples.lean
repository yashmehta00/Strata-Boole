/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean.HashCommands
meta import StrataBoole.Grammar
meta import StrataBoole.Boole
meta import StrataBoole.Boole.Interpretation.Types
meta import StrataBoole.Boole.Interpretation.Runtime
meta import StrataBoole.Boole.Interpretation.Interp
meta import StrataBoole.Boole.Interpretation.Computational.Native
import all StrataBoole.Boole.Interpretation.Computational.Native
import all StrataBoole.Boole.Interpretation.Types
import all StrataBoole.Boole.Interpretation.Runtime
import all StrataBoole.Boole.Interpretation.Source
meta import StrataBoole.Boole.Interpretation.Denotational.Semantics
meta import StrataBoole.Verify
import all StrataBoole.Verify
import all StrataBoole.Boole
import StrataBoole.Boole.Interpretation.Denotational.CoreReference
meta import StrataBoole.Boole.Interpretation.Denotational.CoreReference
import all StrataBoole.Boole.Interpretation.Denotational.Semantics
import all StrataBoole.Boole.Interpretation.Expressions
import all StrataBoole.Boole.Interpretation.Interp

/-! # Small Boole programs and semantic regression checks

Source examples exercise the real parser and shared traversal through the native
instance. Direct relational witnesses and type-carrier equalities exercise the
mathematical semantics, whose general function equality is noncomputable.
None of these examples uses the admitted adequacy theorem.
-/

namespace Strata.Boole.Examples

def max2 :=
#strata
program Boole;
procedure max2(x : int, y : int) returns (r : int)
spec {
  ensures [bounds]: r >= x && r >= y;
  ensures [chosen]: r == x || r == y;
}
{
  if (x >= y) { r := x; } else { r := y; }
};
#end

def incrementGlobal :=
#strata
program Boole;
var g : int;
procedure inc(x : int) returns ()
spec {
  modifies g;
  ensures [increased]: g == old(g) + x;
}
{
  g := g + x;
};
#end

def counting :=
#strata
program Boole;
procedure count(n : int) returns (r : int)
spec { requires n >= 0; ensures r == n; }
{
  r := 0;
  while (r < n)
    invariant 0 <= r
    invariant r <= n
  { r := r + 1; }
};
#end

def scopeAndExit :=
#strata
program Boole;
procedure scoped(x : int) returns (r : int)
{
  r := x;
  inner: {
    var temporary : int;
    temporary := x + 1;
    r := temporary;
    exit inner;
    assert false;
  }
  exit scoped;
  assert false;
};
#end

def nondeterminism :=
#strata
program Boole;
procedure pick() returns (r : int)
{
  havoc r;
  if * { assume r >= 0; } else { assume r < 0; }
  while * { exit pick; }
};
#end

def failureBeforeDivergence :=
#strata
program Boole;
procedure fail() returns ()
{
  assert [failure]: false;
  while (true) { }
};
#end

def missingModifies :=
#strata
program Boole;
var g : int;
procedure bad() returns () { g := 1; };
#end

def callOutsideFragment :=
#strata
program Boole;
procedure identity(x : int) returns (r : int) { r := x; };
procedure caller(x : int) returns (r : int) { call r := identity(x); };
#end

private def meaningOf (source : StrataDDM.Program) : Except String Native.Program := do
  let ast ← (getProgram source).mapError (fun message => toString (message.format none))
  (nativeProgram ast source.globalContext).mapError (fun error => error.message)

private def builds (source : StrataDDM.Program) : Bool := (meaningOf source).isOk

private def checks (source : StrataDDM.Program) : Bool :=
  match getProgram source with
  | .error _ => false
  | .ok ast => (checkedCoreProgram ast source.globalContext).isOk

private def postconditions (source : StrataDDM.Program) (name : String) (state : State) : Bool :=
  match meaningOf source with
  | .error _ => false
  | .ok meaning => match meaning.findProcedure name with
    | none => false
    | some procedure => procedure.contract.ensures.all fun clause =>
        match clause.condition state with | .ok true => true | _ => false

#guard builds max2
#guard checks max2
#guard builds incrementGlobal
#guard checks incrementGlobal
#guard builds counting
#guard checks counting
#guard builds scopeAndExit
#guard checks scopeAndExit
#guard builds nondeterminism
#guard checks nondeterminism
#guard builds failureBeforeDivergence
#guard checks failureBeforeDivergence
#guard !builds missingModifies
#guard !builds callOutsideFragment

-- Actual Boole contract expressions, denoted directly as native operations.
#guard postconditions max2 "max2"
  { locals := [("x", .int 3), ("y", .int 8), ("r", .int 8)] }
#guard !postconditions max2 "max2"
  { locals := [("x", .int 3), ("y", .int 8), ("r", .int 4)] }
#guard postconditions incrementGlobal "inc"
  { globals := [("g", .int 13)], locals := [("x", .int 3)], snapshots := [("g", .int 10)] }
#guard !postconditions incrementGlobal "inc"
  { globals := [("g", .int 13)], locals := [("x", .int 3)], snapshots := [("g", .int 9)] }

open Interpretation

-- Mathematical havoc ranges over the entire carrier.
example :
    ({ locals := [("x", .int 0)] }, (.normal, { locals := [("x", .int (-37))] })) ∈
      Denotational.Command.havoc (.local "x") .int :=
  ⟨-37, rfl⟩

-- False assumptions block; false assertions are finite outcomes.
example (outcome : Interpretation.Result) :
    ({}, outcome) ∉
      Denotational.Command.assumption (Interpretation.Expr.constant .bool false) := by
  intro h
  exact h

example :
    ({}, (.assertionFailure "failure", {})) ∈
      Denotational.Command.seq
        (Denotational.Command.assertion "failure" (Interpretation.Expr.constant .bool false))
        (Denotational.Command.loop (some (Interpretation.Expr.constant .bool true))
          Denotational.Command.skip) :=
  Or.inr ⟨(by intro h; cases h), rfl⟩

example :
    ({}, (.normal, {})) ∈
      Denotational.Command.loop (some (Interpretation.Expr.constant .bool false))
        (Denotational.Command.assertion "unreachable" (Interpretation.Expr.constant .bool false)) :=
  ⟨1, rfl⟩

-- The type interpretation is systematic and directly reduces to native carriers.
example : ValueType.denote (.map .int (.sequence .nat)) = (Int → List Nat) := by rfl
example : ValueType.denote (.arrow .string (.bitvec 32)) = (String → BitVec 32) := by rfl
example : ValueType.denote .regex = (String → Prop) := by rfl

-- A small executable check uses the SAME syntax traversal with the other backend.
private def nativeMax2 : Option Int := do
  let ast ← (getProgram max2).toOption
  let program ← (nativeProgram ast max2.globalContext).toOption
  let config : Native.Config := { choose := fun ty => match ty with
    | .int => some (.int 0) | .bool => some (.bool false) | _ => none }
  match Native.run program { procedure := "max2", arguments := [.int 3, .int 8], globals := [] } config with
  | .outcome (.normal, state) => match state.locals.lookup "r" with
    | some (.int value) => some value | _ => none
  | _ => none

#guard nativeMax2 = some 8

-- A native loop reaches the same result after several guard evaluations.
private def nativeCount : Option Int := do
  let ast ← (getProgram counting).toOption
  let program ← (nativeProgram ast counting.globalContext).toOption
  let config : Native.Config := { choose := fun _ => some (.int 0) }
  match Native.run program { procedure := "count", arguments := [.int 3], globals := [] } config with
  | .outcome (.normal, state) =>
    match state.locals.lookup "r" with | some (.int n) => some n | _ => none
  | _ => none

#guard nativeCount = some 3

-- A failing assertion remains a semantic failure, not a runner timeout.
private def nativeFailure : Bool :=
  match getProgram failureBeforeDivergence with
  | .error _ => false
  | .ok ast => match nativeProgram ast failureBeforeDivergence.globalContext with
    | .error _ => false
    | .ok program => match Native.run program { procedure := "fail", globals := [], arguments := [] } {} with
      | .outcome (.assertionFailure _, _) => true
      | _ => false

#guard nativeFailure

-- The operator receives and returns native values at its fixed carrier.
example : Interpretation.Expr.zip (a := .int) (b := .int) (c := .int) Int.add
    (Interpretation.Expr.constant .int 2) (Interpretation.Expr.constant .int 2)
    {} = .ok 4 := rfl

def add8 :=
#strata
program Boole;
procedure add8(a : bv W8, b : bv W8) returns (r : bv W8)
{ r := a + b; };
#end

#guard builds add8 && checks add8

private def nativeAdd8 : Option Nat := do
  let ast ← (getProgram add8).toOption
  let program ← (nativeProgram ast add8.globalContext).toOption
  let config : Native.Config := { choose := fun ty => match ty with
    | .bitvec width => some (.bitvec width 0) | _ => none }
  match Native.run program
      { procedure := "add8", globals := [], arguments := [.bitvec 8 250, .bitvec 8 10] } config with
  | .outcome (.normal, state) => match state.locals.lookup "r" with
    | some (.bitvec _ value) => some value.toNat | _ => none
  | _ => none

#guard nativeAdd8 = some 4

-- Nat has a native mathematical carrier, but is deliberately outside the
-- primitive-literal Core agreement theorem until its datatype bridge is proved.
def natAddition :=
#strata
program Boole;
procedure natAddition() returns (r : int)
{ r := nat_toInt(nat_add(nat_fromInt(2), nat_fromInt(3))); };
#end

#guard builds natAddition && checks natAddition

private def concrete (source : StrataDDM.Program) : Bool :=
  match getProgram source with
  | .error _ => false
  | .ok ast => decide (inConcreteCoreFragment ast source.globalContext)

#guard concrete max2
#guard concrete add8
#guard !concrete natAddition

-- The semantic backend accepts compound carriers. Use a construction-only
-- instance with its exact type policy so this check remains executable.
private def hasMeaning (source : StrataDDM.Program) : Bool :=
  match getProgram source with
  | .error _ => false
  | .ok ast => (Interpretation.interpProgram Denotational.commands Interpretation.scalarEquality
      (fun _ => true) ast source.globalContext).isOk

def compoundValues :=
#strata
program Boole;
procedure compound(m : Map int string, s : Sequence int) returns (r : string)
{ r := m[2]; assert Sequence.length(s) >= 0; };
#end

#guard hasMeaning compoundValues
#guard checks compoundValues
#guard !concrete compoundValues
#guard !builds compoundValues

end Strata.Boole.Examples
