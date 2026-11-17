/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import StrataDDM.Integration.Lean.HashCommands
meta import StrataBoole.Grammar
meta import StrataBoole.Boole
meta import StrataBoole.Boole.Types
meta import StrataBoole.Boole.Runtime
meta import StrataBoole.Boole.Interp
meta import StrataBoole.Boole.Elaboration.Native
import all StrataBoole.Boole.Elaboration.Native
import all StrataBoole.Boole.Types
import all StrataBoole.Boole.Runtime
import all StrataBoole.Boole.Interp
meta import StrataBoole.Boole.Semantics.Semantics
meta import StrataBoole.Verify
import all StrataBoole.Verify
import all StrataBoole.Boole
import StrataBoole.Boole.Semantics.Adequacy.Theorem
meta import StrataBoole.Boole.Semantics.Adequacy.Theorem
import all StrataBoole.Boole.Semantics.Semantics

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
        match clause.condition state with | .ok (.bool true) => true | _ => false

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

-- Havoc admits every integer, including negative values; no bounded choice set.
example : (Computation.choose (model := .builtins) .int).run {} (.returned (.int (-37)) {}) :=
  ⟨.int (-37), rfl, rfl⟩

-- A failed assumption has no outcomes, rather than an assertion-failure outcome.
example (outcome : Outcome Unit .builtins) :
    ¬ (Computation.assumption (fun _ => .ok (.bool false))).run {} outcome := by
  simp [Bind.bind, Computation.assumption, Computation.test, Computation.evaluate,
    Computation.bind, Computation.pure, Value.bool]

-- A failure is propagated even when the continuation is an infinite loop.
example :
    (Computation.assertion (model := .builtins) "failure" (fun _ => .ok (.bool false)) >>=
      fun _ => Computation.loop (Computation.pure true) (Computation.pure ())).run
      {} (.assertionFailed "failure" {}) := by
  simp [Bind.bind, Computation.assertion, Computation.test, Computation.evaluate,
    Computation.bind, Computation.pure, Computation.loop, Value.bool]
  exact Or.inr (Or.inl ⟨.bool false, {}, ⟨rfl, rfl⟩, rfl⟩)

-- False guards terminate without executing even a failing body.
example : Computation.Iteration (Computation.pure (model := .builtins) false)
    (Computation.assertion "unreachable" (fun _ => .ok (.bool false))) {}
    (.returned () {}) := .stop rfl

-- The type interpretation is systematic and directly reduces to native carriers.
example : ValueType.denote .builtins (.map .int (.sequence .nat)) = (Int → List Nat) := by rfl
example : ValueType.denote .builtins (.arrow .string (.bitvec 32)) = (String → BitVec 32) := by rfl
example : ValueType.denote .builtins .regex = (String → Prop) := by rfl

-- Open names require an explicit carrier and advertised support.
private def tickets : TypeModel :=
  { TypeModel.builtins with
    typeConstructor := fun _ _ => Nat
    hasConstructor := fun name arity => name == "Ticket" && arity == 0 }
example : ValueType.denote tickets (.named "Ticket" []) = Nat := by rfl
#guard ValueType.supported tickets (.named "Ticket" [])
#guard !ValueType.supported .builtins (.named "Ticket" [])

-- A small executable check uses the SAME syntax traversal with the other backend.
private def nativeMax2 : Option Int := do
  let ast ← (getProgram max2).toOption
  let program ← (nativeProgram ast max2.globalContext).toOption
  let config : Native.Config := { choose := fun ty => match ty with
    | .int => some (.int 0) | .bool => some (.bool false) | _ => none }
  match Native.run program { procedure := "max2", arguments := [.int 3, .int 8], globals := [] } config with
  | .outcome (.returned () state) => match state.locals.lookup "r" with
    | some (.int value) => some value | _ => none
  | _ => none

#guard nativeMax2 = some 8

-- A failing assertion remains a semantic failure, not a runner timeout.
private def nativeFailure : Bool :=
  match getProgram failureBeforeDivergence with
  | .error _ => false
  | .ok ast => match nativeProgram ast failureBeforeDivergence.globalContext with
    | .error _ => false
    | .ok program => match Native.run program { procedure := "fail", globals := [], arguments := [] } {} with
      | .outcome (.assertionFailed _ _) => true
      | _ => false

#guard nativeFailure

-- Direct mathematical expressions use native carriers, including compound ones.
example : Expression.binary (model := .builtins) .add (fun _ => .ok (.int 2))
    (fun _ => .ok (.int 2)) {} = .ok (.int 4) := by rfl
example : Expression.sequenceAppend (model := .builtins)
    (fun _ => .ok ⟨.sequence .int, ([1, 2] : List Int)⟩)
    (fun _ => .ok ⟨.sequence .int, ([3] : List Int)⟩) {} = .ok ⟨.sequence .int, ([1, 2, 3] : List Int)⟩ := by rfl
example : Expression.mapGet (model := .builtins)
    (fun _ => .ok ⟨.map .int .int, fun (x : Int) => x + 1⟩)
    (fun _ => .ok (.int 4)) {} = .ok (.int 5) := by rfl

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
  | .outcome (.returned () state) => match state.locals.lookup "r" with
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
  | .ok ast => checkFragment (ValueType.supported .builtins) ast source.globalContext

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
