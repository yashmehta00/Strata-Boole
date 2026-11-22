/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole
public import StrataBoole.Boole.Interpretation.Types
import Strata.Util.Tactics

/-! # Source bindings, scopes and procedure interfaces -/

public section
namespace Strata.Boole
open StrataDDM

/-- A source variable declaration. Names are kept for diagnostics and interfaces. -/
structure Binding where
  name : String
  sort : ValueType
  deriving DecidableEq, Repr

/-- Global and local variables occupy different source stores. -/
inductive Variable where
  | global (name : String)
  | local (name : String)
  deriving DecidableEq, Repr

/-- An individual specification clause, before or after interpretation. -/
structure Clause (E : Type) where
  label : String
  free : Bool
  condition : E

/-- Contracts remain separate from procedure-body execution. -/
structure Contract (E : Type) where
  requires : List (Clause E) := []
  ensures : List (Clause E) := []
  modifies : List String := []

/-- A procedure's interface, contract meanings and body meaning. -/
structure InterpProcedure (E S : Type) where
  name : String
  inputs : List Binding
  outputs : List Binding
  contract : Contract E
  body : S

/-- Program declarations containing meanings, not another statement AST. -/
structure InterpProgram (E S : Type) where
  globals : List Binding
  procedures : List (InterpProcedure E S)

/-- An unsupported construct or invalid source binding, with its source location. -/
structure InterpError where
  range : SourceRange
  message : String
  deriving Repr

/-- Source bindings visible while interpreting a statement. Bound-variable
indices refer to `locals` in reverse declaration order, as in the parsed AST.
Shadowing is rejected in this fragment, matching the target's fresh-slot rules. -/
structure Scope where
  names : GlobalContext := {}
  globals : List Binding := []
  locals : List Binding := []
  modifies : List String := []
  labels : List String := []
  supportsType : ValueType → Bool := fun _ => true

abbrev InterpM := StateT Scope (Except InterpError)

def reject (range : SourceRange) (message : String) : InterpM α :=
  throw ⟨range, message⟩

/-- Resolve the built-in types admitted by the interpretation. -/
def sourceSort (ty : Boole.Type) : InterpM ValueType := do
  let result ← match ty with
    | .bool _ => pure .bool | .int _ => pure .int | .nat _ => pure .nat
    | .real _ => pure .real | .string _ => pure .string | .regex _ => pure .regex
    | .bv _ width => match width with
      | .W1 _ => pure (.bitvec 1) | .W8 _ => pure (.bitvec 8)
      | .W16 _ => pure (.bitvec 16) | .W32 _ => pure (.bitvec 32)
      | .W64 _ => pure (.bitvec 64) | .W128 _ => pure (.bitvec 128)
      | _ => reject default "A concrete bitvector width is required"
    | .arrow _ a b => ValueType.arrow <$> sourceSort a <*> sourceSort b
    | .Map _ value key => ValueType.map <$> sourceSort key <*> sourceSort value
    | .Sequence _ element => ValueType.sequence <$> sourceSort element
    | .Set _ element => ValueType.set <$> sourceSort element
    | .tvar range _ | .bvar range _ =>
        reject range "Type variables are outside the denotational fragment"
    | .fvar range index arguments =>
        let some name := (← get).names.nameOf? index
          | reject range "Unknown type constructor"
        let arguments ← arguments.toList.reverse.mapM sourceSort
        if name == "Set" then
          match arguments with
          | [element] => pure (.set element)
          | _ => reject range "Set requires one type argument"
        else reject range s!"Unsupported named type '{name}'"
    | _ => reject default "Width markers are not standalone value types"
  if !(← get).supportsType result then reject default s!"Type has no interpretation in this model: {repr result}"
  return result
termination_by sizeOf ty
decreasing_by
  all_goals first
    | (simp_all; omega)
    | (cases arguments; simp_all; term_by_mem)

def withScope (action : InterpM α) : InterpM α := do
  let saved ← get
  let result ← action
  set saved
  return result

def findBinding (name : String) (bindings : List Binding) : Option Binding :=
  bindings.find? (fun b => b.name == name)

def fresh (range : SourceRange) (binding : Binding) : InterpM Unit := do
  let scope ← get
  if binding.name.isEmpty || binding.name.contains ' ' then
    reject range "Variable names must be nonempty and contain no spaces"
  if (findBinding binding.name (scope.locals ++ scope.globals)).isSome then
    reject range s!"Duplicate or shadowed variable '{binding.name}' is outside this fragment"

def addLocal (range : SourceRange) (name : String) (ty : Boole.Type) : InterpM Binding := do
  let binding : Binding := ⟨name, ← sourceSort ty⟩
  fresh range binding
  modify fun scope => { scope with locals := scope.locals ++ [binding] }
  return binding

def resolveVariable (range : SourceRange) (name : String) (writing := false) : InterpM (Variable × ValueType) := do
  let scope ← get
  if let some binding := findBinding name scope.locals then
    return (.local name, binding.sort)
  if let some binding := findBinding name scope.globals then
    if writing && !scope.modifies.contains name then
      reject range s!"Global '{name}' is not in this procedure's modifies clause"
    return (.global name, binding.sort)
  reject range s!"Unknown variable '{name}'"

def sourceLabel (range : SourceRange) (label : Option (BooleDDM.Label SourceRange)) : String :=
  match label with
  | some (.label _ name) => name.val
  | none => s!"at_{range.start}"

def bindings : BooleDDM.DeclList SourceRange → List (BooleDDM.Bind SourceRange)
  | .declAtom _ binding => [binding]
  | .declPush _ rest binding => bindings rest ++ [binding]

def inputBindings (parameters : BooleDDM.Bindings SourceRange) : InterpM (List Binding) := do
  let .mkBindings _ parameters := parameters
  parameters.val.toList.mapM fun
    | .mkBinding range name (.expr ty) => addLocal range name.val ty
    | parameter => reject default s!"Unsupported parameter: {repr parameter}"

def outputBindings : BooleDDM.MonoDeclList SourceRange → InterpM (List Binding)
  | .monoDeclAtom range (.mono_bind_mk _ name ty) => do
      return [← addLocal range name.val ty]
  | .monoDeclPush range rest (.mono_bind_mk _ name ty) => do
      let rest ← outputBindings rest
      return rest ++ [← addLocal range name.val ty]

end Strata.Boole
