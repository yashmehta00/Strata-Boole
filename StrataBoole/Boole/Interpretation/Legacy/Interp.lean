/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Source
import Strata.Util.Tactics

public section
namespace Strata.Boole
open StrataDDM

inductive UnaryOp where
  | neg | not | intToNat | natToInt
  deriving DecidableEq, Repr

inductive BinaryOp where
  | add | sub | mul | div | mod | eq | ne | lt | le | gt | ge
  | and | or | implies | iff
  deriving DecidableEq, Repr

/-- A semantic algebra: domains for expressions and statements, together with
the operations that combine their meanings. The structural `interp` functions
are parameterized by this algebra; `Semantics.lean` supplies the Boole domains
and operations. Constructing a meaning does not execute a procedure body. -/
structure Interpretation where
  supportsType : ValueType → Bool := fun _ => true
  Expression : Type
  Statement : Type
  literal : Value → Expression
  apply : Expression → Expression → Expression
  mapGet : Expression → Expression → Expression
  mapSet : Expression → Expression → Expression → Expression
  mapConst : ValueType → Expression → Expression
  sequenceEmpty : ValueType → Expression
  sequenceLength : Expression → Expression
  sequenceAppend : Expression → Expression → Expression
  sequenceBuild : Expression → Expression → Expression
  read : Variable → Expression
  unary : UnaryOp → Expression → Expression
  binary : BinaryOp → Expression → Expression → Expression
  conditional : Expression → Expression → Expression → Expression
  old : Expression → Expression
  skip : Statement
  seq : Statement → Statement → Statement
  declare : Binding → Option Expression → Statement
  assign : Variable → Expression → Statement
  havoc : Variable → ValueType → Statement
  assertion : String → Expression → Statement
  assumption : Expression → Statement
  branch : Option Expression → Statement → Statement → Statement
  loop : Option Expression → Statement → Statement
  scope : Statement → Statement
  block : String → Statement → Statement
  exit : String → Statement

private def interpTypedUnary (I : Interpretation) (op : UnaryOp) (ty : Boole.Type)
    (operand : InterpM I.Expression) : InterpM I.Expression := do
  let _ ← sourceSort ty
  return I.unary op (← operand)

private def interpTypedBinary (I : Interpretation) (op : BinaryOp) (ty : Boole.Type)
    (left right : InterpM I.Expression) : InterpM I.Expression := do
  let _ ← sourceSort ty
  return I.binary op (← left) (← right)

/-- Interpret an expression using source variable bindings and source operations. -/
def interpExpr (I : Interpretation) (e : Boole.Expr) : InterpM I.Expression := do
  match e with
  | .natToInt _ value => return I.literal (.int (Int.ofNat value.val))
  | .strLit _ value => return I.literal (.string value.val)
  | .bv1Lit _ n => return I.literal (.bitvec 1 (BitVec.ofNat 1 n.val))
  | .bv8Lit _ n => return I.literal (.bitvec 8 (BitVec.ofNat 8 n.val))
  | .bv16Lit _ n => return I.literal (.bitvec 16 (BitVec.ofNat 16 n.val))
  | .bv32Lit _ n => return I.literal (.bitvec 32 (BitVec.ofNat 32 n.val))
  | .bv64Lit _ n => return I.literal (.bitvec 64 (BitVec.ofNat 64 n.val))
  | .bv128Lit _ n => return I.literal (.bitvec 128 (BitVec.ofNat 128 n.val))
  | .app _ f a => return I.apply (← interpExpr I f) (← interpExpr I a)
  | .nat_fromInt _ a => interpTypedUnary I .intToNat (.nat default) (interpExpr I a)
  | .nat_toInt _ a => interpTypedUnary I .natToInt (.nat default) (interpExpr I a)
  | .nat_add _ a b => interpTypedBinary I .add (.nat default) (interpExpr I a) (interpExpr I b)
  | .nat_sub _ a b => interpTypedBinary I .sub (.nat default) (interpExpr I a) (interpExpr I b)
  | .nat_mul _ a b => interpTypedBinary I .mul (.nat default) (interpExpr I a) (interpExpr I b)
  | .nat_div _ a b => interpTypedBinary I .div (.nat default) (interpExpr I a) (interpExpr I b)
  | .nat_mod _ a b => interpTypedBinary I .mod (.nat default) (interpExpr I a) (interpExpr I b)
  | .nat_lt _ a b => interpTypedBinary I .lt (.nat default) (interpExpr I a) (interpExpr I b)
  | .nat_le _ a b => interpTypedBinary I .le (.nat default) (interpExpr I a) (interpExpr I b)
  | .nat_gt _ a b => interpTypedBinary I .gt (.nat default) (interpExpr I a) (interpExpr I b)
  | .nat_ge _ a b => interpTypedBinary I .ge (.nat default) (interpExpr I a) (interpExpr I b)
  | .map_get _ key value m index =>
      let _ ← sourceSort (.Map default value key)
      return I.mapGet (← interpExpr I m) (← interpExpr I index)
  | .map_set _ key value m index newValue =>
      let _ ← sourceSort (.Map default value key)
      return I.mapSet (← interpExpr I m) (← interpExpr I index) (← interpExpr I newValue)
  | .map_const _ key value initializer =>
      let _ ← sourceSort (.Map default value key)
      let key ← sourceSort key
      return I.mapConst key (← interpExpr I initializer)
  | .seq_empty _ element =>
      let _ ← sourceSort (.Sequence default element)
      return I.sequenceEmpty (← sourceSort element)
  | .seq_empty_int _ =>
      let _ ← sourceSort (.Sequence default (.int default))
      return I.sequenceEmpty .int
  | .seq_length _ element a =>
      let _ ← sourceSort (.Sequence default element)
      return I.sequenceLength (← interpExpr I a)
  | .seq_append _ element a b =>
      let _ ← sourceSort (.Sequence default element)
      return I.sequenceAppend (← interpExpr I a) (← interpExpr I b)
  | .seq_build _ element a b =>
      let _ ← sourceSort (.Sequence default element)
      return I.sequenceBuild (← interpExpr I a) (← interpExpr I b)
  | .btrue _ => return I.literal (.bool true)
  | .bfalse _ => return I.literal (.bool false)
  | .fvar range index =>
      let some name := (← get).names.nameOf? index
        | reject range s!"Unknown free-variable index {index}"
      let some binding := findBinding name (← get).globals
        | reject range s!"Free variable '{name}' is not a declared global"
      return I.read (.global binding.name)
  | .bvar range index =>
      let some binding := (← get).locals.reverse[index]?
        | reject range s!"Unknown bound-variable index {index}"
      return I.read (.local binding.name)
  | .not _ a => return I.unary .not (← interpExpr I a)
  | .neg_expr _ ty a => interpTypedUnary I .neg ty (interpExpr I a)
  | .add_expr _ ty a b => interpTypedBinary I .add ty (interpExpr I a) (interpExpr I b)
  | .sub_expr _ ty a b => interpTypedBinary I .sub ty (interpExpr I a) (interpExpr I b)
  | .mul_expr _ ty a b => interpTypedBinary I .mul ty (interpExpr I a) (interpExpr I b)
  | .le _ ty a b => interpTypedBinary I .le ty (interpExpr I a) (interpExpr I b)
  | .lt _ ty a b => interpTypedBinary I .lt ty (interpExpr I a) (interpExpr I b)
  | .ge _ ty a b => interpTypedBinary I .ge ty (interpExpr I a) (interpExpr I b)
  | .gt _ ty a b => interpTypedBinary I .gt ty (interpExpr I a) (interpExpr I b)
  | .equal _ ty a b => interpTypedBinary I .eq ty (interpExpr I a) (interpExpr I b)
  | .not_equal _ ty a b => interpTypedBinary I .ne ty (interpExpr I a) (interpExpr I b)
  | .and _ a b => return I.binary .and (← interpExpr I a) (← interpExpr I b)
  | .or _ a b => return I.binary .or (← interpExpr I a) (← interpExpr I b)
  | .implies _ a b => return I.binary .implies (← interpExpr I a) (← interpExpr I b)
  | .equiv _ a b => return I.binary .iff (← interpExpr I a) (← interpExpr I b)
  | .if _ ty c yes no =>
      let _ ← sourceSort ty
      return I.conditional (← interpExpr I c) (← interpExpr I yes) (← interpExpr I no)
  | .old _ ty a =>
      let _ ← sourceSort ty
      return I.old (← interpExpr I a)
  | _ => reject default s!"Unsupported expression: {repr e}"
termination_by sizeOf e

-- The annotations must be supported expressions, but do not control execution.
private def checkInvariants (I : Interpretation) : BooleDDM.Invariants SourceRange → InterpM Unit
  | .nilInvariants _ => pure ()
  | .consInvariants _ _ expression rest => do
      let _ ← interpExpr I expression
      checkInvariants I rest

private def condition (I : Interpretation) : BooleDDM.ExprOrNondet SourceRange → InterpM (Option I.Expression)
  | .condDet _ expression => return some (← interpExpr I expression)
  | .condNondet _ => pure none

mutual
  /-- Interpret a statement; declarations extend the lexical scope of its siblings. -/
  def interpStmt (I : Interpretation) (statement : BooleDDM.Statement SourceRange) : InterpM I.Statement := do
    match statement with
    | .varStatement range _ declarations =>
        let mut result := I.skip
        for declaration in bindings declarations do
          let .bind_mk _ name _ ty := declaration
          let binding ← addLocal range name.val ty
          result := I.seq result (I.declare binding none)
        return result
    | .initStatement range _ ty name expression =>
        let expression ← interpExpr I expression
        let binding ← addLocal range name.val ty
        return I.declare binding (some expression)
    | .assign range _ _ (.lhsIdent _ name) expression =>
        let target ← resolveVariable range name.val true
        return I.assign target.1 (← interpExpr I expression)
    | .havoc_statement range _ name =>
        let target ← resolveVariable range name.val true
        return I.havoc target.1 target.2
    | .assert range annotations label expression =>
        if annotations.val.isSome then reject range "Assertion metadata is outside this fragment"
        return I.assertion (sourceLabel range label.val) (← interpExpr I expression)
    | .assume _ _ _ expression =>
        return I.assumption (← interpExpr I expression)
    | .if_statement _ _ guard yes no =>
        let guard ← condition I guard
        let yes ← interpBlock I yes
        let no ← match no with | .else0 _ => pure I.skip | .else1 _ body => interpBlock I body
        return I.branch guard yes no
    | .while_statement _ _ guard decreases invariants body =>
        let guard ← condition I guard
        if let some (.measure_mk _ expression) := decreases.val then
          let _ ← interpExpr I expression
        checkInvariants I invariants
        return I.loop guard (← interpBlock I body)
    | .block_statement _ _ name body =>
        let body ← withScope do
          modify fun scope => { scope with labels := name.val :: scope.labels }
          interpBlock I body
        return I.block name.val body
    | .exit_statement range _ name =>
        if !(← get).labels.contains name.val then reject range s!"Unbound exit label '{name.val}'"
        return I.exit name.val
    | _ => reject default s!"Unsupported statement: {repr statement}"
    termination_by sizeOf statement

  /-- Compose a statement list in source order. -/
  def interpStmts (I : Interpretation) (statements : List (BooleDDM.Statement SourceRange)) : InterpM I.Statement := do
    match statements with
    | [] => return I.skip
    | statement :: rest => return I.seq (← interpStmt I statement) (← interpStmts I rest)
    termination_by sizeOf statements

  /-- A block restores lexical scope now and runtime local-variable scope later. -/
  def interpBlock (I : Interpretation) (block : BooleDDM.Block SourceRange) : InterpM I.Statement :=
    withScope do
      match block with
      | .block _ ⟨_, statements⟩ => return I.scope (← interpStmts I statements.toList)
    termination_by sizeOf block
    decreasing_by
      cases statements
      simp_all
      omega
end

/-- Interpret requires/ensures as expressions, retaining clause identity and
free attributes. Modifies is a source-level permission on global writes. -/
def interpContract (I : Interpretation) (specification : Option (BooleDDM.Spec SourceRange)) : InterpM (Contract I.Expression) := do
  let mut result : Contract I.Expression := {}
  if let some (.spec_mk _ elements) := specification then
    for element in elements.val do
      match element with
      | .modifies_spec range names =>
          for name in names.val do
            if (findBinding name.val (← get).globals).isNone then
              reject range s!"Unknown modified global '{name.val}'"
            if !result.modifies.contains name.val then
              result := { result with modifies := result.modifies ++ [name.val] }
      | .requires_spec range label free expression =>
          let clause := ⟨sourceLabel range label.val, free.val.isSome, ← interpExpr I expression⟩
          result := { result with requires := result.requires ++ [clause] }
      | .ensures_spec range label free expression =>
          let clause := ⟨sourceLabel range label.val, free.val.isSome, ← interpExpr I expression⟩
          result := { result with ensures := result.ensures ++ [clause] }
  return result

/-- Interpret a structured procedure, including its independent contract meaning. -/
def interpProc (I : Interpretation) (range : SourceRange) (name : String)
    (typeArgs : Option (BooleDDM.TypeArgs SourceRange))
    (parameters : BooleDDM.Bindings SourceRange)
    (outputs : Option (BooleDDM.MonoDeclList SourceRange))
    (specification : Option (BooleDDM.Spec SourceRange))
    (body : Option (BooleDDM.Block SourceRange)) : InterpM (InterpProcedure I.Expression I.Statement) :=
  withScope do
    if typeArgs.isSome then reject range "Polymorphic procedures are outside this fragment"
    let inputs ← inputBindings parameters
    let outputs ← match outputs with | none => pure [] | some outputs => outputBindings outputs
    let contract ← interpContract I specification
    modify fun scope => { scope with modifies := contract.modifies, labels := [name] }
    let some body := body | reject range "A procedure body is required"
    return ⟨name, inputs, outputs, contract, I.block name (← interpBlock I body)⟩

/-- Interpret Boole declarations without lowering to Core. Globals are retained
whenever their source type has a meaning; Core rejection of unlowerable types
is the lowering's responsibility. -/
def interpProgram (I : Interpretation) (program : Boole.Program) (names : GlobalContext) :
    Except InterpError (InterpProgram I.Expression I.Statement) :=
  let action : InterpM (InterpProgram I.Expression I.Statement) := do
    let .prog _ commands := program
    let mut procedures : List (InterpProcedure I.Expression I.Statement) := []
    for command in commands.val do
      match command with
      | .command_typedecl .. => pure ()
      | .command_var range (.bind_mk _ name _ ty) =>
          if !procedures.isEmpty then reject range "Declare globals before procedures"
          let binding := { name := name.val, sort := ← sourceSort ty : Binding }
          fresh range binding
          modify fun scope => { scope with globals := scope.globals ++ [binding] }
      | .boole_procedure range name types inputs outputs decreases spec body =>
          if decreases.val.isSome then reject range "Procedure decreases clauses are outside this fragment"
          if procedures.any (fun p => p.name == name.val) then reject range "Duplicate procedure name"
          let procedure ← interpProc I range name.val types.val inputs outputs.val spec.val body.val
          procedures := procedures ++ [procedure]
      | .command_procedure range _ name types inputs spec body =>
          if procedures.any (fun p => p.name == name.val) then reject range "Duplicate procedure name"
          let procedure ← interpProc I range name.val types.val inputs none spec.val body.val
          procedures := procedures ++ [procedure]
      | _ => reject default s!"Unsupported declaration: {repr command}"
    return ⟨(← get).globals, procedures⟩
  action.run' { names := names, supportsType := I.supportsType }

private def checkingInterpretation (supportsType : ValueType → Bool) : Interpretation where
  supportsType := supportsType
  Expression := Unit
  Statement := Unit
  literal := fun _ => ()
  apply := fun _ _ => ()
  mapGet := fun _ _ => ()
  mapSet := fun _ _ _ => ()
  mapConst := fun _ _ => ()
  sequenceEmpty := fun _ => ()
  sequenceLength := fun _ => ()
  sequenceAppend := fun _ _ => ()
  sequenceBuild := fun _ _ => ()
  read := fun _ => ()
  unary := fun _ _ => ()
  binary := fun _ _ _ => ()
  conditional := fun _ _ _ => ()
  old := fun _ => ()
  skip := ()
  seq := fun _ _ => ()
  declare := fun _ _ => ()
  assign := fun _ _ => ()
  havoc := fun _ _ => ()
  assertion := fun _ _ => ()
  assumption := fun _ => ()
  branch := fun _ _ _ => ()
  loop := fun _ _ => ()
  scope := fun _ => ()
  block := fun _ _ => ()
  exit := fun _ => ()

/-- Check syntax, binding and type support with the same traversal used to build
meanings. This discards the meanings and does not run the program. -/
def checkFragment (supportsType : ValueType → Bool) (source : Boole.Program)
    (names : GlobalContext) : Bool :=
  (interpProgram (checkingInterpretation supportsType) source names).isOk

end Strata.Boole
