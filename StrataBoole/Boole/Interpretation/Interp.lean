/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Interpretation.Expressions

/-! Resolve source bindings and types, then fold expressions and statements
into their meanings. Expression cases use the mathematical operations in
`Expressions.lean`. Statement cases use a supplied command algebra.
The lexical scope exists only during construction. -/

public section
namespace Strata.Boole.Interpretation
open StrataDDM

/-- The index of an expression parsed without a known expected type.
This pair is used only while constructing meanings. -/
structure SomeExpr where
  sort : ValueType
  meaning : Expr sort

def SomeExpr.expect (range : SourceRange) (t : ValueType) (expression : SomeExpr) :
    InterpM (Expr t) :=
  if h : expression.sort = t then pure (h ▸ expression.meaning)
  else reject range s!"Expected {repr t}, got {repr expression.sort}"

private inductive Arithmetic where
  | add | sub | mul

private def Arithmetic.apply [Add α] [Sub α] [Mul α] : Arithmetic → α → α → α
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)

private def arithmetic (range : SourceRange) (op : Arithmetic)
    (t : ValueType) (x y : Expr t) : InterpM SomeExpr :=
  match t with
  | .int => pure ⟨.int, Expr.zip op.apply x y⟩
  | .nat => pure ⟨.nat, Expr.zip op.apply x y⟩
  | .real => pure ⟨.real, Expr.zip op.apply x y⟩
  | .bitvec n => pure ⟨.bitvec n, Expr.zip op.apply x y⟩
  | _ => reject range s!"Arithmetic is undefined for {repr t}"

private inductive Comparison where
  | lt | le | gt | ge

private def Comparison.apply [LT α] [LE α] [DecidableLT α] [DecidableLE α] :
    Comparison → α → α → Bool
  | .lt => fun x y => decide (x < y)
  | .le => fun x y => decide (x ≤ y)
  | .gt => fun x y => decide (y < x)
  | .ge => fun x y => decide (y ≤ x)

private def comparison (range : SourceRange) (op : Comparison)
    (t : ValueType) (x y : Expr t) : InterpM SomeExpr :=
  match t with
  | .int => pure ⟨.bool, Expr.zip op.apply x y⟩
  | .nat => pure ⟨.bool, Expr.zip op.apply x y⟩
  | .real => pure ⟨.bool, Expr.zip op.apply x y⟩
  | .bitvec n => pure ⟨.bool, Expr.zip (a := .bitvec n) (b := .bitvec n) (fun a b => op.apply a.toNat b.toNat) x y⟩
  | _ => reject range s!"Ordering is undefined for {repr t}"

private def negation (range : SourceRange) (t : ValueType) (x : Expr t) : InterpM SomeExpr :=
  match t with
  | .int => pure ⟨.int, Expr.map Neg.neg x⟩
  | .real => pure ⟨.real, Expr.map Neg.neg x⟩
  | .bitvec n => pure ⟨.bitvec n, Expr.map Neg.neg x⟩
  | _ => reject range s!"Negation is undefined for {repr t}"

private def equality (equal : Equality) (range : SourceRange) (t : ValueType) :
    InterpM (t.denote → t.denote → Bool) := do
  let some test := equal t | reject range s!"No executable equality for {repr t}"
  return test

private def withOperands (range : SourceRange) (ty : Boole.Type)
    (left right : InterpM SomeExpr)
    (combine : (t : ValueType) → Expr t → Expr t → InterpM SomeExpr) :
    InterpM SomeExpr := do
  let t ← sourceSort ty
  combine t (← (← left).expect range t) (← (← right).expect range t)

private def lift1 (range : SourceRange) (a b : ValueType) (f : a.denote → b.denote)
    (operand : InterpM SomeExpr) : InterpM SomeExpr := do
  return ⟨b, Expr.map f (← (← operand).expect range a)⟩

private def lift2 (range : SourceRange) (a b c : ValueType)
    (f : a.denote → b.denote → c.denote) (left right : InterpM SomeExpr) :
    InterpM SomeExpr := do
  return ⟨c, Expr.zip f (← (← left).expect range a) (← (← right).expect range b)⟩

private def bitvector (width : Nat) (n : Nat) : SomeExpr :=
  ⟨.bitvec width, Expr.constant (.bitvec width) (BitVec.ofNat width n)⟩

/-- Interpret the immediate subexpressions and combine their typed values.
Source types select overloaded operations during construction. -/
def interpExpr (equal : Equality) (expression : Boole.Expr) : InterpM SomeExpr := do
  match expression with
  | .natToInt _ n => return ⟨.int, Expr.constant .int (Int.ofNat n.val)⟩
  | .strLit _ s => return ⟨.string, Expr.constant .string s.val⟩
  | .bv1Lit _ n => return bitvector 1 n.val
  | .bv8Lit _ n => return bitvector 8 n.val
  | .bv16Lit _ n => return bitvector 16 n.val
  | .bv32Lit _ n => return bitvector 32 n.val
  | .bv64Lit _ n => return bitvector 64 n.val
  | .bv128Lit _ n => return bitvector 128 n.val
  | .btrue _ => return ⟨.bool, Expr.constant .bool true⟩
  | .bfalse _ => return ⟨.bool, Expr.constant .bool false⟩
  | .fvar range index =>
      let some name := (← get).names.nameOf? index
        | reject range s!"Unknown free-variable index {index}"
      let some binding := findBinding name (← get).globals
        | reject range s!"Free variable '{name}' is not a declared global"
      return ⟨binding.sort, Expr.read binding.sort (.global name)⟩
  | .bvar range index =>
      let some binding := (← get).locals.reverse[index]?
        | reject range s!"Unknown bound-variable index {index}"
      return ⟨binding.sort, Expr.read binding.sort (.local binding.name)⟩
  | .app range f a =>
      let function ← interpExpr equal f
      match function with
      | ⟨.arrow domain codomain, fn⟩ =>
          return ⟨codomain, Expr.zip (a := .arrow domain codomain) (fun g x => g x) fn
            (← (← interpExpr equal a).expect range domain)⟩
      | _ => reject range "Expected a function"
  | .nat_fromInt range a => lift1 range .int .nat Int.toNat (interpExpr equal a)
  | .nat_toInt range a => lift1 range .nat .int Int.ofNat (interpExpr equal a)
  | .nat_add range a b => lift2 range .nat .nat .nat (· + ·) (interpExpr equal a) (interpExpr equal b)
  | .nat_sub range a b => lift2 range .nat .nat .nat (· - ·) (interpExpr equal a) (interpExpr equal b)
  | .nat_mul range a b => lift2 range .nat .nat .nat (· * ·) (interpExpr equal a) (interpExpr equal b)
  | .nat_div range a b => lift2 range .nat .nat .nat (· / ·) (interpExpr equal a) (interpExpr equal b)
  | .nat_mod range a b => lift2 range .nat .nat .nat (· % ·) (interpExpr equal a) (interpExpr equal b)
  | .nat_lt range a b => lift2 range .nat .nat .bool Comparison.lt.apply (interpExpr equal a) (interpExpr equal b)
  | .nat_le range a b => lift2 range .nat .nat .bool Comparison.le.apply (interpExpr equal a) (interpExpr equal b)
  | .nat_gt range a b => lift2 range .nat .nat .bool Comparison.gt.apply (interpExpr equal a) (interpExpr equal b)
  | .nat_ge range a b => lift2 range .nat .nat .bool Comparison.ge.apply (interpExpr equal a) (interpExpr equal b)
  | .map_get range key value m k =>
      let _ ← sourceSort (.Map range value key)
      let key ← sourceSort key
      let value ← sourceSort value
      lift2 range (.map key value) key value (fun f x => f x) (interpExpr equal m) (interpExpr equal k)
  | .map_set range key value m k v =>
      let _ ← sourceSort (.Map range value key)
      let key ← sourceSort key
      let value ← sourceSort value
      let m ← (← interpExpr equal m).expect range (.map key value)
      let k ← (← interpExpr equal k).expect range key
      let v ← (← interpExpr equal v).expect range value
      let test ← equality equal range key
      return ⟨.map key value, Expr.mapSet test m k v⟩
  | .map_const range key value initializer =>
      let _ ← sourceSort (.Map range value key)
      let key ← sourceSort key
      let value ← sourceSort value
      lift1 range value (.map key value) (fun v _ => v) (interpExpr equal initializer)
  | .seq_empty range element =>
      let _ ← sourceSort (.Sequence range element)
      let element ← sourceSort element
      return ⟨.sequence element, Expr.constant (.sequence element) []⟩
  | .seq_empty_int range =>
      let _ ← sourceSort (.Sequence range (.int range))
      return ⟨.sequence .int, Expr.constant (.sequence .int) []⟩
  | .seq_length range element a =>
      let _ ← sourceSort (.Sequence range element)
      let element ← sourceSort element
      lift1 range (.sequence element) .int (fun xs => Int.ofNat xs.length) (interpExpr equal a)
  | .seq_append range element a b =>
      let _ ← sourceSort (.Sequence range element)
      let element ← sourceSort element
      let sequence := ValueType.sequence element
      lift2 range sequence sequence sequence List.append (interpExpr equal a) (interpExpr equal b)
  | .seq_build range element a b =>
      let _ ← sourceSort (.Sequence range element)
      let element ← sourceSort element
      let sequence := ValueType.sequence element
      lift2 range sequence element sequence (fun xs x => xs ++ [x]) (interpExpr equal a) (interpExpr equal b)
  | .not range a => lift1 range .bool .bool (! ·) (interpExpr equal a)
  | .neg_expr range ty a =>
      let t ← sourceSort ty
      negation range t (← (← interpExpr equal a).expect range t)
  | .add_expr range ty a b =>
      withOperands range ty (interpExpr equal a) (interpExpr equal b) (arithmetic range .add)
  | .sub_expr range ty a b =>
      withOperands range ty (interpExpr equal a) (interpExpr equal b) (arithmetic range .sub)
  | .mul_expr range ty a b =>
      withOperands range ty (interpExpr equal a) (interpExpr equal b) (arithmetic range .mul)
  | .lt range ty a b =>
      withOperands range ty (interpExpr equal a) (interpExpr equal b) (comparison range .lt)
  | .le range ty a b =>
      withOperands range ty (interpExpr equal a) (interpExpr equal b) (comparison range .le)
  | .gt range ty a b =>
      withOperands range ty (interpExpr equal a) (interpExpr equal b) (comparison range .gt)
  | .ge range ty a b =>
      withOperands range ty (interpExpr equal a) (interpExpr equal b) (comparison range .ge)
  | .equal range ty a b =>
      withOperands range ty (interpExpr equal a) (interpExpr equal b) fun t x y => do
        return ⟨.bool, Expr.zip (← equality equal range t) x y⟩
  | .not_equal range ty a b =>
      withOperands range ty (interpExpr equal a) (interpExpr equal b) fun t x y => do
        let test ← equality equal range t
        return ⟨.bool, Expr.zip (fun a b => !test a b) x y⟩
  | .and range a b => lift2 range .bool .bool .bool (· && ·) (interpExpr equal a) (interpExpr equal b)
  | .or range a b => lift2 range .bool .bool .bool (· || ·) (interpExpr equal a) (interpExpr equal b)
  | .implies range a b => lift2 range .bool .bool .bool (fun a b => !a || b) (interpExpr equal a) (interpExpr equal b)
  | .equiv range a b => lift2 range .bool .bool .bool (· == ·) (interpExpr equal a) (interpExpr equal b)
  | .if range ty c yes no =>
      let t ← sourceSort ty
      return ⟨t, Expr.ite (← (← interpExpr equal c).expect range .bool)
        (← (← interpExpr equal yes).expect range t) (← (← interpExpr equal no).expect range t)⟩
  | .old range ty a =>
      let t ← sourceSort ty
      return ⟨t, Expr.old (← (← interpExpr equal a).expect range t)⟩
  | _ => reject default s!"Unsupported expression: {repr expression}"
termination_by sizeOf expression

/-- An absent guard is a nondeterministic choice of true or false. -/
abbrev Guard := Option (Expr .bool)

structure CommandAlgebra (Command : Type) where
  skip : Command
  seq : Command → Command → Command
  declare : (binding : Binding) → Option (Expr binding.sort) → Command
  assign : {t : ValueType} → Variable → Expr t → Command
  havoc : Variable → ValueType → Command
  assertion : String → Expr .bool → Command
  assumption : Expr .bool → Command
  branch : Guard → Command → Command → Command
  loop : Guard → Command → Command
  scope : Command → Command
  block : String → Command → Command
  exit : String → Command

abbrev Procedure (Command : Type) := InterpProcedure (Expr .bool) Command
abbrev Program (Command : Type) := InterpProgram (Expr .bool) Command

/-! The deterministic state effects used before either backend handles control. -/
namespace Effect

def assign (reference : Variable) (expression : Expr t) (state : State) : Result :=
  match Expr.read t reference state with
  | .error reason => (.runtimeError reason, state)
  | .ok _ => match expression state with
    | .ok value => (.normal, state.update reference ⟨t, value⟩)
    | .error reason => (.runtimeError reason, state)

def declare (binding : Binding) (initializer : Expr binding.sort) (state : State) : Result :=
  if (state.locals.lookup binding.name).isSome then
    (.runtimeError (.duplicateLocal binding.name), state)
  else match initializer state with
    | .ok value => (.normal, { state with locals := state.locals ++ [(binding.name, ⟨binding.sort, value⟩)] })
    | .error reason => (.runtimeError reason, state)

def assertion (label : String) (expression : Expr .bool) (state : State) : Result :=
  match expression state with
  | .ok true => (.normal, state)
  | .ok false => (.assertionFailure label, state)
  | .error reason => (.runtimeError reason, state)

end Effect

/-! The source fold constructs command meanings using the supplied algebra.
Source expressions are given typed meanings before entering the command operations. -/

-- The annotations must be supported expressions, but do not control execution.
private def checkInvariants (equal : Equality) : BooleDDM.Invariants SourceRange → InterpM Unit
  | .nilInvariants _ => pure ()
  | .consInvariants range _ expression rest => do
      let _ ← (← interpExpr equal expression).expect range .bool
      checkInvariants equal rest

private def condition (equal : Equality) : BooleDDM.ExprOrNondet SourceRange → InterpM (Guard)
  | .condDet range expression => return some (← (← interpExpr equal expression).expect range .bool)
  | .condNondet _ => pure none

mutual
  /-- Interpret a statement; declarations extend the lexical scope of its siblings. -/
  def interpStmt (I : CommandAlgebra C) (equal : Equality) (statement : BooleDDM.Statement SourceRange) : InterpM C := do
    match statement with
    | .varStatement range _ declarations =>
        let mut result := I.skip
        for declaration in bindings declarations do
          let .bind_mk _ name _ ty := declaration
          let binding ← addLocal range name.val ty
          result := I.seq result (I.declare binding none)
        return result
    | .initStatement range _ ty name expression =>
        let expression ← interpExpr equal expression
        let binding ← addLocal range name.val ty
        return I.declare binding (some (← expression.expect range binding.sort))
    | .assign range _ _ (.lhsIdent _ name) expression =>
        let target ← resolveVariable range name.val true
        return I.assign target.1 (← (← interpExpr equal expression).expect range target.2)
    | .havoc_statement range _ name =>
        let target ← resolveVariable range name.val true
        return I.havoc target.1 target.2
    | .assert range annotations label expression =>
        if annotations.val.isSome then reject range "Assertion metadata is outside this fragment"
        return I.assertion (sourceLabel range label.val) (← (← interpExpr equal expression).expect range .bool)
    | .assume range _ _ expression =>
        return I.assumption (← (← interpExpr equal expression).expect range .bool)
    | .if_statement _ _ guard yes no =>
        let guard ← condition equal guard
        let yes ← interpBlock I equal yes
        let no ← match no with | .else0 _ => pure I.skip | .else1 _ body => interpBlock I equal body
        return I.branch guard yes no
    | .while_statement _ _ guard decreases invariants body =>
        let guard ← condition equal guard
        if let some (.measure_mk _ expression) := decreases.val then
          let _ ← interpExpr equal expression
        checkInvariants equal invariants
        return I.loop guard (← interpBlock I equal body)
    | .block_statement _ _ name body =>
        let body ← withScope do
          modify fun scope => { scope with labels := name.val :: scope.labels }
          interpBlock I equal body
        return I.block name.val body
    | .exit_statement range _ name =>
        if !(← get).labels.contains name.val then reject range s!"Unbound exit label '{name.val}'"
        return I.exit name.val
    | _ => reject default s!"Unsupported statement: {repr statement}"
    termination_by sizeOf statement

  /-- Compose a statement list in source order. -/
  def interpStmts (I : CommandAlgebra C) (equal : Equality) (statements : List (BooleDDM.Statement SourceRange)) : InterpM C := do
    match statements with
    | [] => return I.skip
    | statement :: rest => return I.seq (← interpStmt I equal statement) (← interpStmts I equal rest)
    termination_by sizeOf statements

  /-- A block restores lexical scope now and runtime local-variable scope later. -/
  def interpBlock (I : CommandAlgebra C) (equal : Equality) (block : BooleDDM.Block SourceRange) : InterpM C :=
    withScope do
      match block with
      | .block _ ⟨_, statements⟩ => return I.scope (← interpStmts I equal statements.toList)
    termination_by sizeOf block
    decreasing_by
      cases statements
      simp_all
      omega
end

/-- Interpret requires/ensures as expressions, retaining clause identity and
free attributes. Modifies is a source-level permission on global writes. -/
def interpContract (equal : Equality) (specification : Option (BooleDDM.Spec SourceRange)) : InterpM (Contract (Expr .bool)) := do
  let mut result : Contract (Expr .bool) := {}
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
          let clause := ⟨sourceLabel range label.val, free.val.isSome, ← (← interpExpr equal expression).expect range .bool⟩
          result := { result with requires := result.requires ++ [clause] }
      | .ensures_spec range label free expression =>
          let clause := ⟨sourceLabel range label.val, free.val.isSome, ← (← interpExpr equal expression).expect range .bool⟩
          result := { result with ensures := result.ensures ++ [clause] }
  return result

/-- Interpret a structured procedure, including its independent contract meaning. -/
def interpProc (I : CommandAlgebra C) (equal : Equality) (range : SourceRange) (name : String)
    (typeArgs : Option (BooleDDM.TypeArgs SourceRange))
    (parameters : BooleDDM.Bindings SourceRange)
    (outputs : Option (BooleDDM.MonoDeclList SourceRange))
    (specification : Option (BooleDDM.Spec SourceRange))
    (body : Option (BooleDDM.Block SourceRange)) : InterpM (Procedure C) :=
  withScope do
    if typeArgs.isSome then reject range "Polymorphic procedures are outside this fragment"
    let inputs ← inputBindings parameters
    let outputs ← match outputs with | none => pure [] | some outputs => outputBindings outputs
    let contract ← interpContract equal specification
    modify fun scope => { scope with modifies := contract.modifies, labels := [name] }
    let some body := body | reject range "A procedure body is required"
    return ⟨name, inputs, outputs, contract, I.block name (← interpBlock I equal body)⟩

/-- Interpret Boole declarations without lowering to Core. Globals are retained
whenever their source type has a meaning; Core rejection of unlowerable types
is the lowering's responsibility. -/
def interpProgram (I : CommandAlgebra C) (equal : Equality)
    (supportsType : ValueType → Bool) (program : Boole.Program) (names : GlobalContext) :
    Except InterpError (Program C) :=
  let action : InterpM (Program C) := do
    let .prog _ commands := program
    let mut procedures : List (Procedure C) := []
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
          let procedure ← interpProc I equal range name.val types.val inputs outputs.val spec.val body.val
          procedures := procedures ++ [procedure]
      | .command_procedure range _ name types inputs spec body =>
          if procedures.any (fun p => p.name == name.val) then reject range "Duplicate procedure name"
          let procedure ← interpProc I equal range name.val types.val inputs none spec.val body.val
          procedures := procedures ++ [procedure]
      | _ => reject default s!"Unsupported declaration: {repr command}"
    return ⟨(← get).globals, procedures⟩
  action.run' { names := names, supportsType := supportsType }

end Strata.Boole.Interpretation
