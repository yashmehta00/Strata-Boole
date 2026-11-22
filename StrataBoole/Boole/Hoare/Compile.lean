/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Hoare.Rules
import all StrataBoole.Boole.Interpretation.Legacy.Interp
import all StrataBoole.Boole.Interpretation.Source
import all StrataBoole.Boole.Interpretation.Legacy.Runtime
import all StrataBoole.Boole.Interpretation.Runtime

/-! Compile Boole statements to predicate transformers. Track writes alongside
the transformer to determine which variables a loop can change. -/

public section
namespace Strata.Boole.Hoare

open StrataDDM

private def scalar : ValueType → Bool
  | .bool | .int | .nat | .real | .string | .bitvec _ => true
  | _ => false

private def numeric : ValueType → Bool
  | .int | .nat | .real | .bitvec _ => true
  | _ => false

private structure TypedExpr where
  sort : ValueType
  eval : Expression

private def TypedExpr.expect (e : TypedExpr) (sort : ValueType) (range : SourceRange) :
    InterpM Expression :=
  if e.sort == sort then pure e.eval
  else reject range s!"Expected {repr sort}, got {repr e.sort}"

private def literal (value : Value) : TypedExpr := ⟨value.sort, fun _ => .ok value⟩

def binaryValue (op : BinaryOp) (left right : Value) : Except RuntimeError Value :=
  Expression.binaryWith (fun a b => match a.equal? b with
    | some result => .ok result
    | none => .error .wrongType) op (fun _ => .ok left) (fun _ => .ok right) {}

@[cbv_opaque, expose] def binary (op : BinaryOp) (left right : Expression) : Expression :=
  fun state =>
    (left state).bind fun a =>
    (right state).bind fun b =>
    binaryValue op a b

theorem binaryValue_int (op : BinaryOp) (a b : Int) :
    binaryValue op ⟨.int, a⟩ ⟨.int, b⟩ = match op with
    | .add => .ok (.int (a + b)) | .sub => .ok (.int (a - b)) | .mul => .ok (.int (a * b))
    | .lt => .ok (.bool (decide (a < b))) | .le => .ok (.bool (decide (a ≤ b)))
    | .gt => .ok (.bool (decide (b < a))) | .ge => .ok (.bool (decide (b ≤ a)))
    | .eq => .ok (.bool (a == b)) | .ne => .ok (.bool (!(a == b)))
    | _ => .error .wrongType := by
  cases op <;> rfl

theorem binaryValue_bool (op : BinaryOp) (a b : Bool) :
    binaryValue op ⟨.bool, a⟩ ⟨.bool, b⟩ = match op with
    | .and => .ok (.bool (a && b)) | .or => .ok (.bool (a || b))
    | .implies => .ok (.bool (!a || b)) | .iff | .eq => .ok (.bool (a == b))
    | .ne => .ok (.bool (!(a == b)))
    | _ => .error .wrongType := by
  cases op <;> rfl

private theorem binaryValue_nat (op : BinaryOp) (a b : Nat) :
    binaryValue op ⟨.nat, a⟩ ⟨.nat, b⟩ = match op with
    | .add => .ok (.nat (a + b)) | .sub => .ok (.nat (a - b)) | .mul => .ok (.nat (a * b))
    | .div => .ok (.nat (a / b)) | .mod => .ok (.nat (a % b))
    | .lt => .ok (.bool (decide (a < b))) | .le => .ok (.bool (decide (a ≤ b)))
    | .gt => .ok (.bool (decide (b < a))) | .ge => .ok (.bool (decide (b ≤ a)))
    | .eq => .ok (.bool (a == b)) | .ne => .ok (.bool (!(a == b)))
    | _ => .error .wrongType := by
  cases op <;> rfl

private theorem binaryValue_bitvec (op : BinaryOp) (width : Nat) (a b : BitVec width) :
    binaryValue op ⟨.bitvec width, a⟩ ⟨.bitvec width, b⟩ = match op with
    | .add => .ok (.bitvec width (a + b))
    | .sub => .ok (.bitvec width (a - b))
    | .mul => .ok (.bitvec width (a * b))
    | .lt => .ok (.bool (decide (a.toNat < b.toNat)))
    | .le => .ok (.bool (decide (a.toNat ≤ b.toNat)))
    | .gt => .ok (.bool (decide (b.toNat < a.toNat)))
    | .ge => .ok (.bool (decide (b.toNat ≤ a.toNat)))
    | .eq => .ok (.bool (decide (a = b)))
    | .ne => .ok (.bool (!(decide (a = b))))
    | _ => .error .wrongType := by
  cases op <;> simp [binaryValue, Expression.binaryWith, Expression.atType, Value.equal?,
    bind, pure, Except.bind, Except.pure, Value.bitvec] <;> rfl

private theorem binaryValue_real (op : BinaryOp) (a b : Rat) :
    binaryValue op ⟨.real, a⟩ ⟨.real, b⟩ = match op with
    | .add => .ok (.real (a + b)) | .sub => .ok (.real (a - b)) | .mul => .ok (.real (a * b))
    | .div => .ok (.real (a / b))
    | .lt => .ok (.bool (decide (a < b))) | .le => .ok (.bool (decide (a ≤ b)))
    | .gt => .ok (.bool (decide (b < a))) | .ge => .ok (.bool (decide (b ≤ a)))
    | .eq => .ok (.bool (a == b)) | .ne => .ok (.bool (!(a == b)))
    | _ => .error .wrongType := by
  cases op <;> rfl

private theorem binaryValue_string (op : BinaryOp) (a b : String) :
    binaryValue op ⟨.string, a⟩ ⟨.string, b⟩ = match op with
    | .eq => .ok (.bool (a == b)) | .ne => .ok (.bool (!(a == b)))
    | _ => .error .wrongType := by
  cases op <;> rfl

private def typedBinary (range : SourceRange) (op : BinaryOp) (result operand : ValueType)
    (a b : TypedExpr) : InterpM TypedExpr := do
  return ⟨result, binary op (← a.expect operand range) (← b.expect operand range)⟩

private structure ReadContext where
  /-- In requires, these slots are in the binder stack but unavailable to read. -/
  requiresOutputs : Option (List String) := none
  old : Bool := false

private def read (range : SourceRange) (context : ReadContext) (slot : Variable)
    (binding : Binding) : InterpM TypedExpr := do
  match slot with
  | .local _ =>
    if (context.requiresOutputs.getD []).contains binding.name then
      reject range s!"Output '{binding.name}' is unavailable in requires"
  | .global _ =>
    if context.old && context.requiresOutputs.isSome && (← get).modifies.contains binding.name then
      reject range s!"old({binding.name}) is unavailable in requires"
  let eval := Expression.read slot
  return ⟨binding.sort, if context.old then Expression.old eval else eval⟩

private def expr (e : Boole.Expr) (context : ReadContext := {}) : InterpM TypedExpr := do
  match e with
  | .natToInt _ n => return literal (.int n.val)
  | .strLit _ s => return literal (.string s.val)
  | .btrue _ => return literal (.bool true)
  | .bfalse _ => return literal (.bool false)
  | .bv1Lit _ n | .bv8Lit _ n | .bv16Lit _ n | .bv32Lit _ n | .bv64Lit _ n | .bv128Lit _ n =>
    let width := match e with
      | .bv1Lit .. => 1 | .bv8Lit .. => 8 | .bv16Lit .. => 16 | .bv32Lit .. => 32
      | .bv64Lit .. => 64 | _ => 128
    return literal (.bitvec width (BitVec.ofNat width n.val))
  | .fvar range index =>
    let scope ← get
    let some name := scope.names.nameOf? index | reject range s!"Unknown free-variable index {index}"
    let some binding := findBinding name scope.globals | reject range s!"Unknown global '{name}'"
    read range context (.global name) binding
  | .bvar range index =>
    let some binding := (← get).locals.reverse[index]?
      | reject range s!"Unknown bound-variable index {index}"
    read range context (.local binding.name) binding
  | .not range a =>
    return ⟨.bool, Expression.unary .not (← (← expr a context).expect .bool range)⟩
  | .neg_expr range ty a =>
    let sort ← sourceSort ty
    unless sort == .int || sort == .real || (match sort with | .bitvec _ => true | _ => false) do
      reject range s!"Negation is unsupported at {repr sort}"
    return ⟨sort, Expression.unary .neg (← (← expr a context).expect sort range)⟩
  | .add_expr range ty a b | .sub_expr range ty a b | .mul_expr range ty a b
  | .le range ty a b | .lt range ty a b | .ge range ty a b | .gt range ty a b
  | .equal range ty a b | .not_equal range ty a b =>
    let sort ← sourceSort ty
    let (op, result) := match e with
      | .add_expr .. => (BinaryOp.add, sort)
      | .sub_expr .. => (.sub, sort)
      | .mul_expr .. => (.mul, sort)
      | .le .. => (.le, .bool)
      | .lt .. => (.lt, .bool)
      | .ge .. => (.ge, .bool)
      | .gt .. => (.gt, .bool)
      | .equal .. => (.eq, .bool)
      | _ => (.ne, .bool)
    unless op == .eq || op == .ne || numeric sort do
      reject range s!"Arithmetic is unsupported at {repr sort}"
    typedBinary range op result sort (← expr a context) (← expr b context)
  | .and range a b | .or range a b | .implies range a b | .equiv range a b =>
    let op := match e with
      | .and .. => BinaryOp.and | .or .. => .or | .implies .. => .implies | _ => .iff
    typedBinary range op .bool .bool (← expr a context) (← expr b context)
  | .nat_fromInt range a =>
    return ⟨.nat, Expression.unary .intToNat (← (← expr a context).expect .int range)⟩
  | .nat_toInt range a =>
    return ⟨.int, Expression.unary .natToInt (← (← expr a context).expect .nat range)⟩
  | .nat_add range a b | .nat_sub range a b | .nat_mul range a b
  | .nat_div range a b | .nat_mod range a b
  | .nat_lt range a b | .nat_le range a b | .nat_gt range a b | .nat_ge range a b =>
    let (op, result) := match e with
      | .nat_add .. => (BinaryOp.add, ValueType.nat) | .nat_sub .. => (.sub, .nat)
      | .nat_mul .. => (.mul, .nat) | .nat_div .. => (.div, .nat) | .nat_mod .. => (.mod, .nat)
      | .nat_lt .. => (.lt, .bool) | .nat_le .. => (.le, .bool)
      | .nat_gt .. => (.gt, .bool) | _ => (.ge, .bool)
    typedBinary range op result .nat (← expr a context) (← expr b context)
  | .if range ty guard yes no =>
    let sort ← sourceSort ty
    return ⟨sort, Expression.conditional
      (← (← expr guard context).expect .bool range)
      (← (← expr yes context).expect sort range)
      (← (← expr no context).expect sort range)⟩
  | .old range ty e =>
    let sort ← sourceSort ty
    return ⟨sort, ← (← expr e { context with old := true }).expect sort range⟩
  | _ => reject default s!"Unsupported Hoare expression: {repr e}"
termination_by sizeOf e

private def boolean (range : SourceRange) (e : Boole.Expr) (context : ReadContext := {}) :
    InterpM Expression := do
  (← expr e context).expect .bool range

private def guardExpr : BooleDDM.ExprOrNondet SourceRange → InterpM (Option Expression)
  | .condDet range e => some <$> boolean range e
  | .condNondet _ => pure none

private def measureExpr : Option (BooleDDM.Measure SourceRange) → InterpM (Option Expression)
  | none => pure none
  | some (.measure_mk range e) => do return some (← (← expr e).expect .int range)

/-- Read source clause conditions in their declared order. -/
@[cbv_opaque] def clausesHold (clauses : List (Clause Expression)) (s : State) : Prop :=
  match clauses with
  | [] => True
  | c :: rest => Obligation c.label (Holds c.condition s) ∧ clausesHold rest s

private def invariants : BooleDDM.Invariants SourceRange → InterpM (List (Clause Expression))
  | .nilInvariants _ => pure []
  | .consInvariants range label e rest => do
    return ⟨sourceLabel range label.val, false, ← boolean range e⟩ :: (← invariants rest)

private abbrev Writes := List (Variable × ValueType)

private structure Compiled where
  command : Transformer
  writes : Writes := []

private def Compiled.seq (first second : Compiled) : Compiled :=
  ⟨first.command.seq second.command, (first.writes ++ second.writes).eraseDups⟩

private def writable (readOnly : List String) (range : SourceRange) (name : String) :
    InterpM (Variable × ValueType) := do
  if readOnly.contains name then reject range s!"Input '{name}' is read-only"
  resolveVariable range name true

mutual
  private def stmt (s : BooleDDM.Statement SourceRange) (readOnly : List String) :
      InterpM Compiled := do
    match s with
    | .initStatement range _ ty name e =>
      let rhs ← expr e
      let binding ← addLocal range name.val ty
      return ⟨.step (Transformer.initState binding (← rhs.expect binding.sort range)), []⟩
    | .varStatement range _ declarations =>
      let mut command := Transformer.skip
      for .bind_mk _ name _ ty in bindings declarations do
        let binding ← addLocal range name.val ty
        let init := Transformer.arbitrary fun (value : binding.sort.denote) =>
          .step (Transformer.initState binding (fun _ => .ok ⟨binding.sort, value⟩))
        command := command.seq init
      return ⟨command, []⟩
    | .assign range _ _ (.lhsIdent _ name) e =>
      let target ← writable readOnly range name.val
      let rhs ← (← expr e).expect target.2 range
      return ⟨.step (Transformer.assignState target.1 rhs), [target]⟩
    | .havoc_statement range _ name =>
      let target ← writable readOnly range name.val
      let command := Transformer.arbitrary fun (value : target.2.denote) =>
        .step (Transformer.assignState target.1 (fun _ => .ok ⟨target.2, value⟩))
      return ⟨command, [target]⟩
    | .assert range annotations label e =>
      if annotations.val.isSome then
        reject range "Assertion metadata is unsupported by Hoare verification"
      return ⟨.assertion (sourceLabel range label.val) (← boolean range e), []⟩
    | .assume range _ _ e =>
      return ⟨.assumption (← boolean range e), []⟩
    | .if_statement _ _ guard yes no =>
      let guard ← guardExpr guard
      let yes ← block yes readOnly
      let no ← match no with
        | .else0 _ => pure { command := .skip }
        | .else1 _ body => block body readOnly
      return ⟨.branch guard yes.command no.command, (yes.writes ++ no.writes).eraseDups⟩
    | .while_statement _ _ guard measure invs body =>
      let guard ← guardExpr guard
      let measure ← measureExpr measure.val
      let invariant := clausesHold (← invariants invs)
      let body ← block body readOnly
      return ⟨.loop body.writes guard invariant measure body.command, body.writes⟩
    | .block_statement range _ name body =>
      let compiled ← withScope do
        if (← get).labels.contains name.val then
          reject range s!"Block label '{name.val}' shadows an enclosing label"
        modify fun scope => { scope with labels := name.val :: scope.labels }
        block body readOnly
      return { compiled with command := .block name.val compiled.command }
    | .exit_statement range _ name =>
      unless (← get).labels.contains name.val do reject range s!"Unbound exit label '{name.val}'"
      return ⟨.exit name.val, []⟩
    | _ => reject default s!"Unsupported Hoare statement: {repr s}"
  termination_by sizeOf s

  private def stmts (ss : List (BooleDDM.Statement SourceRange)) (readOnly : List String) :
      InterpM Compiled := do
    match ss with
    | [] => return { command := .skip }
    | [s] => stmt s readOnly
    | s :: rest =>
      let first ← stmt s readOnly
      return first.seq (← stmts rest readOnly)
  termination_by sizeOf ss

  private def block (b : BooleDDM.Block SourceRange) (readOnly : List String) : InterpM Compiled :=
    withScope do
      let outer := (← get).locals
      match b with
      | .block _ ⟨_, ss⟩ =>
        let body ← stmts ss.toList readOnly
        let writes := body.writes.filter fun (slot, _) => match slot with
          | .global _ => true
          | .local name => (findBinding name outer).isSome
        return ⟨.scope body.command, writes⟩
  termination_by sizeOf b
  decreasing_by
    cases ss
    simp_all
    omega
end

private def contract (specification : Option (BooleDDM.Spec SourceRange)) (outputs : List Binding) :
    InterpM (Contract Expression) := do
  let some (.spec_mk _ elements) := specification | return {}
  let mut modifies := []
  for element in elements.val do
    if let .modifies_spec range names := element then
      for name in names.val do
        if (findBinding name.val (← get).globals).isNone then
          reject range s!"Unknown modified global '{name.val}'"
        unless modifies.contains name.val do
          modifies := modifies ++ [name.val]
  modify fun scope => { scope with modifies }
  let mut result : Contract Expression := { modifies }
  for element in elements.val do
    match element with
    | .requires_spec range label free e =>
      let condition ← boolean range e { requiresOutputs := some (outputs.map Binding.name) }
      result := { result with requires := result.requires ++
        [⟨sourceLabel range label.val, free.val.isSome, condition⟩] }
    | .ensures_spec range label free e =>
      let condition ← boolean range e
      result := { result with ensures := result.ensures ++
        [⟨sourceLabel range label.val, free.val.isSome, condition⟩] }
    | .modifies_spec .. => pure ()
  return result

abbrev Procedure := InterpProcedure Expression Transformer
abbrev CompiledProgram := InterpProgram Expression Transformer

private def procedure (range : SourceRange) (name : String)
    (types : Option (BooleDDM.TypeArgs SourceRange)) (inputs : BooleDDM.Bindings SourceRange)
    (outputs : Option (BooleDDM.MonoDeclList SourceRange))
    (specification : Option (BooleDDM.Spec SourceRange))
    (body : Option (BooleDDM.Block SourceRange)) : InterpM Procedure :=
  withScope do
    if types.isSome then reject range "Polymorphic procedures are unsupported by Hoare verification"
    let entry ← get
    let ins ← inputBindings inputs
    let outs ← match outputs with | none => pure [] | some ds => outputBindings ds
    let specs ← contract specification outs
    let some body := body | reject range "Hoare verification requires a procedure body"
    set { entry with
      locals := entry.locals ++ ins ++ outs
      modifies := specs.modifies
      labels := [name] }
    let compiled ← block body (ins.map Binding.name)
    return ⟨name, ins, outs, specs, .block name compiled.command⟩

private def declaration (compiled : List Procedure) :
    BooleDDM.Command SourceRange → InterpM (List Procedure)
  | .command_var range (.bind_mk _ name _ ty) => do
    unless compiled.isEmpty do reject range "Declare globals before procedures"
    let binding : Binding := ⟨name.val, ← sourceSort ty⟩
    fresh range binding
    modify fun scope => { scope with globals := scope.globals ++ [binding] }
    return compiled
  | .boole_procedure range name types inputs outputs decreases specs body => do
    if decreases.val.isSome then reject range "Procedure decreases is unsupported by Hoare verification"
    if compiled.any (·.name == name.val) then reject range "Duplicate procedure name"
    return compiled ++ [← procedure range name.val types.val inputs outputs.val specs.val body.val]
  | .command_procedure range annotations name types inputs specs body => do
    if annotations.val.isSome then
      reject range "Procedure metadata is unsupported by Hoare verification"
    if compiled.any (·.name == name.val) then reject range "Duplicate procedure name"
    return compiled ++ [← procedure range name.val types.val inputs none specs.val body.val]
  | command => reject default s!"Unsupported Hoare declaration: {repr command}"

private def declarations (commands : List (BooleDDM.Command SourceRange))
    (compiled : List Procedure) : InterpM (List Procedure) :=
  match commands with
  | [] => pure compiled
  | command :: rest => do
    declarations rest (← declaration compiled command)

/-- Construct procedure transformers from Boole syntax and its own name context. -/
def compile (source : Boole.Program) (names : GlobalContext) :
    Except InterpError CompiledProgram :=
  let action : InterpM CompiledProgram := do
    let .prog _ commands := source
    let procedures ← declarations commands.val.toList []
    return ⟨(← get).globals, procedures⟩
  action.run' { names, supportsType := scalar }

end Strata.Boole.Hoare
