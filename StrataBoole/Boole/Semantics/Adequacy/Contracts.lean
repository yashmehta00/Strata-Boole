/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Semantics.Adequacy.Expressions
public import StrataBoole.Boole.Semantics.Adequacy.Typing
import all StrataBoole.Boole.Semantics.Adequacy.Lowering
public import StrataBoole.Boole.Semantics.Adequacy.Entry
import all StrataBoole.Boole.Semantics.CoreReference
import all StrataBoole.Boole.Interp
import all StrataBoole.Boole.Semantics.Semantics
import all StrataBoole.Verify
import all Strata.Languages.Core.Procedure
import all Strata.Languages.Core.ProcedureType
import all Strata.Util.ListMap
import Strata.Util.ListMapProps

public section
namespace Strata.Boole

/-! ## Contract expressions -/

private def clauseCount (isClause : BooleDDM.SpecElt SourceRange → Bool)
    (spec : Option (BooleDDM.Spec SourceRange)) : Nat :=
  match spec with
  | none => 0
  | some (.spec_mk _ elements) => elements.val.toList.countP isClause

private def isRequires : BooleDDM.SpecElt SourceRange → Bool
  | .requires_spec .. => true
  | _ => false

private def isEnsures : BooleDDM.SpecElt SourceRange → Bool
  | .ensures_spec .. => true
  | _ => false

private theorem forIn_count {σ ε α β : Type} (items : List α)
    (step : α → β → StateT σ (Except ε) (ForInStep β)) (size : β → Nat) (includeItem : α → Bool)
    (increases : ∀ item before entry control final,
      step item before entry = .ok (control, final) →
      ∃ next, control = .yield next ∧ size next = size before + (if includeItem item then 1 else 0))
    (before after : β) (entry final : σ)
    (ran : (forIn items before step) entry = .ok (after, final)) :
    size after = size before + items.countP includeItem := by
  induction items generalizing before entry with
  | nil =>
    have equal : before = after := congrArg Prod.fst (Except.ok.inj ran)
    simp [← equal]
  | cons item items ih =>
    simp only [List.forIn_cons, bind, StateT.bind, Except.bind, pure] at ran
    cases executed : step item before entry with
    | error => simp [executed] at ran
    | ok result =>
      obtain ⟨control, nextState⟩ := result
      obtain ⟨next, rfl, counted⟩ := increases _ _ _ _ _ executed
      have tail : (forIn items next step) nextState = .ok (after, final) := by
        simpa [executed] using ran
      rw [ih next nextState tail, counted, List.countP_cons]
      split <;> omega

private theorem interpModifies_preserves (I : Interpretation) (range : SourceRange)
    (names : Array (StrataDDM.Ann String SourceRange)) (before after : Contract I.Expression)
    (entry final : Scope) (size : Contract I.Expression → Nat)
    (onlyClauses : ∀ contract modifies, size { contract with modifies } = size contract)
    (ran : (forIn names before (fun (name : StrataDDM.Ann String SourceRange) (contract : Contract I.Expression) => do
      if (findBinding name.val (← (get : InterpM Scope)).globals).isNone then
        reject range s!"Unknown modified global '{name.val}'"
      if !contract.modifies.contains name.val then
        pure (.yield { contract with modifies := contract.modifies ++ [name.val] })
      else pure (.yield contract))) entry = .ok (after, final)) :
    size after = size before := by
  rw [← (Array.toArray_toList (xs := names)), List.forIn_toArray] at ran
  have counted := forIn_count _ _ size (fun _ => false)
    (by
      intro item old state control next step
      have readScope : (get : InterpM Scope) state = .ok (state, state) := rfl
      repeat' first
        | contradiction
        | simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
            readScope, reject, throw, throwThe, MonadExceptOf.throw] at step
        | (refine ⟨_, (congrArg Prod.fst (Except.ok.inj step)).symm, ?_⟩
           first | exact onlyClauses _ _ | rfl)
        | split at step)
    _ _ _ _ ran
  simpa using counted

private theorem interpContract_clauseCounts (I : Interpretation)
    (spec : Option (BooleDDM.Spec SourceRange)) (entry final : Scope)
    (contract : Contract I.Expression) (ran : interpContract I spec entry = .ok (contract, final)) :
    contract.requires.length = clauseCount isRequires spec ∧
    contract.ensures.length = clauseCount isEnsures spec := by
  cases spec with
  | none =>
    have empty : ({} : Contract I.Expression) = contract := congrArg Prod.fst (Except.ok.inj ran)
    simp [← empty, clauseCount]
  | some specification =>
    cases specification with
    | spec_mk range elements =>
      unfold interpContract at ran
      simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
      split at ran
      · contradiction
      · rename_i accumulated loop
        have equal : accumulated.1 = contract := congrArg Prod.fst (Except.ok.inj ran)
        rw [← equal]
        rw [← (Array.toArray_toList (xs := elements.val)), List.forIn_toArray] at loop
        constructor
        · simpa [clauseCount] using
            (forIn_count _ _ (fun c : Contract I.Expression => c.requires.length) isRequires
              (by
                intro item before state control next step
                cases item
                all_goals
                  repeat' first
                    | contradiction
                    | simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at step
                    | (refine ⟨_, (congrArg Prod.fst (Except.ok.inj step)).symm, ?_⟩
                       simp [isRequires])
                    | split at step
                all_goals
                  rename_i namesRan
                  exact interpModifies_preserves I _ _ _ _ _ _ (fun c => c.requires.length)
                    (fun _ _ => rfl) namesRan)
              _ _ _ _ loop)
        · simpa [clauseCount] using
            (forIn_count _ _ (fun c : Contract I.Expression => c.ensures.length) isEnsures
              (by
                intro item before state control next step
                cases item
                all_goals
                  repeat' first
                    | contradiction
                    | simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at step
                    | (refine ⟨_, (congrArg Prod.fst (Except.ok.inj step)).symm, ?_⟩
                       simp [isEnsures])
                    | split at step
                all_goals
                  rename_i namesRan
                  exact interpModifies_preserves I _ _ _ _ _ _ (fun c => c.ensures.length)
                    (fun _ _ => rfl) namesRan)
              _ _ _ _ loop)

private theorem toCoreSpec_clauseCounts (range : SourceRange) (name : String)
    (spec : Option (BooleDDM.Spec SourceRange)) (entry final : TranslateState)
    (contract : Core.Procedure.Spec) (ran : toCoreSpec range name spec entry = .ok (contract, final)) :
    contract.preconditions.toList.length = clauseCount isRequires spec ∧
    contract.postconditions.toList.length = clauseCount isEnsures spec := by
  cases spec with
  | none =>
    have empty : ({ preconditions := [], postconditions := [] } : Core.Procedure.Spec) = contract :=
      congrArg Prod.fst (Except.ok.inj ran)
    rw [← empty]
    exact ⟨rfl, rfl⟩
  | some specification =>
    cases specification with
    | spec_mk range elements =>
      simp only [toCoreSpec, toCoreSpecElts, bind, StateT.bind, Except.bind, pure,
        StateT.pure, Except.pure] at ran
      split at ran
      · contradiction
      · rename_i accumulated loop
        have equal : _ = contract := congrArg Prod.fst (Except.ok.inj ran)
        rw [← equal]
        change accumulated.1.1.reverse.length = _ ∧ accumulated.1.2.reverse.length = _
        simp only [List.length_reverse]
        constructor
        · simpa [clauseCount] using
            (forIn_count _ _ (fun c : List (String × Core.Procedure.Check) ×
                List (String × Core.Procedure.Check) => c.1.length) isRequires
              (by
                intro item before state control next step
                cases item
                case' requires_spec range label free expression => cases label; cases free
                case' ensures_spec range label free expression => cases label; cases free
                all_goals
                  repeat' first
                    | contradiction
                    | simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at step
                    | (refine ⟨_, (congrArg Prod.fst (Except.ok.inj step)).symm, ?_⟩
                       simp [isRequires])
                    | split at step)
              _ _ _ _ loop)
        · simpa [clauseCount] using
            (forIn_count _ _ (fun c : List (String × Core.Procedure.Check) ×
                List (String × Core.Procedure.Check) => c.2.length) isEnsures
              (by
                intro item before state control next step
                cases item
                case' requires_spec range label free expression => cases label; cases free
                case' ensures_spec range label free expression => cases label; cases free
                all_goals
                  repeat' first
                    | contradiction
                    | simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at step
                    | (refine ⟨_, (congrArg Prod.fst (Except.ok.inj step)).symm, ?_⟩
                       simp [isEnsures])
                    | split at step)
              _ _ _ _ loop)

private theorem interpProc_clauseCounts (I : Interpretation) (range : SourceRange) (name : String)
    (types : Option (BooleDDM.TypeArgs SourceRange)) (inputs : BooleDDM.Bindings SourceRange)
    (outputs : Option (BooleDDM.MonoDeclList SourceRange)) (spec : Option (BooleDDM.Spec SourceRange))
    (body : Option (BooleDDM.Block SourceRange)) (entry final : Scope)
    (procedure : InterpProcedure I.Expression I.Statement)
    (ran : interpProc I range name types inputs outputs spec body entry = .ok (procedure, final)) :
    procedure.contract.requires.length = clauseCount isRequires spec ∧
    procedure.contract.ensures.length = clauseCount isEnsures spec := by
  unfold interpProc at ran
  obtain ⟨_, ran⟩ := withScope_success ran
  cases types <;> cases outputs <;> cases body
  all_goals
    repeat' first
      | contradiction
      | simp only [Option.isSome, Bool.false_eq_true, ite_false, bind, StateT.bind, Except.bind,
          pure, StateT.pure, Except.pure, modify, modifyGet, MonadStateOf.modifyGet,
          StateT.modifyGet, reject, throw, throwThe, MonadExceptOf.throw] at ran
      | (have equal : _ = procedure.contract :=
           congrArg (fun result => result.1.contract) (Except.ok.inj ran)
         rw [← equal]
         exact interpContract_clauseCounts I spec _ _ _ (by assumption))
      | split at ran

private theorem scopedCoreSpec_clauseCounts (range : SourceRange) (name : String)
    (spec : Option (BooleDDM.Spec SourceRange)) (contract : Core.Procedure.Spec)
    (xs : List String) (entry final : TranslateState)
    (ran : withBVars xs (toCoreSpec range name spec) entry = .ok (contract, final)) :
    contract.preconditions.toList.length = clauseCount isRequires spec ∧
    contract.postconditions.toList.length = clauseCount isEnsures spec := by
  obtain ⟨_, _, called⟩ := withBVars_success ran
  exact toCoreSpec_clauseCounts range name spec _ _ contract called

private theorem translateProcedureDecl_clauseCounts (range : SourceRange) (name : String)
    (types : List String) (inputs outputs : ListMap Core.CoreIdent Lambda.LMonoTy)
    (spec : Option (BooleDDM.Spec SourceRange)) (body : Option (BooleDDM.Block SourceRange))
    (entry final : TranslateState) (decls : List Core.Decl)
    (ran : translateProcedureDecl range name types inputs outputs spec body entry = .ok (decls, final))
    (procedure : Core.Procedure) (metadata : Imperative.MetaData Core.Expression)
    (present : .proc procedure metadata ∈ decls) :
    procedure.spec.preconditions.toList.length = clauseCount isRequires spec ∧
    procedure.spec.postconditions.toList.length = clauseCount isEnsures spec := by
  cases body
  all_goals
    repeat' first
      | contradiction
      | simp only [translateProcedureDecl, bind, StateT.bind, Except.bind, pure, StateT.pure,
          Except.pure, get, getThe, MonadStateOf.get, StateT.get, modify, modifyGet,
          MonadStateOf.modifyGet, StateT.modifyGet] at ran
      | (have equal : _ = decls := congrArg Prod.fst (Except.ok.inj ran)
         rw [← equal] at present
         simp only [List.mem_singleton, Core.Decl.proc.injEq] at present
         rcases present with ⟨rfl, rfl⟩
         exact scopedCoreSpec_clauseCounts range name spec _ _ _ _ (by assumption))
      | split at ran

private theorem updateCheckExprs_keys (expressions : List Core.Expression.Expr)
    (checks : ListMap String Core.Procedure.Check) :
    (Core.Procedure.Spec.updateCheckExprs expressions checks).keys = checks.keys := by
  have lengths (checks : List Core.Procedure.Check) (es : List Core.Expression.Expr) :
      (Core.Procedure.Spec.updateCheckExprs.go es checks).length = checks.length := by
    induction es generalizing checks with
    | nil => cases checks <;> rfl
    | cons e es ih =>
      cases checks with
      | nil => rfl
      | cons c cs => simp [Core.Procedure.Spec.updateCheckExprs.go, ih]
  have keyLength : checks.keys.length = checks.toList.length := ListMap.keys.length
  have valueLength : checks.values.length = checks.toList.length := ListMap.values_length _
  rw [ListMap.keys_eq_map_fst (Core.Procedure.Spec.updateCheckExprs expressions checks)]
  change (checks.keys.zip (Core.Procedure.Spec.updateCheckExprs.go expressions checks.values)).map
    Prod.fst = checks.keys
  exact List.map_fst_zip (by rw [lengths, keyLength, valueLength]; exact Nat.le_refl _)

/-- The checked specification installs precisely the expressions returned
by the two condition-checking runs, keeping their positions in the raw
requires and ensures lists. -/
private theorem checkedProcedure_contract_runs {program : Core.Program} {raw checked : Core.Procedure}
    (checkedByCore : ProcedureWasChecked program raw checked) :
    ∃ (context : Core.Expression.TyContext) (preEntry preExit postEntry postExit : Core.Expression.TyEnv)
      (pre post : Array Core.Expression.Expr),
      Core.Procedure.typeCheckConditions context preEntry raw.spec.preconditions raw.header.name =
        .ok (pre, preExit) ∧
      Core.Procedure.typeCheckConditions context postEntry raw.spec.postconditions raw.header.name =
        .ok (post, postExit) ∧
      checked.spec.preconditions = Core.Procedure.Spec.updateCheckExprs pre.toList raw.spec.preconditions ∧
      checked.spec.postconditions = Core.Procedure.Spec.updateCheckExprs post.toList raw.spec.postconditions := by
  obtain ⟨context, environment, final, metadata, success⟩ := checkedByCore
  unfold Core.Procedure.typeCheck at success
  simp only [bind, Except.bind] at success
  repeat' first
    | contradiction
    | (obtain rfl := congrArg Prod.fst (Except.ok.inj success)
       exact ⟨context, _, _, _, _, _, _, by assumption, by assumption, rfl, rfl⟩)
    | split at success

/-- Core checking keeps the order and names of the requires and ensures clauses. -/
theorem checkedProcedure_clauseKeys {program : Core.Program} {raw checked : Core.Procedure}
    (checkedByCore : ProcedureWasChecked program raw checked) :
    checked.spec.preconditions.keys = raw.spec.preconditions.keys ∧
    checked.spec.postconditions.keys = raw.spec.postconditions.keys := by
  obtain ⟨_, _, _, _, _, pre, post, _, _, preconditions, postconditions⟩ :=
    checkedProcedure_contract_runs checkedByCore
  rw [preconditions, postconditions]
  exact ⟨updateCheckExprs_keys pre.toList _, updateCheckExprs_keys post.toList _⟩

private def commandSpecification : BooleDDM.Command SourceRange → Option (BooleDDM.Spec SourceRange)
  | .boole_procedure _ _ _ _ _ _ specification _ => specification.val
  | .command_procedure _ _ _ _ _ specification _ => specification.val
  | _ => none

/-- Interpretation and lowering count the same Boole requires and ensures clauses. -/
theorem lowered_clauseCounts {command : BooleDDM.Command SourceRange}
    {procedure : ProcedureMeaning} {raw : Core.Procedure}
    (interpreted : ProcedureWasInterpreted (denotation .builtins) command procedure)
    (translated : ProcedureWasLowered command raw) :
    procedure.contract.requires.length = raw.spec.preconditions.toList.length ∧
    procedure.contract.ensures.length = raw.spec.postconditions.toList.length := by
  let spec := commandSpecification command
  have source : procedure.contract.requires.length = clauseCount isRequires spec ∧
      procedure.contract.ensures.length = clauseCount isEnsures spec := by
    have ran := interpreted
    cases shape : command <;> simp only [shape, ProcedureWasInterpreted] at ran
    all_goals
      first
      | contradiction
      | obtain ⟨_, _, called⟩ := ran
        simp only [spec, shape, commandSpecification]
        exact interpProc_clauseCounts _ _ _ _ _ _ _ _ _ _ _ called
  have lowered : raw.spec.preconditions.toList.length = clauseCount isRequires spec ∧
      raw.spec.postconditions.toList.length = clauseCount isEnsures spec := by
    obtain ⟨entry, final, decls, metadata, ran, present⟩ := translated
    have interpreted := interpreted
    cases shape : command <;> simp only [shape, ProcedureWasInterpreted] at interpreted
    all_goals try contradiction
    all_goals simp only [shape, toCoreDecls] at ran
    case' boole_procedure range name types inputs returns decreases specification body =>
      obtain ⟨_, outputs⟩ := returns
      cases outputs
    case' command_procedure range annotations name types inputs specification body =>
      cases modifiers : hasOutOrInoutBinding inputs
      case some bad =>
        obtain ⟨parameter, modifier⟩ := bad
        simp [modifiers, bind, StateT.bind, Except.bind, throwAt, throw, throwThe,
          MonadExceptOf.throw, get, getThe, MonadStateOf.get, StateT.get, StateT.lift,
          pure, Except.pure] at ran
      case' none => simp only [modifiers] at ran
    all_goals
      simp only [spec, shape, commandSpecification]
      obtain ⟨_, ran⟩ := withTypeBVars_success ran
      repeat' first
        | contradiction
        | simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
        | exact translateProcedureDecl_clauseCounts _ _ _ _ _ _ _ _ _ _ ran _ _ present
        | split at ran
  exact ⟨source.1.trans lowered.1.symm, source.2.trans lowered.2.symm⟩

/-- Each source clause corresponds to the checked expression in the same
position. Compare their truth for every well-typed interface state. -/
def ContractClausesMatch (globals : List Binding) (procedure : ProcedureMeaning)
    (source : List (Clause Expression)) (target : ListMap String Core.Procedure.Check) : Prop :=
  source.length = target.toList.length ∧
    ∀ pair ∈ source.zip target.toList, ∀ state, procedureStateWellTyped globals procedure state →
      (pair.1.holds state ↔
        Core.Expression.eval coreRuntimeFactory (coreStore state) pair.2.2.expr =
          some (Imperative.HasBool.ttVal coreRuntimeFactory))

/-- Declarative typing gives every precondition and postcondition expression
a Boolean type. If erasing annotations makes a raw procedure's specification
equal to the typed procedure's specification, each raw clause has a
same-position Boolean-typed counterpart. -/
theorem declarative_contract_clause_typed
    {program : Core.Program} {context : Core.Expression.TyContext}
    {scopes : Core.TypeSpec.TypeScopes} {raw annotated : Core.Procedure}
    (typed : Core.TypeSpec.ProcWellTyped program context scopes annotated)
    (sameSpec : Core.Procedure.Spec.eraseTypes annotated.spec =
      Core.Procedure.Spec.eraseTypes raw.spec) :
    (∀ (i : Nat) (label : String) (check : Core.Procedure.Check), raw.spec.preconditions.toList[i]? = some (label, check) →
      ∃ resolved, annotated.spec.preconditions.toList[i]? = some (label, resolved) ∧
        Core.Procedure.Check.eraseTypes resolved = Core.Procedure.Check.eraseTypes check ∧
        Core.TypeSpec.ExprWellTyped context
          (Core.TypeSpec.procInputScopes scopes annotated) resolved.expr .bool) ∧
    (∀ (i : Nat) (label : String) (check : Core.Procedure.Check), raw.spec.postconditions.toList[i]? = some (label, check) →
      ∃ resolved, annotated.spec.postconditions.toList[i]? = some (label, resolved) ∧
        Core.Procedure.Check.eraseTypes resolved = Core.Procedure.Check.eraseTypes check ∧
        Core.TypeSpec.ExprWellTyped context
          (Core.TypeSpec.procBodyScopes scopes annotated) resolved.expr .bool) := by
  constructor
  · intro i label check found
    apply typed_clause_at typed.preconditionsTyped ?_ found
    have equal := congrArg (fun spec : Core.Procedure.Spec => spec.preconditions.toList) sameSpec
    simpa [Core.Procedure.Spec.eraseTypes, ListMap.toList] using equal
  · intro i label check found
    apply typed_clause_at typed.postconditionsTyped ?_ found
    have equal := congrArg (fun spec : Core.Procedure.Spec => spec.postconditions.toList) sameSpec
    simpa [Core.Procedure.Spec.eraseTypes, ListMap.toList] using equal

private theorem mapPairValue_length {α β : Type} (f : β → β) (items : List (α × β)) :
    (items.map fun (key, value) => (key, f value)).length = items.length := by
  induction items with
  | nil => rfl
  | cons head tail ih => cases head; simp [ih]

/-- One interpreted Boole clause and its position in the Core specification
have the same truth value on a source state. The remaining semantic work is
to connect the expression closure produced by interpExpr with evaluation of
the corresponding lowered Core expression. -/
private theorem declarative_clause_truth
    {command : BooleDDM.Command SourceRange} {source : ProcedureMeaning}
    {raw annotated : Core.Procedure} {program : Core.Program}
    {globals : List Binding} {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    (layout : ProcedureLayout globals source annotated)
    (interpreted : ProcedureWasInterpreted (denotation .builtins) command source)
    (translated : ProcedureWasLowered command raw)
    (typed : Core.TypeSpec.ProcWellTyped program context scopes annotated)
    (sameSpec : Core.Procedure.Spec.eraseTypes annotated.spec =
      Core.Procedure.Spec.eraseTypes raw.spec)
    (postcondition : Bool)
    (pair : Clause Expression × (String × Core.Procedure.Check))
    (paired : pair ∈
      (if postcondition then source.contract.ensures else source.contract.requires).zip
        (if postcondition then annotated.spec.postconditions.toList else annotated.spec.preconditions.toList))
    (state : State) (stateTyped : procedureStateWellTyped globals source state) :
    pair.1.holds state ↔
      Core.Expression.eval coreRuntimeFactory (coreStore state) pair.2.2.expr =
        some (Imperative.HasBool.ttVal coreRuntimeFactory) := by
  sorry

/-- Build requires and ensures agreement for a declaratively typed procedure
whose specification is the annotation-only version of the raw lowering.
Clause order and labels come from the shared raw specification. -/
theorem declarative_contract_clauses
    {command : BooleDDM.Command SourceRange} {source : ProcedureMeaning}
    {raw annotated : Core.Procedure} {coreProgram : Core.Program}
    {globals : List Binding} {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    (layout : ProcedureLayout globals source annotated)
    (interpreted : ProcedureWasInterpreted (denotation .builtins) command source)
    (translated : ProcedureWasLowered command raw)
    (typed : Core.TypeSpec.ProcWellTyped coreProgram context scopes annotated)
    (sameSpec : Core.Procedure.Spec.eraseTypes annotated.spec =
      Core.Procedure.Spec.eraseTypes raw.spec) :
    ContractClausesMatch globals source source.contract.requires annotated.spec.preconditions ∧
    ContractClausesMatch globals source source.contract.ensures annotated.spec.postconditions := by
  obtain ⟨preCount, postCount⟩ := lowered_clauseCounts interpreted translated
  have preChecksSame := congrArg
    (fun spec : Core.Procedure.Spec => spec.preconditions.toList) sameSpec
  have postChecksSame := congrArg
    (fun spec : Core.Procedure.Spec => spec.postconditions.toList) sameSpec
  have preLength : annotated.spec.preconditions.toList.length =
      raw.spec.preconditions.toList.length := by
    have equal : annotated.spec.preconditions.toList.map
        (fun (name, check) => (name, Core.Procedure.Check.eraseTypes check)) =
        raw.spec.preconditions.toList.map
        (fun (name, check) => (name, Core.Procedure.Check.eraseTypes check)) := by
      simpa [Core.Procedure.Spec.eraseTypes, ListMap.toList] using preChecksSame
    have count := congrArg List.length equal
    simpa only [List.length_map] using count
  have postLength : annotated.spec.postconditions.toList.length =
      raw.spec.postconditions.toList.length := by
    have equal : annotated.spec.postconditions.toList.map
        (fun (name, check) => (name, Core.Procedure.Check.eraseTypes check)) =
        raw.spec.postconditions.toList.map
        (fun (name, check) => (name, Core.Procedure.Check.eraseTypes check) ) := by
      simpa [Core.Procedure.Spec.eraseTypes, ListMap.toList] using postChecksSame
    have count := congrArg List.length equal
    simpa only [List.length_map] using count
  constructor
  · refine ⟨preCount.trans preLength.symm, fun pair paired state stateTyped => ?_⟩
    exact declarative_clause_truth layout interpreted translated typed sameSpec false pair paired state stateTyped
  · refine ⟨postCount.trans postLength.symm, fun pair paired state stateTyped => ?_⟩
    exact declarative_clause_truth layout interpreted translated typed sameSpec true pair paired state stateTyped

private theorem forall_zip_iff {source : List α} {target : List β}
    {sourceHolds : α → Prop} {targetHolds : β → Prop}
    (length : source.length = target.length)
    (matched : ∀ pair ∈ source.zip target, sourceHolds pair.1 ↔ targetHolds pair.2) :
    (∀ clause ∈ source, sourceHolds clause) ↔ ∀ clause ∈ target, targetHolds clause := by
  induction source generalizing target with
  | nil => cases target <;> simp_all
  | cons clause rest ih =>
    cases target with
    | nil => simp at length
    | cons check tail =>
      have head := matched (clause, check) (by simp)
      have remaining := ih (Nat.succ.inj length)
        (fun pair member => matched pair (List.mem_cons_of_mem _ member))
      simpa only [List.forall_mem_cons] using and_congr head remaining

/-- Pointwise agreement implies agreement of the conjunction of clauses. -/
theorem ContractClausesMatch.holds {globals : List Binding} {procedure : ProcedureMeaning}
    {source : List (Clause Expression)} {target : ListMap String Core.Procedure.Check}
    (matched : ContractClausesMatch globals procedure source target)
    {state : State} (typed : procedureStateWellTyped globals procedure state) :
    (∀ clause ∈ source, clause.holds state) ↔ coreClausesHold target state := by
  exact forall_zip_iff matched.1 (fun pair member => matched.2 pair member state typed)

end Strata.Boole
