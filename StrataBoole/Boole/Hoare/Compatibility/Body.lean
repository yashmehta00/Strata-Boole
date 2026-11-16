/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all StrataBoole.Boole.Hoare.Compile
import all StrataBoole.Boole.Hoare.Compatibility.Expressions
import all StrataBoole.Boole.Semantics.Adequacy.SourceInterface
import all StrataBoole.Boole.Semantics.Adequacy.SourceFreshness
import all Strata.Languages.Core.CmdType
import all Strata.DL.Lambda.LExpr
import all StrataBoole.Boole.Semantics.Adequacy.AssignmentOrigin
import all StrataBoole.Boole.Interp
import all Strata.Languages.Core.Statement
import all Strata.DL.Imperative.Cmd
import all StrataBoole.Boole.Hoare.Rules
import all StrataBoole.Boole.Hoare.Compatibility.Fragment
import all StrataBoole.Boole.Hoare.Compatibility.Transfer
import StrataBoole.Boole.Semantics.Adequacy.ExecutionLowering
import StrataBoole.Boole.Semantics.Adequacy.ExecutionScopes
import all StrataBoole.Boole.Semantics.Adequacy.Execution
import all StrataBoole.Boole.Semantics.Adequacy.ExecutionInvariant
import all Strata.DL.Imperative.Logic.HoareTemplate
import all StrataBoole.Verify

namespace Strata.Boole.Hoare

open StrataDDM Core.TypeSpec Core.Logic Imperative

private def ExtendsLocals (before after : Scope) : Prop :=
  ∃ added, after = {before with locals := before.locals ++ added}

private theorem ExtendsLocals.refl (scope : Scope) : ExtendsLocals scope scope := by
  exact ⟨[], by cases scope; simp⟩

private theorem ExtendsLocals.trans {before middle after : Scope}
    (first : ExtendsLocals before middle) (second : ExtendsLocals middle after) :
    ExtendsLocals before after := by
  obtain ⟨earlier, rfl⟩ := first
  obtain ⟨later, rfl⟩ := second
  exact ⟨earlier ++ later, by simp [List.append_assoc]⟩

private def PreservesScope (action : InterpM α) : Prop :=
  ∀ before value after, action before = .ok (value, after) → ExtendsLocals before after

private theorem readOnly_preservesScope {action : InterpM α} (keeps : ReadOnly action) :
    PreservesScope action := by
  intro before value after run
  obtain rfl := keeps _ _ _ run
  exact ExtendsLocals.refl _

private theorem PreservesScope.bind {first : InterpM α} {next : α → InterpM β}
    (head : PreservesScope first) (tail : ∀ x, PreservesScope (next x)) :
    PreservesScope (first >>= next) := by
  intro before value after run
  obtain ⟨x, middle, firstRun, nextRun⟩ := split_run run
  exact (head _ _ _ firstRun).trans (tail _ _ _ _ nextRun)

private theorem PreservesScope.forIn (xs : List α) (init : β)
    (step : α → β → InterpM (ForInStep β))
    (keeps : ∀ x acc, PreservesScope (step x acc)) :
    PreservesScope (forIn xs init step) := by
  induction xs generalizing init with
  | nil => exact readOnly_preservesScope (readOnly_pure _)
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply PreservesScope.bind (keeps x init)
    intro control
    cases control
    · exact readOnly_preservesScope (readOnly_pure _)
    · exact ih _

private theorem addLocal_preservesScope (range : SourceRange) (name : String) (ty : Boole.Type) :
    PreservesScope (addLocal range name ty) := by
  intro before binding after success
  unfold addLocal at success
  obtain ⟨sort, middle, sorted, rest⟩ := split_run success
  have same := sourceSort_readOnly _ _ _ _ sorted
  subst middle
  obtain ⟨_, next, freshRun, added⟩ := split_run rest
  obtain ⟨_, _, same⟩ := fresh_names freshRun
  subst next
  exact ⟨[_], (congrArg Prod.snd (Except.ok.inj added)).symm⟩

private theorem boolean_readOnly (range : SourceRange) (e : Boole.Expr)
    (context : ReadContext) : ReadOnly (boolean range e context) :=
  (expr_readOnly e context).bind fun value => expect_readOnly value .bool range

private theorem guardExpr_readOnly (guard : BooleDDM.ExprOrNondet SourceRange) :
    ReadOnly (guardExpr guard) := by
  cases guard
  · exact ReadOnly.map some (boolean_readOnly _ _ _)
  · exact readOnly_pure _

private theorem measureExpr_readOnly (measure : Option (BooleDDM.Measure SourceRange)) :
    ReadOnly (measureExpr measure) := by
  cases measure
  · exact readOnly_pure _
  · rename_i measure
    cases measure
    exact (expr_readOnly _ _).bind fun value =>
      (expect_readOnly value .int _).bind fun result => readOnly_pure (some result)

private theorem invariants_readOnly (invs : BooleDDM.Invariants SourceRange) :
    ReadOnly (invariants invs) := by
  induction invs with
  | nilInvariants => exact readOnly_pure _
  | consInvariants _ _ expression rest ih =>
    rw [invariants]
    exact (boolean_readOnly _ expression _).bind fun _ => ih.bind fun _ => readOnly_pure _

private theorem writable_readOnly (readOnly : List String) (range : SourceRange) (name : String) :
    ReadOnly (writable readOnly range name) := by
  unfold writable
  split
  · exact (readOnly_reject _ _).bind fun _ => resolveVariable_readOnly _ _ _
  · exact resolveVariable_readOnly _ _ _

private theorem block_readOnly (body : BooleDDM.Block SourceRange) (readOnly : List String) :
    ReadOnly (block body readOnly) := by
  rw [block.eq_def]
  exact fun _ _ _ run => withScope_restores run

private theorem statement_preservesScope
    (statement : BooleDDM.Statement SourceRange) (readOnly : List String) :
    PreservesScope (stmt statement readOnly) := by
  cases statement
  case' assign _ _ _ lhs _ => cases lhs
  case' if_statement _ _ _ _ otherwise => cases otherwise
  all_goals rw [stmt.eq_def]
  all_goals
    repeat' first
      | exact readOnly_preservesScope (readOnly_pure _)
      | exact readOnly_preservesScope (readOnly_reject _ _)
      | exact readOnly_preservesScope readOnly_get
      | exact readOnly_preservesScope (expr_readOnly _ _)
      | exact readOnly_preservesScope (expect_readOnly _ _ _)
      | exact readOnly_preservesScope (boolean_readOnly _ _ _)
      | exact readOnly_preservesScope (guardExpr_readOnly _)
      | exact readOnly_preservesScope (measureExpr_readOnly _)
      | exact readOnly_preservesScope (invariants_readOnly _)
      | exact readOnly_preservesScope (writable_readOnly _ _ _)
      | exact readOnly_preservesScope (block_readOnly _ _)
      | exact readOnly_preservesScope (fun _ _ _ run => withScope_restores run)
      | exact addLocal_preservesScope _ _ _
      | apply PreservesScope.forIn
      | apply PreservesScope.bind
      | dsimp only
      | split
      | intro

private theorem statements_extend_locals
    (statements : List (BooleDDM.Statement SourceRange)) (readOnly : List String) :
    PreservesScope (stmts statements readOnly) := by
  induction statements with
  | nil =>
    rw [stmts.eq_def]
    exact readOnly_preservesScope (readOnly_pure _)
  | cons head rest ih =>
    cases rest
    · rw [stmts.eq_def]
      exact statement_preservesScope head readOnly
    · rw [stmts.eq_def]
      exact (statement_preservesScope head readOnly).bind fun first =>
        ih.bind fun second => readOnly_preservesScope (readOnly_pure (first.seq second))

/-- The source, raw, and checked scopes at one statement boundary. -/
private structure CompilerScopes where
  source : Scope
  lowering : TranslateState
  context : Core.Expression.TyContext
  variables : TypeScopes

/-- The lexical invariant shared by the statement and expression proofs. -/
private structure ScopesAgree (scopes : CompilerScopes) : Prop where
  names : scopes.source.names = scopes.lowering.gctx
  binders : scopes.lowering.bvars = scopes.source.locals.toArray.map
    (fun binding => (.fvar () ⟨binding.name, ()⟩ none : Core.Expression.Expr))
  globals : ∀ binding ∈ scopes.source.globals,
    scopes.lowering.globalVarTypes.contains binding.name = true
  modifies : ∀ name, name ∈ scopes.source.modifies ↔ name ∈ scopes.lowering.currentInoutNames
  distinct : ((scopes.source.locals ++ scopes.source.globals).map Binding.name).Nodup
  validNames : ∀ binding ∈ scopes.source.locals ++ scopes.source.globals,
    binding.name.contains ' ' = false
  builtins : ∀ fn : Lambda.LFunc Core.CoreLParams, Core.Factory[fn.name.name]? = some fn →
    scopes.context.functions[fn.name.name]? = some fn

private abbrev BodyRelation :=
  Scope → List Core.CoreIdent → State → Env Core.Expression → Prop

private def BodyTransfer (program : Core.Program) (params : InitEnvWFParams)
    (factory : Lambda.Factory Core.CoreLParams) (related : BodyRelation)
    (entry final : Scope) (unwritten remaining : List Core.CoreIdent)
    (command : Transformer) (statements : Core.Statements) : Prop :=
  ∀ Q : Control → Assertion, Core.Logic.Hoare.Triple program.findProcByString? params
    (Lift (related entry unwritten) (command.transform Q))
    statements (Lift (related final remaining) (Q none)) (factory := factory)

private def StatementTransfer (program : Core.Program) (params : InitEnvWFParams)
    (factory : Lambda.Factory Core.CoreLParams) (related : BodyRelation)
    (paired : CompilerScopes → Prop) (readOnly labels : List String) : Prop :=
  ∀ (source : BooleDDM.Statement SourceRange) (entry final : CompilerScopes)
    (compiled : Compiled) (raw annotated : Core.Statements)
    (unwritten remaining : List Core.CoreIdent),
    stmt source readOnly entry.source = .ok (compiled, final.source) →
    lowerStatementChunk source entry.lowering = .ok (raw, final.lowering) →
    eraseStatementsAnnotations annotated = eraseStatementsAnnotations raw →
    StatementsWellTyped program entry.context entry.variables labels
      annotated final.context final.variables →
    coreStatements annotated unwritten = some remaining →
    paired entry →
    paired final ∧ BodyTransfer program params factory related entry.source final.source
      unwritten remaining compiled.command annotated

/-- Compose the per-statement proof along the actual compiler runs.
Split the typed Core list at exactly the boundaries of the raw chunks. -/
private theorem compiled_statements_transfer
    (program : Core.Program) (params : InitEnvWFParams)
    (factory : Lambda.Factory Core.CoreLParams) (related : BodyRelation)
    (paired : CompilerScopes → Prop) (readOnly labels : List String)
    (scopeEquiv : ∀ entry other, Strata.Util.HMaps.Equiv other entry.variables →
      paired entry → paired {entry with variables := other})
    (headTransfer : StatementTransfer program params factory related paired readOnly labels)
    (source : List (BooleDDM.Statement SourceRange))
    {entry final : CompilerScopes} {compiled : Compiled}
    {chunks : List (List Core.Statement)} {annotated : Core.Statements}
    {unwritten remaining : List Core.CoreIdent}
    (built : stmts source readOnly entry.source = .ok (compiled, final.source))
    (lowered : source.mapM lowerStatementChunk entry.lowering = .ok (chunks, final.lowering))
    (erased : eraseStatementsAnnotations annotated = eraseStatementsAnnotations chunks.flatten)
    (typed : StatementsWellTyped program entry.context entry.variables labels
      annotated final.context final.variables)
    (supported : coreStatements annotated unwritten = some remaining)
    (aligned : paired entry) :
    paired final ∧ BodyTransfer program params factory related entry.source final.source
      unwritten remaining compiled.command annotated := by
  induction source generalizing entry final compiled chunks annotated unwritten remaining with
  | nil =>
    cases entry with | mk sourceEntry rawEntry context vars =>
    cases final with | mk sourceFinal rawFinal next nextVars =>
    simp only [stmts, pure, StateT.pure, Except.pure] at built
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj built)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj lowered)
    cases annotated with
    | cons stmt rest => simp [eraseStatementsAnnotations] at erased
    | nil =>
      cases typed with
      | nil _ _ _ _ equiv =>
        have same : unwritten = remaining := Option.some.inj (by simpa [coreStatements] using supported)
        subst remaining
        refine ⟨scopeEquiv _ _ equiv aligned, fun Q => ?_⟩
        exact Imperative.Logic.Hoare.skip_block (Core.EvalCommandE program.findProcByString?)
          BlockInitEnvWF params (Lift (related sourceEntry unwritten) (Q none))
  | cons first rest ih =>
    obtain ⟨rawHead, rawMiddle, rawTail, headLowered, tailLowered, rfl⟩ :=
      mapM_lowerStatementChunk_cons first rest entry.lowering final.lowering chunks lowered
    cases rest with
    | nil =>
      obtain ⟨rfl, rawSame⟩ := Prod.mk.inj (Except.ok.inj tailLowered)
      exact headTransfer first entry final compiled rawHead annotated unwritten remaining
        (by simpa [stmts] using built) (by simpa [rawSame] using headLowered)
        (by simpa using erased) typed supported aligned
    | cons second rest =>
      rw [stmts.eq_def] at built
      simp only [bind, StateT.bind, Except.bind] at built
      cases headBuilt : stmt first readOnly entry.source with
      | error error => simp [headBuilt] at built
      | ok result =>
        obtain ⟨head, sourceMiddle⟩ := result
        cases tailBuilt : stmts (second :: rest) readOnly sourceMiddle with
        | error error => simp [headBuilt, tailBuilt] at built
        | ok output =>
          obtain ⟨tail, sourceEnd⟩ := output
          simp only [headBuilt, tailBuilt, pure, StateT.pure, Except.pure] at built
          obtain ⟨rfl, sourceSame⟩ := Prod.mk.inj (Except.ok.inj built)
          rw [List.flatten_cons, eraseStatements_append] at erased
          obtain ⟨headEq, tailEq⟩ := statementsEraseTypes_take_drop erased rawHead.length
          rw [← eraseStatements_length rawHead, List.take_left] at headEq
          rw [← eraseStatements_length rawHead, List.drop_left] at tailEq
          simp only [eraseStatements_length] at headEq tailEq
          rw [← List.take_append_drop rawHead.length annotated] at typed supported ⊢
          obtain ⟨middleContext, middleVars, headTyped, tailTyped⟩ :=
            statementsWellTyped_append_split typed
          rw [coreStatements_append] at supported
          cases headGate : coreStatements (annotated.take rawHead.length) unwritten with
          | none => simp [headGate, Option.bind] at supported
          | some afterHead =>
            have tailGate : coreStatements (annotated.drop rawHead.length) afterHead = some remaining := by
              simpa [headGate, Option.bind] using supported
            let middle : CompilerScopes := ⟨sourceMiddle, rawMiddle, middleContext, middleVars⟩
            obtain ⟨pairedMiddle, headTriple⟩ := headTransfer first entry middle head rawHead _
              unwritten afterHead headBuilt headLowered headEq headTyped headGate aligned
            obtain ⟨pairedFinal, tailTriple⟩ := ih (entry := middle) (final := final) (compiled := tail)
              (by simpa [middle, sourceSame] using tailBuilt) tailLowered tailEq
              tailTyped tailGate pairedMiddle
            have closed := coreStatements_closed _ _ _ headGate
            refine ⟨pairedFinal, fun Q => ?_⟩
            exact Core.Logic.Hoare.seq program.findProcByString? params
              (headTriple (fun
                | none => tail.command.transform Q
                | some label => Q (some label))) (tailTriple Q) closed

private theorem declared_of_lookup {bindings : List Binding} {store : Store}
    (typed : SourceSlotsTyped bindings store) {name : String} {value : Value}
    (lookup : store.lookup name = some value) :
    ∃ binding ∈ bindings, binding.name = name := by
  have slot := typed name
  cases found : bindings.find? (fun b => b.name == name) with
  | none => simp [lookup, found] at slot
  | some binding =>
    exact ⟨binding, List.mem_of_find?_eq_some found, beq_iff_eq.mp (List.find?_some (p := fun b : Binding => b.name == name) found)⟩

private theorem compiled_assignment
    {range lhsRange : SourceRange} {annotations other}
    {name : Ann String SourceRange} {expression : Boole.Expr}
    {scope final : Scope} {compiled : Compiled} {readOnly : List String}
    (run : stmt (.assign range annotations other (.lhsIdent lhsRange name) expression)
      readOnly scope = .ok (compiled, final)) :
    ∃ slot value, expr expression {} scope = .ok (value, scope) ∧
      final = scope ∧ compiled.command = Transformer.step (Transformer.assignState slot value.eval) ∧
      coreIdent slot = ⟨name.val, ()⟩ ∧
      (match slot with
       | .local n => ∃ binding, findBinding n scope.locals = some binding
       | .global n => findBinding n scope.locals = none ∧
           ∃ binding, findBinding n scope.globals = some binding) := by
  rw [stmt.eq_def] at run
  obtain ⟨⟨slot, sort⟩, next, resolved, rest⟩ := split_run run
  unfold writable at resolved
  by_cases immutable : readOnly.contains name.val = true
  · simp only [immutable, ite_true] at resolved
    obtain ⟨_, _, denied, _⟩ := split_run resolved
    contradiction
  · simp only [ite_eq_right immutable] at resolved
    have ⟨stateEq, named⟩ := resolveWriting_name range name.val scope next slot sort resolved
    subst next
    obtain ⟨value, mid, compiledExpr, rest⟩ := split_run rest
    have same := expr_readOnly _ _ _ _ _ compiledExpr
    subst mid
    obtain ⟨rhs, endScope, expected, done⟩ := split_run rest
    unfold TypedExpr.expect at expected
    split at expected
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj expected)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj done)
      refine ⟨slot, value, compiledExpr, rfl, rfl, by cases slot <;> exact named, ?_⟩
      unfold resolveVariable at resolved
      simp only [bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, Except.pure, Bool.true_and] at resolved
      cases localSlot : findBinding name.val scope.locals with
      | some binding =>
        rw [localSlot] at resolved
        obtain ⟨values, _⟩ := Prod.mk.inj (Except.ok.inj resolved)
        obtain ⟨rfl, _⟩ := Prod.mk.inj values
        exact ⟨binding, localSlot⟩
      | none =>
        cases globalSlot : findBinding name.val scope.globals with
        | none => simp [localSlot, globalSlot, reject, throw, throwThe, MonadExceptOf.throw,
            StateT.lift, Functor.map, Except.map] at resolved
        | some binding =>
          simp only [localSlot, globalSlot] at resolved
          split at resolved
          · obtain ⟨_, _, denied, _⟩ := split_run resolved
            contradiction
          · obtain ⟨values, _⟩ := Prod.mk.inj (Except.ok.inj resolved)
            obtain ⟨rfl, _⟩ := Prod.mk.inj values
            exact ⟨localSlot, binding, globalSlot⟩
    · contradiction

private theorem find_local_by_name {locals : List Binding} {binding : Binding}
    (distinct : (locals.map Binding.name).Nodup) (present : binding ∈ locals) :
    findBinding binding.name locals = some binding := by
  induction locals with
  | nil => simp at present
  | cons first rest ih =>
    rcases List.mem_cons.mp present with rfl | later
    · simp [findBinding]
    · have distinct := List.nodup_cons.mp (by simpa only [List.map_cons] using distinct :
        (first.name :: rest.map Binding.name).Nodup)
      have other : first.name ≠ binding.name := by
        intro same
        exact distinct.1 (same ▸ List.mem_map_of_mem later)
      have found := ih distinct.2 later
      simpa [findBinding, other] using found

private theorem bound_rhs_agrees
    {entry : CompilerScopes} {after : TranslateState} {factory unwritten}
    {range : SourceRange} {index : Nat} {value : TypedExpr} {raw target : Core.Expression.Expr}
    (aligned : ScopesAgree entry)
    (built : expr (.bvar range index) {} entry.source = .ok (value, entry.source))
    (lowered : toCoreExpr (.bvar range index) entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (readable : ready unwritten target = true) :
    after = entry.lowering ∧
      ExprAgrees (ScopedStoresAgree entry.source factory unwritten) value.eval target ∧
      ∀ state, StateFits entry.source state →
        ∃ result, result.sort = value.sort ∧ value.eval state = .ok result := by
  cases found : entry.source.locals.reverse[index]? with
  | none =>
      rw [expr.eq_def] at built
      simp [found, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
        reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, pure, Except.pure] at built
  | some binding =>
      have rawShape := (lowerLocalRead (checkingInterpretation (fun _ => true)) entry.source
        entry.lowering range index binding aligned.binders found).2
      have same := ExpressionWasLowered.unique ⟨after, lowered⟩ rawShape
      have readableName : coreIdent (.local binding.name) ∉ unwritten := by
        rw [same] at erased
        cases target <;> simp [Lambda.LExpr.eraseTypes] at erased
        case fvar md id annotation =>
          cases md
          subst id
          simpa [ready, Core.CmdType.freeVars, Lambda.LExpr.freeVars, coreIdent] using readable
      have stable : after = entry.lowering := by
        have bounded : index < entry.source.locals.length := by
          simpa using (List.getElem?_eq_some_iff.mp found).1
        have atIndex : entry.lowering.bvars[entry.lowering.bvars.size - index - 1]? =
            some (.fvar () ⟨binding.name, ()⟩ none) := by
          rw [aligned.binders]
          simp only [Array.size_map, List.size_toArray, Array.getElem?_map, List.getElem?_toArray]
          have position : entry.source.locals.length - index - 1 =
              entry.source.locals.length - 1 - index := by omega
          rw [position, ← List.getElem?_reverse bounded, found]
          rfl
        have below : index < entry.lowering.bvars.size := by
          simpa [aligned.binders] using bounded
        rw [toCoreExpr.eq_def] at lowered
        simp only [toCoreQuantExpr?, getBVarExpr, bind, StateT.bind, Except.bind,
          get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure] at lowered
        simp [below, atIndex, StateT.pure] at lowered
        exact (congrArg Prod.snd (Except.ok.inj lowered)).symm
      have distinct : (entry.source.locals.map Binding.name).Nodup :=
        (List.nodup_append.mp (by simpa only [List.map_append] using aligned.distinct :
          (entry.source.locals.map Binding.name ++ entry.source.globals.map Binding.name).Nodup)).1
      have present := List.mem_reverse.mp (List.mem_of_getElem? found)
      obtain ⟨_, total, agrees⟩ := local_read_agrees (factory := factory) (unwritten := unwritten)
        aligned.binders found (find_local_by_name distinct present) readableName built ⟨after, lowered⟩ erased
      exact ⟨stable, agrees, total⟩

private theorem global_rhs_agrees
    {entry : CompilerScopes} {after : TranslateState} {factory unwritten}
    {range : SourceRange} {index : Nat} {value : TypedExpr} {raw target : Core.Expression.Expr}
    (aligned : ScopesAgree entry)
    (built : expr (.fvar range index) {} entry.source = .ok (value, entry.source))
    (lowered : toCoreExpr (.fvar range index) entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (readable : ready unwritten target = true) :
    after = entry.lowering ∧
      ExprAgrees (ScopedStoresAgree entry.source factory unwritten) value.eval target ∧
      ∀ state, StateFits entry.source state →
        ∃ result, result.sort = value.sort ∧ value.eval state = .ok result := by
  cases resolves : entry.source.names.nameOf? index with
  | none =>
    rw [expr.eq_def] at built
    simp [resolves, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
      reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, pure, Except.pure] at built
  | some name =>
    cases found : findBinding name entry.source.globals with
    | none =>
      rw [expr.eq_def] at built
      simp [resolves, found, bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
        reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, pure, Except.pure] at built
    | some binding =>
      have sameName := beq_iff_eq.mp
        (List.find?_some (p := fun b : Binding => b.name == name) found)
      have registered : entry.lowering.globalVarTypes.contains name = true := by
        rw [← sameName]
        exact aligned.globals binding (List.mem_of_find?_eq_some found)
      have rawShape := (lowerGlobalRead (checkingInterpretation (fun _ => true))
        entry.source entry.lowering range index name binding aligned.names resolves found registered).2
      have same := ExpressionWasLowered.unique ⟨after, lowered⟩ rawShape
      have readableName : coreIdent (.global name) ∉ unwritten := by
        rw [same] at erased
        cases target <;> simp [Lambda.LExpr.eraseTypes] at erased
        case fvar md ident annotation =>
          cases md
          subst ident
          simpa [ready, Core.CmdType.freeVars, Lambda.LExpr.freeVars, coreIdent] using readable
      have stable : after = entry.lowering := by
        have rawName : entry.lowering.gctx.nameOf? index = some name := aligned.names ▸ resolves
        have classified : getFVarIsOp range index entry.lowering = .ok (false, entry.lowering) := by
          cases found : entry.lowering.gctx.vars[index]? with
          | none => simp [GlobalContext.nameOf?, found] at rawName
          | some entryAtIndex =>
            obtain ⟨key, kind⟩ := entryAtIndex
            have nameEq : key = name := by simpa [GlobalContext.nameOf?, found] using rawName
            subst key
            cases kind <;> simp [getFVarIsOp, TranslateState.isGlobalVar, found, registered, bind,
              StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure]
        rw [toCoreExpr.eq_def] at lowered
        simp only [toCoreQuantExpr?, getFVarName, rawName, classified, mkIdent,
          bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
          pure, StateT.pure, Except.pure] at lowered
        exact (congrArg Prod.snd (Except.ok.inj lowered)).symm
      obtain ⟨_, total, agrees⟩ := global_read_agrees (factory := factory) (unwritten := unwritten)
        rfl aligned.names resolves found registered readableName built ⟨after, lowered⟩ erased
      exact ⟨stable, agrees, total⟩

private def isScalarLeaf : Boole.Expr → Prop
  | .bvar .. | .fvar .. => True
  | expression => isScalarLiteral expression

private theorem integer_leaf_agrees
    {entry : CompilerScopes} {after : TranslateState} {factory unwritten}
    {expression : Boole.Expr} {value : TypedExpr} {raw target : Core.Expression.Expr}
    (leaf : isScalarLeaf expression) (aligned : ScopesAgree entry)
    (built : expr expression {} entry.source = .ok (value, entry.source))
    (lowered : toCoreExpr expression entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (readable : ready unwritten target = true) (integer : value.sort = .int) :
    after = entry.lowering ∧
      ∀ state env, ScopedStoresAgree entry.source factory unwritten state env →
        ∃ n : Int, value.eval state = .ok (.int n) ∧
          Core.Expression.eval env.factory env.store target = some (.ofInt env.factory.model.tcInterp n) := by
  obtain ⟨stable, agrees, total⟩ :
      after = entry.lowering ∧
        ExprAgrees (ScopedStoresAgree entry.source factory unwritten) value.eval target ∧
        ∀ state, StateFits entry.source state →
          ∃ result, result.sort = value.sort ∧ value.eval state = .ok result := by
    by_cases literal : isScalarLiteral expression
    · obtain ⟨result, sort, evaluated, agrees⟩ := literal_agrees literal built
        ⟨_, lowered⟩ erased (ScopedStoresAgree entry.source factory unwritten)
      exact ⟨literal_lowering_unchanged literal lowered, agrees,
        fun state _ => ⟨result, sort.symm, evaluated state⟩⟩
    · cases expression <;> try solve | exact False.elim (literal leaf)
      case bvar => exact bound_rhs_agrees aligned built lowered erased readable
      case fvar => exact global_rhs_agrees aligned built lowered erased readable
  refine ⟨stable, ?_⟩
  intro state env related
  obtain ⟨⟨sort, payload⟩, same, evaluated⟩ := total state related.2
  have intSort : sort = .int := same.trans integer
  subst sort
  obtain ⟨v, encoded, evaluates⟩ := agrees state env _ related evaluated
  obtain rfl := Option.some.inj encoded
  exact ⟨payload, evaluated, evaluates⟩

private inductive IntegerSum : Boole.Expr → Prop where
  | leaf {expression} : isScalarLeaf expression → IntegerSum expression
  | add (range typeRange : SourceRange) {left right} :
      IntegerSum left → IntegerSum right → IntegerSum (.add_expr range (.int typeRange) left right)

private theorem integer_sum_agrees
    {entry : CompilerScopes} {after : TranslateState} {factory unwritten}
    {expression : Boole.Expr} {value : TypedExpr} {raw target : Core.Expression.Expr}
    {ty : Lambda.LMonoTy}
    (supported : IntegerSum expression) (aligned : ScopesAgree entry)
    (ambient : factory["Int.Add"]? = some (Lambda.intAddFunc (T := Core.CoreLParams)).func)
    (built : expr expression {} entry.source = .ok (value, entry.source))
    (lowered : toCoreExpr expression entry.lowering = .ok (raw, after))
    (erased : target.eraseTypes = raw.eraseTypes)
    (typed : ExprWellTyped entry.context entry.variables target ty)
    (readable : ready unwritten target = true) (integer : value.sort = .int) :
    after = entry.lowering ∧
      ∀ state env, ScopedStoresAgree entry.source factory unwritten state env →
        ∃ n : Int, value.eval state = .ok (.int n) ∧
          Core.Expression.eval env.factory env.store target = some (.ofInt env.factory.model.tcInterp n) := by
  induction supported generalizing entry after value raw target ty with
  | leaf leaf => exact integer_leaf_agrees leaf aligned built lowered erased readable integer
  | add _ _ _ _ leftIH rightIH =>
    apply int_add_agrees built lowered erased typed readable
      (aligned.builtins (Lambda.intAddFunc (T := Core.CoreLParams)).func Core.coreFactory_intAdd)
      ambient
    intro lhs rhs middle lhsRaw rhsRaw lhsTarget rhsTarget lhsBuilt rhsBuilt
      lhsSort rhsSort lhsLowered rhsLowered lhsErased rhsErased lhsType rhsType lhsRead rhsRead
    obtain ⟨rfl, evalLeft⟩ := leftIH aligned lhsBuilt lhsLowered lhsErased lhsType lhsRead lhsSort
    obtain ⟨stable, evalRight⟩ := rightIH aligned rhsBuilt rhsLowered rhsErased rhsType rhsRead rhsSort
    refine ⟨stable, ?_⟩
    intro state env related
    obtain ⟨a, sourceLeft, targetLeft⟩ := evalLeft state env related
    obtain ⟨b, sourceRight, targetRight⟩ := evalRight state env related
    exact ⟨a, b, sourceLeft, sourceRight, targetLeft, targetRight⟩

/-- Pair the two translations of a plain assignment. The only expression
obligation is the correspondence for the actual RHS. -/
private theorem assignment_transfer
    {program : Core.Program} {params : InitEnvWFParams} {factory : Lambda.Factory Core.CoreLParams}
    {range lhsRange : SourceRange} {annotations other}
    {name : Ann String SourceRange} {expression : Boole.Expr}
    {entry final : CompilerScopes} {compiled : Compiled} {readOnly labels : List String}
    {raw annotated : Core.Statements} {unwritten remaining : List Core.CoreIdent}
    (built : stmt (.assign range annotations other (.lhsIdent lhsRange name) expression)
      readOnly entry.source = .ok (compiled, final.source))
    (lowered : lowerStatementChunk (.assign range annotations other (.lhsIdent lhsRange name) expression)
      entry.lowering = .ok (raw, final.lowering))
    (erased : eraseStatementsAnnotations annotated = eraseStatementsAnnotations raw)
    (typed : StatementsWellTyped program entry.context entry.variables labels
      annotated final.context final.variables)
    (gate : coreStatements annotated unwritten = some remaining)
    (aligned : ScopesAgree entry)
    (rhs : ∀ value rawExpr target ty,
      expr expression {} entry.source = .ok (value, entry.source) →
      toCoreExpr expression entry.lowering = .ok (rawExpr, final.lowering) →
      target.eraseTypes = rawExpr.eraseTypes →
      ExprWellTyped entry.context entry.variables target ty →
      ready unwritten target = true →
      final.lowering = entry.lowering ∧
      ExprAgrees (ScopedStoresAgree entry.source factory unwritten) value.eval target) :
    ScopesAgree final ∧
      BodyTransfer program params factory (fun scope unwritten => ScopedStoresAgree scope factory unwritten)
        entry.source final.source unwritten remaining compiled.command annotated := by
  obtain ⟨slot, value, sourceExpr, sourceScope, sourceBody, named, resolves⟩ :=
    compiled_assignment built
  have nameValid : (coreIdent slot).name.contains ' ' = false := by
    cases slot with
    | «local» n =>
        obtain ⟨binding, found⟩ := resolves
        have same := beq_iff_eq.mp (List.find?_some (p := fun b : Binding => b.name == n) found)
        change n.contains ' ' = false
        rw [← same]
        exact aligned.validNames _ (List.mem_append_left _ (List.mem_of_find?_eq_some found))
    | global n =>
        obtain ⟨_, binding, found⟩ := resolves
        have same := beq_iff_eq.mp (List.find?_some (p := fun b : Binding => b.name == n) found)
        change n.contains ' ' = false
        rw [← same]
        exact aligned.validNames _ (List.mem_append_right _ (List.mem_of_find?_eq_some found))
  have unshadowed : ∀ state, StateFits entry.source state → SlotUnshadowed state slot := by
    intro state fits
    cases slot with
    | «local» n =>
        change state.globals.lookup n = none
        cases read : state.globals.lookup n with
        | none => rfl
        | some previous =>
          exfalso
          obtain ⟨globalBinding, globalMember, globalName⟩ := declared_of_lookup fits.globals read
          obtain ⟨localBinding, localFound⟩ := resolves
          have localName := beq_iff_eq.mp
            (List.find?_some (p := fun b : Binding => b.name == n) localFound)
          have both := List.nodup_append.mp (by simpa [List.map_append] using aligned.distinct :
            (entry.source.locals.map Binding.name ++ entry.source.globals.map Binding.name).Nodup)
          have inLocal : n ∈ entry.source.locals.map Binding.name :=
            List.mem_map.mpr ⟨_, List.mem_of_find?_eq_some localFound, localName⟩
          have inGlobal : n ∈ entry.source.globals.map Binding.name :=
            List.mem_map.mpr ⟨_, globalMember, globalName⟩
          exact both.2.2 n inLocal n inGlobal rfl
    | global n =>
        have lookup := fits.locals n
        change (state.locals.lookup n).map Value.sort =
          (findBinding n entry.source.locals).map Binding.sort at lookup
        rw [resolves.1] at lookup
        cases answer : state.locals.lookup n <;> simp_all [SlotUnshadowed]
  simp only [lowerStatementChunk] at lowered
  rw [toCoreStmt, toCoreStmt.lhsParts] at lowered
  simp only [bind, StateT.bind, Except.bind, StateT.pure, Except.pure, pure] at lowered
  cases rhsRun : toCoreExpr expression entry.lowering with
  | error => simp [rhsRun] at lowered
  | ok result =>
    obtain ⟨rawExpr, afterExpr⟩ := result
    simp only [rhsRun, toCoreMetaData, get, getThe, MonadStateOf.get, StateT.get,
      bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at lowered
    obtain ⟨rfl, rawFinal⟩ := Prod.mk.inj (Except.ok.inj lowered)
    cases annotated with
    | nil => simp [eraseStatementsAnnotations] at erased
    | cons head rest =>
      cases rest with
      | cons next rest => simp [eraseStatementsAnnotations] at erased
      | nil =>
        have headEq := (List.cons.inj erased).1
        cases head <;> simp [eraseStatementAnnotations] at headEq
        case cmd cmd =>
          cases cmd <;> simp [Core.Command.eraseTypes] at headEq
          case cmd primitive =>
            cases primitive <;> simp at headEq
            case set id initializer md =>
              cases initializer <;> simp [Imperative.ExprOrNondet.map] at headEq
              case det target =>
                obtain ⟨rfl, sameExpr, _⟩ := headEq
                simp only [nestMapSet] at sameExpr
                have gateResult : ready unwritten target = true ∧
                    unwritten.filter (· != ⟨name.val, ()⟩) = remaining := by
                  by_cases readOK : ready unwritten target = true <;>
                    simp [coreStatements, coreStatement, readOK, bind, Option.bind] at gate
                  exact ⟨readOK, gate⟩
                cases typed with
                | cons _ _ _ _ _ _ _ _ _ headTyped tailTyped =>
                  cases headTyped with
                  | cmd _ _ _ _ _ cmdTyped =>
                    cases cmdTyped with
                    | cmd _ _ primitiveTyped =>
                      cases primitiveTyped with
                      | set_det =>
                        rename_i expressionTyped _
                        have finalContext : final.context = entry.context := by
                          generalize final.context = ctx at tailTyped ⊢
                          cases tailTyped
                          rfl
                        obtain ⟨rawScope, agrees⟩ := rhs value rawExpr target _ sourceExpr
                          (rawFinal ▸ rhsRun) sameExpr expressionTyped gateResult.1
                        refine ⟨?_, ?_⟩
                        · constructor
                          · simpa only [sourceScope, rawScope] using aligned.names
                          · simpa only [sourceScope, rawScope] using aligned.binders
                          · simpa only [sourceScope, rawScope] using aligned.globals
                          · simpa only [sourceScope, rawScope] using aligned.modifies
                          · simpa only [sourceScope] using aligned.distinct
                          · simpa only [sourceScope] using aligned.validNames
                          · simpa only [finalContext] using aligned.builtins
                        · intro Q
                          rw [sourceBody, sourceScope, ← gateResult.2]
                          have result := transfer_scalar_assign (π := program.findProcByString?)
                            (params := params) unwritten slot value.eval target md (Q none)
                            entry.source agrees unshadowed nameValid
                          simpa only [Transformer.step, named, mkIdent, Core.Statement.set] using result

/-- A scoped assertion survives Core's block projection when the block
declares none of the scope's visible names or snapshots. -/
private theorem scoped_postWF {factory unwritten} {scope : Scope} {statements : Core.Statements}
    (keep : ∀ binding ∈ scope.globals ++ scope.locals,
      (⟨binding.name, ()⟩ : Core.CoreIdent) ∉ Imperative.Block.definedVars statements true)
    (keepOld : ∀ name ∈ scope.modifies,
      Core.CoreIdent.mkOld name ∉ Imperative.Block.definedVars statements true)
    (Q : Assertion) :
    Imperative.Logic.Hoare.PostWF statements (Lift (ScopedStoresAgree scope factory unwritten) Q) := by
  rintro env ⟨state, ⟨agrees, fits⟩, holds⟩
  refine ⟨state, ⟨?_, fits⟩, holds⟩
  have projected := agrees.restrictLocals_dropVars state.locals
    (Imperative.Block.definedVars statements true) ?_ ?_ ?_
  · simpa only [restrict_self] using projected
  · intro name value found
    obtain ⟨binding, member, rfl⟩ := declared_of_lookup fits.globals found
    exact keep binding (List.mem_append_left _ member)
  · intro name present
    obtain ⟨value, found⟩ := Option.isSome_iff_exists.mp present
    obtain ⟨binding, member, rfl⟩ := declared_of_lookup fits.locals found
    exact keep binding (List.mem_append_right _ member)
  · intro name value found
    obtain ⟨binding, member, rfl⟩ := declared_of_lookup fits.snapshots found
    exact keepOld _ (List.contains_iff_mem.mp (List.mem_filter.mp member).2)

private theorem transfer_scoped_body
    {program : Core.Program} {params : InitEnvWFParams}
    {factory : Lambda.Factory Core.CoreLParams} {scope : Scope} {inner : List Binding}
    {unwritten remaining : List Core.CoreIdent} {body : Transformer}
    {statements : Core.Statements}
    (inside : BodyTransfer program params factory
      (fun scope unwritten => ScopedStoresAgree scope factory unwritten)
      scope {scope with locals := inner} unwritten remaining body statements)
    (visible : ∀ name binding, scope.locals.find? (fun b => b.name == name) = some binding →
      inner.find? (fun b => b.name == name) = some binding)
    (keep : ∀ binding ∈ scope.globals ++ scope.locals,
      (⟨binding.name, ()⟩ : Core.CoreIdent) ∉ Imperative.Block.definedVars statements true)
    (keepOld : ∀ name ∈ scope.modifies,
      Core.CoreIdent.mkOld name ∉ Imperative.Block.definedVars statements true)
    (label : String) (md : MetaData Core.Expression) (Q : Assertion) :
    Core.Logic.Hoare.Triple program.findProcByString? params
      (Lift (ScopedStoresAgree scope factory unwritten)
        ((Transformer.block label (Transformer.scope body)).transform (fun _ => Q)))
      [.block label statements md] (Lift (ScopedStoresAgree scope factory remaining) Q)
      (factory := factory) := by
  apply transfer_scope body statements label md Q ?_ (scoped_postWF keep keepOld Q)
  intro entry
  by_cases fits : StateFits scope entry
  · let post := fun state : State =>
      Q {state with locals := state.locals.restrict entry.locals}
    apply Core.Logic.Hoare.consequence program.findProcByString? params (inside (fun _ => post))
    · exact fun _ h => ⟨entry, h⟩
    · rintro env ⟨state, ⟨agrees, typed⟩, holds⟩
      have projected := agrees.restrictLocals_dropVars entry.locals [] (by simp) (by simp) (by simp)
      refine ⟨_, ⟨?_, fits.restrictLocals typed visible⟩, holds⟩
      have dropsNothing : dropVars (P := Core.Expression) [] env.store = env.store := by
        funext name
        simp [dropVars]
      simpa only [dropsNothing] using projected
  · intro env final trace hpre _ _
    exact False.elim (fits hpre.1.2)

end Strata.Boole.Hoare
