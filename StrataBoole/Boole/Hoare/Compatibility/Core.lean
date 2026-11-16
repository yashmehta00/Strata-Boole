/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Hoare.Compatibility.Fragment
import all StrataBoole.Boole.Hoare.Compatibility.Fragment
public import StrataBoole.Boole.Hoare.Compatibility.Transfer
public import StrataBoole.Boole.Hoare.Compatibility.ScalarEval
import all StrataBoole.Boole.Hoare.Compatibility.Origin
import all StrataBoole.Boole.Hoare.Compatibility.Fresh
import all StrataBoole.Boole.Hoare.Compatibility.Body
import all StrataBoole.Boole.Hoare.Compatibility.Assumption
import all StrataBoole.Boole.Hoare.Compatibility.Initializer
import all StrataBoole.Boole.Hoare.Compatibility.Condition
import all StrataBoole.Boole.Hoare.Compatibility.Expressions
import all StrataBoole.Boole.Hoare.Rules
import all StrataBoole.Boole.Hoare.Compile
import all StrataBoole.Verify
import all Strata.Languages.Core.Procedure
import all StrataBoole.Boole.Semantics.Adequacy.ExecutionLowering
import StrataBoole.Boole.Semantics.Adequacy.BlockShape
public import StrataBoole.Boole.Semantics.Adequacy.Typing
public import StrataBoole.Boole.Semantics.Adequacy.Entry
import all StrataBoole.Boole.Semantics.Adequacy.Entry
import StrataBoole.Boole.Hoare.Compatibility.Entry
import all StrataBoole.Boole.Hoare.Certificate
public import Strata.Languages.Core.Typing.Spec.TypingSpec
import Strata.Util.ListMapProps

public section

namespace Strata.Boole.Hoare

open StrataDDM Core.Logic Imperative

/-- The part of lowering needed for Core compatibility. The two relations
allow the entry to leave output-only slots unconstrained until assignment. -/
structure ContractLowering (prepared : Prepared) (program : Core.Program)
    (name : String) (params : InitEnvWFParams) (target : Core.Procedure)
    (body : Core.Statements) where
  entry : State → Env Core.Expression → Prop
  final : State → Env Core.Expression → Prop
  requires : ∀ env,
    Core.Logic.Hoare.Procedure.contractPre (program.factoryBeforeProcedure name) target env →
    BlockInitEnvWF params [.block "" body #[]] env →
    ∃ globals arguments outputs,
      valuesMatch prepared.globals globals = true ∧
      valuesMatch prepared.procedure.inputs arguments = true ∧
      valuesMatch prepared.procedure.outputs outputs = true ∧
      let state := prepared.entryState globals arguments outputs
      clausesHold prepared.procedure.contract.requires state ∧ entry state env
  ensures : ∀ state env, final state env → prepared.postcondition none state →
    Core.Logic.Hoare.Procedure.contractPost (program.factoryBeforeProcedure name) target env
  bodyTriple : ∀ Q : Assertion,
    Core.Logic.Hoare.Triple program.findProcByString? params
      (Lift entry (prepared.procedure.body.transform (fun
        | none => Q
        | some _ => fun _ => False)))
      [.block "" body #[]] (Lift final Q) (factory := program.factoryBeforeProcedure name)

/-- Consume a Boole certificate directly in Core's Hoare judgment. -/
theorem contractTriple_of_transform
    (prepared : Prepared) (certificate : prepared.Valid)
    (program : Core.Program) (name : String) (params : InitEnvWFParams)
    (target : Core.Procedure) (body : Core.Statements)
    (lookup : program.findProcByString? name = some target)
    (structured : target.body = .structured body)
    (typed : Core.Logic.Hoare.Procedure.contractChecksTyped target)
    (relation : ContractLowering prepared program name params target body) :
    Core.Logic.Hoare.Procedure.contractTriple program params name := by
  apply Core.Logic.Hoare.Procedure.contractTriple_of_core_typed
    program params name target body lookup structured typed
  intro env finalEnv trace pre wf run
  obtain ⟨globals, arguments, outputs, hg, ha, ho, requires, represented⟩ :=
    relation.requires env pre wf
  have condition := certificate.atEntry hg ha ho requires
  obtain ⟨valid, post⟩ := relation.bodyTriple (prepared.postcondition none)
    env finalEnv trace ⟨_, represented, condition⟩ wf run
  refine ⟨valid, fun reachable => ?_⟩
  obtain ⟨state, related, ensures⟩ := post reachable
  exact relation.ensures state finalEnv related ensures

/-- Declarative procedure typing supplies the exact Boolean annotation
check used by Core's contract judgment. -/
theorem contractChecksTyped_of_wellTyped
    {program : Core.Program} {context : Core.Expression.TyContext}
    {scopes : Core.TypeSpec.TypeScopes} {target : Core.Procedure}
    (typed : Core.TypeSpec.ProcWellTyped program context scopes target) :
    Core.Logic.Hoare.Procedure.contractChecksTyped target := by
  constructor <;> apply List.all_eq_true.mpr <;> intro clause member <;>
    apply decide_eq_true
  · exact Lambda.LExpr.HasTypeA_to_typeCheck
      (typed.preconditionsTyped clause.2
        (by rw [ListMap.values_eq_map_snd]; exact List.mem_map_of_mem member)).1
  · exact Lambda.LExpr.HasTypeA_to_typeCheck
      (typed.postconditionsTyped clause.2
        (by rw [ListMap.values_eq_map_snd]; exact List.mem_map_of_mem member)).1

/-- Canonical source entries contain exactly the declared interface slots,
with the saved values constructed by `entryState`. -/
private def IsProcedureEntry (prepared : Prepared) (state : State) : Prop :=
  ∃ globals arguments initialOutputs,
    valuesMatch prepared.globals globals = true ∧
    valuesMatch prepared.procedure.inputs arguments = true ∧
    valuesMatch prepared.procedure.outputs initialOutputs = true ∧
    state = prepared.entryState globals arguments initialOutputs

private def entryRelation (prepared : Prepared) (factory : Lambda.Factory Core.CoreLParams)
    (unwritten : List Core.CoreIdent) (state : State) (env : Env Core.Expression) : Prop :=
  StoreAgrees factory unwritten state env ∧ IsProcedureEntry prepared state

private def returnRelation (prepared : Prepared) (factory : Lambda.Factory Core.CoreLParams)
    (state : State) (env : Env Core.Expression) : Prop :=
  StoreAgrees factory [] state env ∧ StateFits prepared.interfaceScope state

private def BodyLowering (prepared : Prepared) (program : Core.Program) (name : String)
    (params : InitEnvWFParams) (target : Core.Procedure) (body : Core.Statements) : Prop :=
  ∀ Q : Assertion, Core.Logic.Hoare.Triple program.findProcByString? params
    (Lift (entryRelation prepared (program.factoryBeforeProcedure name)
      target.header.getOutputOnlyParams.keys)
      (prepared.procedure.body.transform (fun
        | none => Q
        | some _ => fun _ => False)))
    [.block "" body #[]] (Lift (returnRelation prepared (program.factoryBeforeProcedure name)) Q)
    (factory := program.factoryBeforeProcedure name)

/-- What remains to prove about the two compilers. The interface identifies
the corresponding slots, while the clauses and body use those slots. -/
private structure ProcedureAlignment (prepared : Prepared) (program : Core.Program)
    (name : String) (params : InitEnvWFParams) (target : Core.Procedure)
    (body : Core.Statements) : Prop where
  inputs : ∀ binding ∈ prepared.globals ++ prepared.procedure.inputs,
    binding.sort = .int ∧ ((⟨binding.name, ()⟩ : Core.CoreIdent), Lambda.LMonoTy.int) ∈
      target.header.inputs.toList
  outputs : ∀ binding ∈ prepared.procedure.outputs,
    binding.sort = .int ∧ (⟨binding.name, ()⟩ : Core.CoreIdent) ∈ target.header.getOutputOnlyParams.keys
  modified : ∀ n ∈ prepared.procedure.contract.modifies,
    (⟨n, ()⟩ : Core.CoreIdent) ∈ target.header.getInoutParams.keys
  requires : ∀ clause ∈ prepared.procedure.contract.requires, ∃ label check,
    (label, check) ∈ target.spec.preconditions.toList ∧
    ∀ state env, IsProcedureEntry prepared state →
      StoreAgrees (program.factoryBeforeProcedure name)
        target.header.getOutputOnlyParams.keys state env →
      Core.Expression.eval env.factory env.store check.expr = some (HasBool.ttVal env.factory) →
      Holds clause.condition state
  ensures : ∀ label check, (label, check) ∈ target.spec.postconditions.toList →
    check.attr = Core.Procedure.CheckAttr.Default →
    ∃ clause ∈ prepared.procedure.contract.ensures, clause.free = false ∧
    ∀ state env, StateFits prepared.interfaceScope state →
    StoreAgrees (program.factoryBeforeProcedure name) [] state env →
    Holds clause.condition state →
    Core.Expression.eval env.factory env.store check.expr = some (HasBool.ttVal env.factory)
  bodyTriple : BodyLowering prepared program name params target body

private def ProcedureAlignment.contractLowering
    {prepared : Prepared} {program : Core.Program} {name : String} {params : InitEnvWFParams}
    {target : Core.Procedure} {body : Core.Statements}
    (alignment : ProcedureAlignment prepared program name params target body) :
    ContractLowering prepared program name params target body where
  entry := entryRelation prepared (program.factoryBeforeProcedure name) target.header.getOutputOnlyParams.keys
  final := returnRelation prepared (program.factoryBeforeProcedure name)
  requires env pre wf := by
    obtain ⟨globals, arguments, outputs, hg, ha, ho, related⟩ :=
      entryState_agrees prepared pre wf.storeWellDefined alignment.inputs alignment.outputs alignment.modified
    refine ⟨globals, arguments, outputs, hg, ha, ho, ?_, related,
      globals, arguments, outputs, hg, ha, ho, rfl⟩
    apply requires_of_core related pre
    intro clause member
    obtain ⟨label, check, present, agrees⟩ := alignment.requires clause member
    exact ⟨label, check, present,
      agrees _ env ⟨globals, arguments, outputs, hg, ha, ho, rfl⟩ related⟩
  ensures state env related post := by
    apply ensures_to_core related.1 post
    intro label check member ordinary
    obtain ⟨clause, present, checked, agrees⟩ := alignment.ensures label check member ordinary
    exact ⟨clause, present, checked, agrees state env related.2 related.1⟩
  bodyTriple := alignment.bodyTriple

private theorem compiled_body_lowering
    {source : Boole.Program} {names : GlobalContext}
    {command : BooleDDM.Command SourceRange} {prepared : Prepared}
    {program rawProgram : Core.Program} {name : String} {params : InitEnvWFParams}
    {raw target : Core.Procedure} {metadata : MetaData Core.Expression} {body : Core.Statements}
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    (compiledRun : prepare source names name = .ok prepared)
    (loweringRun : toCoreProgram source names = .ok rawProgram)
    (typedProgram : Core.TypeSpec.ProgramWellTyped coreTypingContext [] program)
    (sameSyntax : procedureSyntax program = procedureSyntax rawProgram)
    (sourceMember : match source with | .prog _ declarations => command ∈ declarations.val.toList)
    (rawMember : Core.Decl.proc raw metadata ∈ rawProgram.decls)
    {sourceScope : Scope}
    (sourceRunOrigin : ProcedureRun command prepared.procedure sourceScope)
    (topScope : TopLevelScope names sourceScope)
    (sourceGlobals : sourceScope.globals = prepared.globals)
    (layout : ProcedureLayout prepared.globals prepared.procedure target)
    (headerSlots : ∀ binding ∈ prepared.globals ++
        (prepared.procedure.inputs ++ prepared.procedure.outputs),
      (⟨binding.name, ()⟩ : Core.CoreIdent) ∈ target.header.inputs.keys ++ target.header.outputs.keys)
    (modifiedSlots : ∀ name ∈ prepared.procedure.contract.modifies,
      (⟨name, ()⟩ : Core.CoreIdent) ∈ target.header.getInoutParams.keys)
    (translated : ProcedureWasLowered command raw)
    (annotated : procedureWithoutAnnotations target = procedureWithoutAnnotations raw)
    (typed : Core.TypeSpec.ProcWellTyped program context scopes target)
    (builtins : ∀ fn : Lambda.LFunc Core.CoreLParams, Core.Factory[fn.name.name]? = some fn →
      context.functions[fn.name.name]? = some fn)
    (structured : target.body = .structured body)
    (supported : bodyInFragment target body) :
    BodyLowering prepared program name params target body := by
  obtain ⟨sourceBody, sourceShape, built⟩ := sourceRunOrigin.body
  obtain ⟨label, rawBody, rawProcedureEntry, rawEntry, rawExit, formalNames,
    rawRun, rawBinders, rawShape, _⟩ := raw_procedure_parts sourceShape translated
  have lowered : BlockWasLowered sourceBody rawBody := ⟨rawEntry, rawExit, rawRun⟩
  have sameBody := congrArg (fun proc : Core.Procedure => proc.body) annotated
  cases sourceBody with
  | block range sourceSyntax =>
    obtain ⟨ann, statements⟩ := sourceSyntax
    by_cases empty : statements = #[]
    · subst statements
      have rawEmpty := BlockWasLowered.empty range ann rawBody lowered
      subst rawBody
      change raw.body = .structured [] at rawShape
      cases body with
      | cons first tail =>
        simp [procedureWithoutAnnotations, structured, rawShape, eraseStatementsAnnotations] at sameBody
      | nil =>
        intro Q
        have slots : some target.header.getOutputOnlyParams.keys = some [] := by
          simpa only [coreStatements] using supported.2
        have outputs := Option.some.inj slots
        simp only [compiledProcedureBody_empty built.exists_scope, outputs]
        apply transfer_empty prepared.procedure.name Q
        rintro state env ⟨related, globals, arguments, outputs, hg, ha, ho, rfl⟩
        exact ⟨related, Prepared.entry_fits hg ha ho⟩
    · have rawNonempty := BlockWasLowered.nonempty range ann statements rawBody lowered empty
      have shaped : raw.body = .structured [.block label rawBody .empty] := by
        simpa [List.isEmpty_eq_false_iff.mpr rawNonempty] using rawShape
      obtain ⟨inner, finalContext, finalScopes, wrapper, innerSyntax, innerTyped⟩ :=
        typed_lowered_block typed shaped sameBody
      obtain rfl := Imperative.Body.structured.inj (structured.symm.trans wrapper)
      obtain ⟨chunks, chunksRun, flattened⟩ := lower_block_chunks rawRun
      let sourceEntry := procedureBodyScope sourceScope prepared.procedure
      obtain ⟨sourceExit, compiled, sourceRun, sourceWrapper⟩ :=
        compiledBlock_inner built
      have globals : sourceEntry.globals = prepared.globals := sourceGlobals
      have locals : sourceEntry.locals = prepared.procedure.inputs ++ prepared.procedure.outputs := by
        simp only [sourceEntry, procedureBodyScope, topScope.2.1, List.nil_append]
      have modifies : sourceEntry.modifies = prepared.procedure.contract.modifies := rfl
      have fitsEntry (state : State) :
          StateFits sourceEntry state ↔ StateFits prepared.interfaceScope state := by
        constructor
        · intro fits
          exact ⟨by simpa only [Prepared.interfaceScope, globals] using fits.globals,
            by simpa only [Prepared.interfaceScope, locals] using fits.locals,
            by simpa only [Prepared.interfaceScope, globals, modifies] using fits.snapshots⟩
        · intro fits
          exact ⟨by simpa only [Prepared.interfaceScope, ← globals] using fits.globals,
            by simpa only [Prepared.interfaceScope, ← locals] using fits.locals,
            by simpa only [Prepared.interfaceScope, ← globals, ← modifies] using fits.snapshots⟩
      have innerGate : coreStatements inner target.header.getOutputOnlyParams.keys = some [] := by
        have gate := supported.2
        cases ran : coreStatements inner target.header.getOutputOnlyParams.keys <;>
          simp [coreStatements, coreStatement, bind, Option.bind, ran] at gate ⊢
        exact gate
      have closed := coreStatements_closed _ _ _ innerGate
      let factory := program.factoryBeforeProcedure name
      let unwritten := target.header.getOutputOnlyParams.keys
      let entryScopes : CompilerScopes :=
        ⟨sourceEntry, rawEntry, context, Core.TypeSpec.procBodyScopes scopes target⟩
      let exitScopes : CompilerScopes := ⟨sourceExit, rawExit, finalContext, finalScopes⟩
      let related : BodyRelation := fun scope unwritten => ScopedStoresAgree scope factory unwritten
      let readOnly := prepared.procedure.inputs.map Binding.name
      obtain ⟨added, sourceExtension⟩ :=
        statements_extend_locals statements.toList readOnly _ _ _ sourceRun
      have onlyLocals : sourceExit = {sourceEntry with locals := sourceExit.locals} := by
        rw [sourceExtension]
      have visible (n : String) (binding : Binding)
          (found : sourceEntry.locals.find? (fun b => b.name == n) = some binding) :
          sourceExit.locals.find? (fun b => b.name == n) = some binding := by
        change (procedureBodyScope sourceScope prepared.procedure).locals.find?
          (fun b => b.name == n) = some binding at found
        simp [sourceExtension, List.find?_append, found]
      have keep (binding : Binding) (member : binding ∈ sourceEntry.globals ++ sourceEntry.locals) :
          (⟨binding.name, ()⟩ : Core.CoreIdent) ∉ Block.definedVars inner true := by
        rw [globals, locals] at member
        obtain ⟨_, lookup⟩ := procBodyScopes_lookup scopes target ⟨binding.name, ()⟩
          (List.mem_append_left _ (headerSlots binding member))
        exact typed_stmts_keep_slot innerTyped lookup
      have keepOld (n : String) (member : n ∈ sourceEntry.modifies) :
          Core.CoreIdent.mkOld n ∉ Block.definedVars inner true := by
        rw [modifies] at member
        obtain ⟨_, lookup⟩ := procBodyScopes_lookup scopes target (Core.CoreIdent.mkOld n)
          (List.mem_append_right _ (List.mem_map_of_mem
            (f := fun id => Core.CoreIdent.mkOld id.name) (modifiedSlots n member)))
        exact typed_stmts_keep_slot innerTyped lookup
      have distinct : ((sourceEntry.locals ++ sourceEntry.globals).map Binding.name).Nodup := by
        rw [locals, globals]
        apply (List.perm_append_comm |>.map Binding.name).nodup_iff.mp
        simpa only [List.append_assoc] using layout.distinct
      obtain ⟨namesMatch, globalsRegistered, modifiesMatch, formalNamesMatch, noOuterBinders, validNames⟩ :
          sourceEntry.names = rawEntry.gctx ∧
          (∀ binding ∈ sourceEntry.globals, rawEntry.globalVarTypes.contains binding.name = true) ∧
          (∀ n, n ∈ sourceEntry.modifies ↔ n ∈ rawEntry.currentInoutNames) ∧
          formalNames = sourceEntry.locals.map Binding.name ∧
          rawProcedureEntry.bvars = #[] ∧
          (∀ binding ∈ sourceEntry.locals ++ sourceEntry.globals,
            binding.name.contains ' ' = false) := by
        sorry
      have aligned : ScopesAgree entryScopes := by
        refine ⟨namesMatch, ?_, globalsRegistered, modifiesMatch, distinct, validNames, builtins⟩
        change rawEntry.bvars = _
        rw [rawBinders, noOuterBinders, formalNamesMatch]
        simp [mkIdent, List.map_toArray, Function.comp_def, entryScopes]
      have addBuiltin := builtinAtProcedure program name
        (Lambda.intAddFunc (T := Core.CoreLParams)).func Core.coreFactory_intAdd
      have geBuiltin := builtinAtProcedure program name
        (Lambda.intGeFunc (T := Core.CoreLParams)).func Core.coreFactory_intGe
      have statementTransfer :
          StatementTransfer program params factory related ScopesAgree readOnly [label] := by
        intro statement entry final result raw annotated unwritten remaining
          built lowered erased typed gate aligned
        cases statement with
        | assign range annotations other lhs expression =>
          cases lhs with
          | lhsIdent lhsRange lhsName =>
            apply assignment_transfer built lowered erased typed gate aligned
            intro value rawExpr target sort compiledExpr rawRun sameExpr typedExpr readable
            by_cases literal : isScalarLiteral expression
            · obtain ⟨_, _, _, agrees⟩ := literal_agrees literal compiledExpr
                ⟨_, rawRun⟩ sameExpr (ScopedStoresAgree entry.source factory unwritten)
              exact ⟨literal_lowering_unchanged literal rawRun, agrees⟩
            · cases expression with
              | bvar range index =>
                have ⟨stable, agrees, _⟩ := bound_rhs_agrees (factory := factory)
                  aligned compiledExpr rawRun sameExpr readable
                exact ⟨stable, agrees⟩
              | fvar range index =>
                have ⟨stable, agrees, _⟩ := global_rhs_agrees (factory := factory)
                  aligned compiledExpr rawRun sameExpr readable
                exact ⟨stable, agrees⟩
              | add_expr range kind lhs rhs =>
                cases kind with
                | int typeRange =>
                  by_cases supported : IntegerSum (.add_expr range (.int typeRange) lhs rhs)
                  · obtain ⟨_, _, _, _, _, _, sort, _⟩ := compiled_int_add compiledExpr
                    obtain ⟨stable, evaluate⟩ := integer_sum_agrees supported aligned
                      (builtinAtProcedure program name
                        (Lambda.intAddFunc (T := Core.CoreLParams)).func Core.coreFactory_intAdd)
                      compiledExpr rawRun sameExpr typedExpr readable sort
                    refine ⟨stable, ?_⟩
                    intro state env value related ran
                    obtain ⟨n, source, target⟩ := evaluate state env related
                    obtain rfl := Except.ok.inj (ran.symm.trans source)
                    exact ⟨_, rfl, target⟩
                  · sorry
                | _ => sorry
              | _ => sorry
          | lhsArray =>
            rw [stmt.eq_def] at built
            contradiction
        | initStatement range annotations ty localName expression =>
          by_cases accepted : SupportedCondition expression
          · apply initializer_transfer built lowered erased typed gate aligned
            intro value middle rawExpr target _ sourceRun rawRun exprEq exprTyped readable
            exact condition_agrees accepted aligned addBuiltin geBuiltin
              sourceRun rawRun exprEq exprTyped readable
          · sorry
        | assert range annotations label expression =>
          by_cases accepted : SupportedCondition expression
          · apply assertion_transfer built lowered erased typed gate aligned
            intro middle rawEnd value rawExpr target middleAligned sourceRun rawRun exprEq
              expressionTyped readable
            exact condition_agrees accepted middleAligned addBuiltin geBuiltin
              sourceRun rawRun exprEq expressionTyped readable
          · sorry
        | assume range annotations label expression =>
          by_cases accepted : SupportedCondition expression
          · apply assumption_transfer built lowered erased typed gate aligned
            intro value middle rawEnd rawExpr target sourceRun rawRun exprEq expressionTyped readable
              middleAligned
            exact condition_agrees accepted middleAligned addBuiltin geBuiltin
              sourceRun rawRun exprEq expressionTyped readable
          · sorry
        | _ => sorry
      have scopeEquiv : ∀ entry other, Strata.Util.HMaps.Equiv other entry.variables →
          ScopesAgree entry → ScopesAgree {entry with variables := other} := by
        intro entry other equivalent agrees
        exact ⟨agrees.names, agrees.binders, agrees.globals, agrees.modifies, agrees.distinct,
          agrees.validNames, agrees.builtins⟩
      have inside := (compiled_statements_transfer program params factory related ScopesAgree
        readOnly [label] scopeEquiv statementTransfer statements.toList (entry := entryScopes)
        (final := exitScopes) sourceRun chunksRun (flattened.symm ▸ innerSyntax) innerTyped innerGate aligned).2
      change BodyTransfer program params factory related sourceEntry sourceExit unwritten []
        compiled.command inner at inside
      have scopedInside : BodyTransfer program params factory related sourceEntry
          {sourceEntry with locals := sourceExit.locals} unwritten [] compiled.command inner :=
        onlyLocals ▸ inside
      intro Q
      have named := transfer_scoped_body scopedInside visible keep keepOld label #[] Q
      have outer := Core.Logic.Hoare.block program.findProcByString? params (l := "") (md := #[]) named
        (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by simp))
      apply Core.Logic.Hoare.consequence program.findProcByString? params outer
      · rintro env ⟨state, ⟨store, globals, arguments, outputs, hg, ha, ho, rfl⟩, condition⟩
        refine ⟨_, ⟨store, (fitsEntry _).mpr (Prepared.entry_fits hg ha ho)⟩, ?_⟩
        rw [sourceWrapper] at condition
        have normal := (Transformer.block prepared.procedure.name
          (Transformer.scope compiled.command)).monotone
          (Q := fun _ => Q) (by
            intro control state holds
            cases control with
            | none => exact holds
            | some _ => exact False.elim holds) _ condition
        have constant (blockLabel : String) :
            ((Transformer.block blockLabel (Transformer.scope compiled.command)).transform
              (fun _ => Q)) = (Transformer.scope compiled.command).transform (fun _ => Q) := by
          unfold Transformer.block
          congr 1
        rw [constant] at normal ⊢
        exact normal
      · rintro env ⟨state, ⟨store, fits⟩, holds⟩
        exact ⟨state, ⟨store, (fitsEntry state).mp fits⟩, holds⟩

private theorem source_single_true_requires {range ann : SourceRange} {outputs : List Binding}
    {before after : Scope} {spec : Contract Expression}
    (ran : contract (some (.spec_mk range
      ⟨ann, #[.requires_spec range ⟨ann, none⟩ ⟨ann, none⟩ (.btrue range)]⟩))
        outputs before = .ok (spec, after)) :
    spec.modifies = [] ∧ spec.ensures = [] ∧
      ∀ clause ∈ spec.requires, ∀ state, Holds clause.condition state := by
  have always : boolean range (.btrue range) { requiresOutputs := some (outputs.map Binding.name) } =
      pure (fun _ => .ok (.bool true)) := by
    unfold boolean
    rw [expr.eq_def]
    rfl
  unfold contract at ran
  simp only [← Array.forIn_toList, List.forIn_cons, List.forIn_nil,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, always,
    bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
  obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj ran)
  simp [Holds, test, Value.bool]

private theorem raw_single_true_requires {range ann procRange : SourceRange} {name : String}
    {before after : TranslateState} {spec : Core.Procedure.Spec}
    (ran : toCoreSpec procRange name (some (.spec_mk range
      ⟨ann, #[.requires_spec range ⟨ann, none⟩ ⟨ann, none⟩ (.btrue range)]⟩))
        before = .ok (spec, after)) :
    spec.preconditions.toList ≠ [] ∧ spec.postconditions.toList = [] := by
  have always : toCoreExpr (.btrue range) = pure (.true ()) := by
    rw [toCoreExpr.eq_def]
    simp only [toCoreQuantExpr?]
  simp only [toCoreSpec, toCoreSpecElts, List.forIn_cons, List.forIn_nil, always,
    toCoreMetaData, defaultLabel, get, getThe, MonadStateOf.get, StateT.get,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
  obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj ran)
  simp [ListMap.toList]

/-- Temporary static premise shared with adequacy. Discharge this from the
actual source bindings and the two raw header encoding lemmas in
`Adequacy/DeclarativeEntry.lean`. -/
def CoreLayoutSpec : Prop :=
  ∀ source names name raw checked prepared target,
    prepare source names name = .ok prepared →
    toCoreProgram source names = .ok raw →
    CoreBridgeFragment source names checked name →
    Core.TypeSpec.ProgramWellTyped coreTypingContext [] checked →
    procedureSyntax checked = procedureSyntax raw →
    checked.findProcByString? name = some target →
    ProcedureLayout prepared.globals prepared.procedure target

private theorem member_encoded_formal {bindings : List Binding}
    {formals : List (Core.CoreIdent × Lambda.LMonoTy)}
    (encoded : bindings.mapM scalarFormal? = some formals)
    {binding : Binding} (present : binding ∈ bindings) :
    ∃ formal ∈ formals, scalarFormal? binding = some formal := by
  induction bindings generalizing formals with
  | nil => simp at present
  | cons first rest ih =>
    simp only [List.mapM_cons, bind, Option.bind, pure] at encoded
    cases head : scalarFormal? first with
    | none => simp [head] at encoded
    | some formal =>
      cases tail : rest.mapM scalarFormal? with
      | none => simp [head, tail] at encoded
      | some restFormals =>
        have same : formal :: restFormals = formals := by simpa [head, tail] using encoded
        subst formals
        rcases List.mem_cons.mp present with rfl | later
        · exact ⟨formal, List.mem_cons_self, head⟩
        · obtain ⟨other, member, code⟩ := ih tail later
          exact ⟨other, List.mem_cons_of_mem _ member, code⟩

private theorem integer_formal {binding : Binding} {id : Core.CoreIdent}
    (encoded : scalarFormal? binding = some (id, Lambda.LMonoTy.int)) :
    binding.sort = .int ∧ id = ⟨binding.name, ()⟩ := by
  unfold scalarFormal? at encoded
  split at encoded <;> simp_all [Lambda.LMonoTy.int, Lambda.LMonoTy.bool, Lambda.LMonoTy.string,
    Lambda.LMonoTy.real]

/-- Relate the two compiler outputs using their common source declaration. -/
private theorem compiled_contract_lowering
    {source : Boole.Program} {names : GlobalContext} {checked : Core.Program}
    {name : String} {prepared : Prepared} {target : Core.Procedure} {body : Core.Statements}
    {command : BooleDDM.Command SourceRange} {raw : Core.Program} {before : Core.Procedure}
    {metadata : MetaData Core.Expression}
    (params : InitEnvWFParams)
    (compiled : prepare source names name = .ok prepared)
    (lowered : toCoreProgram source names = .ok raw)
    (fragment : CoreBridgeFragment source names checked name)
    (typedProgram : Core.TypeSpec.ProgramWellTyped coreTypingContext [] checked)
    (sameSyntax : procedureSyntax checked = procedureSyntax raw)
    (sourceMember : match source with | .prog _ declarations => command ∈ declarations.val.toList)
    (rawMember : Core.Decl.proc before metadata ∈ raw.decls)
    (lookup : checked.findProcByString? name = some target)
    (structured : target.body = .structured body)
    (layout : ProcedureLayout prepared.globals prepared.procedure target)
    {sourceScope : Scope}
    (sourceRunOrigin : ProcedureRun command prepared.procedure sourceScope)
    (topScope : TopLevelScope names sourceScope)
    (sourceGlobals : sourceScope.globals = prepared.globals)
    (translated : ProcedureWasLowered command before)
    (annotated : procedureWithoutAnnotations target = procedureWithoutAnnotations before)
    {context : Core.Expression.TyContext} {scopes : Core.TypeSpec.TypeScopes}
    (typed : Core.TypeSpec.ProcWellTyped checked context scopes target)
    (builtins : ∀ fn : Lambda.LFunc Core.CoreLParams, Core.Factory[fn.name.name]? = some fn →
      context.functions[fn.name.name]? = some fn) :
    ProcedureAlignment prepared checked name params target body := by
  have supported : bodyInFragment target body := by
    obtain ⟨proc, stmts, found, shape, inside⟩ := fragment.2
    obtain rfl := Option.some.inj (found.symm.trans lookup)
    obtain rfl := Imperative.Body.structured.inj (shape.symm.trans structured)
    exact inside
  obtain ⟨_, _, sourceContract⟩ := ProcedureOrigin.specification sourceRunOrigin.origin
  obtain ⟨sourceBody, bodyShape, _⟩ := ProcedureOrigin.body sourceRunOrigin.origin
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rawContract⟩ := raw_procedure_parts bodyShape translated
  have integer : ∀ pair ∈ target.header.inputs.toList ++ target.header.outputs.toList,
      pair.2 = Lambda.LMonoTy.int :=
    fun pair member => beq_iff_eq.mp (List.all_eq_true.mp supported.1 pair member)
  have inputs : ∀ binding ∈ prepared.globals ++ prepared.procedure.inputs,
      binding.sort = .int ∧ ((⟨binding.name, ()⟩ : Core.CoreIdent), Lambda.LMonoTy.int) ∈
        target.header.inputs.toList := by
    intro binding member
    obtain ⟨globals, order, encoded⟩ := layout.inputs
    have included := (order.append_right prepared.procedure.inputs).mem_iff.mpr member
    obtain ⟨⟨id, ty⟩, inHeader, code⟩ := member_encoded_formal encoded included
    have slotType := integer (id, ty) (List.mem_append_left _ inHeader)
    change ty = Lambda.LMonoTy.int at slotType
    subst ty
    obtain ⟨sort, rfl⟩ := integer_formal code
    exact ⟨sort, inHeader⟩
  have outputs : ∀ binding ∈ prepared.procedure.outputs,
      binding.sort = .int ∧ (⟨binding.name, ()⟩ : Core.CoreIdent) ∈
        target.header.getOutputOnlyParams.keys := by
    intro binding member
    obtain ⟨⟨id, ty⟩, inOnly, code⟩ := member_encoded_formal layout.outputOnly member
    obtain ⟨inHeader, notInput⟩ := List.mem_filter.mp inOnly
    have slotType := integer (id, ty) (List.mem_append_right _ inHeader)
    change ty = Lambda.LMonoTy.int at slotType
    subst ty
    obtain ⟨sort, rfl⟩ := integer_formal code
    refine ⟨sort, ?_⟩
    have sameKeys : target.header.getOutputOnlyParams.keys =
        Imperative.Calls.outputOnlyParams (P := Core.Expression) target.header := by
      rw [ListMap.keys_eq_map_fst target.header.getOutputOnlyParams]
      change (target.header.outputs.toList.filter
        (fun slot => !target.header.inputs.keys.contains slot.1)).map Prod.fst =
        target.header.outputs.keys.filter (fun id => !target.header.inputs.keys.contains id)
      have keys : target.header.outputs.keys = target.header.outputs.toList.map Prod.fst :=
        ListMap.keys_eq_map_fst _
      rw [keys, List.filter_map]
      rfl
    rw [sameKeys, coreOutputOnly_keys]
    exact List.mem_map_of_mem (f := Prod.fst) inOnly
  have modified : ∀ name ∈ prepared.procedure.contract.modifies,
      (⟨name, ()⟩ : Core.CoreIdent) ∈ target.header.getInoutParams.keys := by
    intro name member
    have hit := (layout.inoutNames (⟨name, ()⟩ : Core.CoreIdent)).mpr member
    have sameKeys : target.header.getInoutParams.keys =
        Imperative.Calls.inoutParams (P := Core.Expression) target.header := by
      rw [ListMap.keys_eq_map_fst target.header.getInoutParams]
      change (target.header.inputs.toList.filter
        (fun slot => target.header.outputs.keys.contains slot.1)).map Prod.fst =
        target.header.inputs.keys.filter (fun id => target.header.outputs.keys.contains id)
      have keys : target.header.inputs.keys = target.header.inputs.toList.map Prod.fst :=
        ListMap.keys_eq_map_fst _
      rw [keys, List.filter_map]
      rfl
    exact sameKeys.symm ▸ hit
  have headerSlots (binding : Binding) (member : binding ∈ prepared.globals ++
      (prepared.procedure.inputs ++ prepared.procedure.outputs)) :
      (⟨binding.name, ()⟩ : Core.CoreIdent) ∈ target.header.inputs.keys ++ target.header.outputs.keys := by
    rw [← List.append_assoc] at member
    rcases List.mem_append.mp member with input | output
    · have keys : target.header.inputs.keys = target.header.inputs.toList.map Prod.fst :=
        ListMap.keys_eq_map_fst _
      rw [keys]
      exact List.mem_append_left _ (List.mem_map_of_mem (inputs binding input).2)
    · obtain ⟨modified, _, _, encoded⟩ := layout.outputs
      obtain ⟨pair, represents, code⟩ :=
        member_encoded_formal encoded (List.mem_append_right modified output)
      have same := scalarFormal_name binding pair code
      have keys : target.header.outputs.keys = target.header.outputs.toList.map Prod.fst :=
        ListMap.keys_eq_map_fst _
      rw [keys]
      apply List.mem_append_right
      refine List.mem_map.mpr ⟨pair, represents, ?_⟩
      change pair.1 = (⟨binding.name, ()⟩ : Core.CoreIdent)
      exact (coreIdent_name_iff pair.1 ⟨binding.name, ()⟩).mp same
  have bodyTriple :=
    compiled_body_lowering (params := params) compiled lowered typedProgram sameSyntax
      sourceMember rawMember sourceRunOrigin topScope sourceGlobals layout headerSlots modified translated annotated typed builtins structured supported
  have specEq := congrArg (fun p : Core.Procedure => p.spec) annotated
  have checkedPostsEmpty (rawPosts : before.spec.postconditions.toList = []) :
      target.spec.postconditions.toList = [] := by
    have posts := congrArg (fun s : Core.Procedure.Spec => s.postconditions.toList) specEq
    change target.spec.postconditions.toList.map
      (fun (label, check) => (label, Core.Procedure.Check.eraseTypes check)) =
      before.spec.postconditions.toList.map
        (fun (label, check) => (label, Core.Procedure.Check.eraseTypes check)) at posts
    rw [rawPosts] at posts
    exact List.map_eq_nil_iff.mp posts
  by_cases noSpec : procedureSpecification command = none
  · simp only [noSpec, contract, pure, StateT.pure, Except.pure] at sourceContract
    have sourceEmpty : prepared.procedure.contract = {} :=
      (congrArg Prod.fst (Except.ok.inj sourceContract)).symm
    simp only [noSpec, toCoreSpec, pure, StateT.pure, Except.pure] at rawContract
    have rawEmpty : before.spec = { preconditions := [], postconditions := [] } :=
      (congrArg Prod.fst (Except.ok.inj rawContract)).symm
    have noCoreEnsures := checkedPostsEmpty (by rw [rawEmpty]; rfl)
    refine ⟨inputs, outputs, modified, ?_, ?_, bodyTriple⟩
    · simp [sourceEmpty]
    · simp [noCoreEnsures]
  · by_cases trivialRequires : ∃ (range ann : SourceRange), procedureSpecification command =
        some (.spec_mk range ⟨ann,
          #[.requires_spec range ⟨ann, none⟩ ⟨ann, none⟩ (.btrue range)]⟩)
    · obtain ⟨range, ann, specShape⟩ := trivialRequires
      rw [specShape] at sourceContract rawContract
      obtain ⟨_, _, requiresTrue⟩ := source_single_true_requires sourceContract
      obtain ⟨rawHasRequires, rawPostsEmpty⟩ := raw_single_true_requires rawContract
      have targetHasRequires : target.spec.preconditions.toList ≠ [] := by
        intro none
        have pres := congrArg (fun s : Core.Procedure.Spec => s.preconditions.toList) specEq
        change target.spec.preconditions.toList.map
          (fun (label, check) => (label, Core.Procedure.Check.eraseTypes check)) =
          before.spec.preconditions.toList.map
            (fun (label, check) => (label, Core.Procedure.Check.eraseTypes check)) at pres
        rw [none] at pres
        exact rawHasRequires (List.map_eq_nil_iff.mp pres.symm)
      refine ⟨inputs, outputs, modified, ?_, by simp [checkedPostsEmpty rawPostsEmpty], bodyTriple⟩
      intro clause member
      cases found : target.spec.preconditions.toList with
      | nil => exact False.elim (targetHasRequires found)
      | cons first rest =>
          exact ⟨first.1, first.2, by simp, fun state _ _ _ _ => requiresTrue clause member state⟩
    · refine ⟨inputs, outputs, modified, ?_, ?_, bodyTriple⟩ <;> sorry

/-- A verified Boole procedure satisfies the Core contract on its checked lowering. -/
def CoreCompatibility : Prop :=
  ∀ source names name checked params,
    checkedCoreProgram source names = .ok checked →
    CoreBridgeFragment source names checked name →
    Verified source names name →
    Core.Logic.Hoare.Procedure.contractTriple checked params name

/-- Core compatibility takes annotated typing and preservation of the raw
procedure's syntax from Strata's checker specification. -/
theorem core_compatibility_of_wellTyped
    {source : Boole.Program} {names : GlobalContext} {name : String}
    {raw checked : Core.Program} {params : InitEnvWFParams}
    (lowered : toCoreProgram source names = .ok raw)
    (fragment : CoreBridgeFragment source names checked name)
    (verified : Verified source names name)
    (typedProgram : Core.TypeSpec.ProgramWellTyped coreTypingContext [] checked)
    (preserved : procedureSyntax checked = procedureSyntax raw)
    (layoutSpec : CoreLayoutSpec) :
    Core.Logic.Hoare.Procedure.contractTriple checked params name := by
  obtain ⟨prepared, compiled, certificate⟩ := verified_iff.mp verified
  obtain ⟨target, body, lookup, structured, _⟩ := fragment.2
  obtain ⟨_, typed, builtins⟩ := wellTypedProcedure_with_builtins typedProgram lookup
  obtain ⟨command, _, sourceMember, sourceRunOrigin, topScope, sourceGlobals⟩ :=
    prepare_scoped_origin compiled
  have named := ProcedureOrigin.name sourceRunOrigin.origin |>.trans (congrArg some (prepare_name compiled))
  obtain ⟨_, _, rawMember, translated, annotated⟩ :=
    annotated_lowering sourceMember named lowered typedProgram preserved lookup
  have layout := layoutSpec source names name raw checked prepared target
    compiled lowered fragment typedProgram preserved lookup
  have alignment := compiled_contract_lowering params compiled lowered fragment typedProgram preserved
    sourceMember rawMember lookup structured layout sourceRunOrigin topScope sourceGlobals translated annotated typed builtins
  exact contractTriple_of_transform prepared certificate checked name params target body lookup
    structured (contractChecksTyped_of_wellTyped typed) alignment.contractLowering

/-- Given Strata's guarantees about the selected checked program and the
shared procedure layout, conclude the original compatibility proposition. -/
theorem core_compatibility
    (checkerSpec : ∀ source names name checked,
      checkedCoreProgram source names = .ok checked →
      CoreBridgeFragment source names checked name →
      ∃ raw, toCoreProgram source names = .ok raw ∧
        Core.TypeSpec.ProgramWellTyped coreTypingContext [] checked ∧
        procedureSyntax checked = procedureSyntax raw)
    (layoutSpec : CoreLayoutSpec) :
    CoreCompatibility := by
  intro source names name checked params lowered fragment verified
  obtain ⟨_, raw, typed, preserved⟩ := checkerSpec source names name checked lowered fragment
  exact core_compatibility_of_wellTyped raw fragment verified typed preserved layoutSpec

end Strata.Boole.Hoare
