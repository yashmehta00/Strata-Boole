/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.StatementSemantics
public import Strata.Languages.Core.ProgramTypeSpec
public import Strata.Languages.Core.Logic.LangDef
public import StrataBoole.Shallow.Interpreter.Interp

/-!
# Successful statement executions (WIP)

The two directional lemmas compare the same Core statement list under
`Core.CoreStepStarE` and `interpStmts`:

    Core initial store ──execution──▶ Core final store
             agrees                           agrees
    Lean initial store ──computation─▶ Lean final store

`CheckedStatementInput` records the starting data and hypotheses. The lemmas
state the execution claims directly; `statement_success_correspondence` pairs
them for use in the procedure-level proofs.

Both proofs contain `sorry`. The input contract remains provisional, especially
for expression-evaluator completeness and representation of native havoc choices.
The contract or source observation may need revision before the goals are
provable. See `Interpreter/Adequacy.lean` for the remaining obligations.
-/

@[expose] public section

namespace Strata.Shallow.Interp.Adequacy

open Lambda Imperative

/-- Copy the model's type/operation interpretations and the type-variable
valuation into the interpreter's `Sem` record. -/
abbrev toSem (model : Lambda.Interp Core.Factory) (typeValues : TyVarVal) : Sem :=
  { tcInterp := model.tcInterp
    opInterp := model.opInterp
    inhab := model.allInhabited
    vt := typeValues }

/-- Corresponding stored values, expressed using Strata's existing `LExpr.denote`.

For every Core binding `variableName ↦ coreValue`, and every type justified by
`valueHasType`, the mathematical meaning of that syntax value must equal the
interpreter's value at the same name and instantiated sort. For example, a Core
integer-literal node containing `5` must correspond to the Lean integer `5`.

`[]` and `.nil` are the empty context/valuation for surrounding bound variables;
ordinary named variables are read from `interpStore`. `substTyVars` replaces
type variables using `typeValues` to obtain the sort used for native lookup.

This relation does not require a binding where Core has none. Required bindings
and their types must therefore be established separately. It does not require
equality at irrelevant positions of the interpreter's total store. -/
def StoresAgree (model : Lambda.Interp Core.Factory) (typeValues : TyVarVal)
    (coreStore : Core.CoreStore) (interpStore : Store (toSem model typeValues)) : Prop :=
  ∀ (variableName : Core.CoreIdent) (coreValue : Core.Expression.Expr)
    (coreType : LMonoTy),
    coreStore variableName = some coreValue →
    ∀ valueHasType : LExpr.HasTypeA [] coreValue coreType,
      LExpr.denote model.tcInterp model.opInterp interpStore typeValues .nil
        coreValue coreType valueHasType =
      interpStore variableName (LMonoTy.substTyVars typeValues coreType)

/-- Every recorded assumption and assertion evaluates to Core's literal `true`
in its captured store and factory. Covers impose no condition.

This describes one passing execution path, rather than the deductive assertion
validity expressed by `Trace.AssertionsValid`. A trace records checks, not every
assignment or execution step.

A condition can denote `true` without evaluating to literal `true`. This choice
of observation therefore needs an expression bridge to the interpreter's
`LExpr.denote`; typing alone does not establish agreement. -/
def ChecksPass (trace : Trace Core.Expression) : Prop :=
  ∀ event ∈ trace,
    match event with
    | .assume condition | .assert condition =>
        Core.Expression.eval condition.factory condition.store condition.expr =
          some (HasBool.tt (P := Core.Expression))
    | .cover _ => True

/-- Passing checks compose across the trace segments of consecutive executions. -/
theorem checksPass_append (firstTrace secondTrace : Trace Core.Expression) :
    ChecksPass (firstTrace ++ secondTrace) ↔
      ChecksPass firstTrace ∧ ChecksPass secondTrace := by
  constructor
  · intro passing
    exact ⟨fun event present => passing event (List.mem_append_left secondTrace present),
      fun event present => passing event (List.mem_append_right firstTrace present)⟩
  · rintro ⟨prefixPasses, suffixPasses⟩ event present
    rcases List.mem_append.mp present with inPrefix | inSuffix
    · exact prefixPasses event inPrefix
    · exact suffixPasses event inSuffix

/-- Statement forms handled by `interpStmts` and its recursive helpers.

Allows base commands (including list-level `init`), blocks, both kinds of
conditional, and deterministic-guard loops. Calls, exits, local type declarations,
and nondeterministic-guard loops are excluded recursively.

This checks syntax coverage only. Expression/type support remains separate.
Extending this predicate changes the scope of the correspondence claims. -/
def SupportedStatements : List Core.Statement → Prop
  | [] => True
  | .cmd (.cmd _) :: rest => SupportedStatements rest
  | .block _ body _ :: rest =>
      SupportedStatements body ∧ SupportedStatements rest
  | .ite _ thenBody elseBody _ :: rest =>
      SupportedStatements thenBody ∧ SupportedStatements elseBody ∧
        SupportedStatements rest
  | .loop (.det _) _ _ body _ :: rest =>
      SupportedStatements body ∧ SupportedStatements rest
  | _ => False
termination_by statements => sizeOf statements

/-- Starting data and proposed hypotheses for statement correspondence.

The first seven fields are data; the remaining fields are proofs supplied when
applying the lemmas. `typedEntry` shares one source variable context between
statement typing, agreement with native variable types, and initial-value typing.
Other contexts and initialization policies are existential witnesses.

The contract still needs review for expression definedness and value-domain
coverage. It contains no assumption of statement-execution correspondence.

The statement list need not occur as a procedure body in `program`: that program
supplies the reference's procedure lookup, and calls are currently excluded.
Typing and execution use `Core.Factory`; `programTyped` does not install program
declarations in that factory. Declared functions need an extended factory/model
before they can be covered. -/
structure CheckedStatementInput where
  /-- Meanings of types and operations, with Strata's consistency evidence. -/
  model : Lambda.Interp Core.Factory
  /-- Instantiate type variables with sorts. -/
  typeValues : TyVarVal
  /-- Surrounding Core program, used for procedure lookup in the reference. -/
  program : Core.Program
  /-- The same existing Core AST is passed to both sides. -/
  statements : List Core.Statement
  /-- Variable names and types used by the interpreter. -/
  variableTypes : Ctx
  /-- Core represents stored values as expression syntax. -/
  coreInitialStore : Core.CoreStore
  /-- The interpreter represents stored values as mathematical Lean values. -/
  interpInitialStore : Store (toSem model typeValues)

  /-- Restrict the claim to statement forms the interpreter handles. -/
  supported : SupportedStatements statements

  /-- The surrounding program satisfies Core's existing typing judgment. -/
  programTyped :
    ∃ (programTypeContext : LContext Core.CoreLParams)
      (programVariableTypes : TContext Unit),
      Core.TypeSpec.ProgramHasTypeA
        programTypeContext programVariableTypes program

  /-- Suitable contexts exist in which the statements are well typed, the
  typing factory is the actual execution factory, source/native variable types
  agree, and declared initial variables have source values of their declared
  types. The empty label list excludes an exit escaping the statement list. -/
  typedEntry :
    ∃ (typeContext : LContext Core.CoreLParams)
      (sourceTypes : TContext Unit)
      (finalTypeContext : LContext Core.CoreLParams)
      (finalSourceTypes : TContext Unit),
      typeContext.functions = Core.Factory ∧
      Core.TypeSpec.StatementsHasTypeA
        program typeContext sourceTypes [] statements
        finalTypeContext finalSourceTypes ∧
      (∀ variableName : Core.CoreIdent,
        sourceTypes.types.find? variableName =
          (variableTypes.tys.lookup variableName).map (LTy.forAll [])) ∧
      (∀ (variableName : Core.CoreIdent) (coreType : LMonoTy),
        sourceTypes.types.find? variableName = some (LTy.forAll [] coreType) →
        ∃ coreValue : Core.Expression.Expr,
          coreInitialStore variableName = some coreValue ∧
          HasVal.valueOfTy (P := Core.Expression)
            Core.Factory coreValue (LTy.forAll [] coreType))

  /-- Core's existing initial-environment gate holds for some policy.
  Existential quantification does not fix a compiler's reserved prefixes: the
  policy may use an empty prefix list. The gate also records store values,
  defined reads/writes, fresh declarations, and evaluator properties. Review
  which of these requirements the correspondence proof actually needs. -/
  initialWellFormed :
    ∃ params : Core.Logic.InitEnvWFParams,
      Core.Logic.BlockInitEnvWF params statements
        ⟨coreInitialStore, Core.Factory, false⟩

  /-- Both computations start with corresponding values. -/
  initialStoresAgree :
    StoresAgree model typeValues coreInitialStore interpInitialStore

/-- Every normally terminating Core execution with passing checks has a
permitted interpreter result whose final values agree.

`.stmts` and `.terminal` are Core configuration constructors. The initial
record contains the store, built-in factory, and legacy failure flag `false`;
`ChecksPass` supplies the success observation. `.run (some store)` means a
permitted successful outcome.

This is the direction that rules out losing Core results. The reverse lemma
rules out additional interpreter results. -/
theorem core_execution_has_matching_interp_result
    (input : CheckedStatementInput) :
    ∀ (trace : Trace Core.Expression)
      (coreFinalEnv : Env Core.Expression),
      Core.CoreStepStarE input.program.findProcByString?
        (.stmts input.statements
          ⟨input.coreInitialStore, Core.Factory, false⟩)
        trace (.terminal coreFinalEnv) →
      ChecksPass trace →
      ∃ interpFinalStore : Store (toSem input.model input.typeValues),
        (interpStmts (toSem input.model input.typeValues)
          input.variableTypes input.statements input.interpInitialStore).run
            (some interpFinalStore) ∧
        StoresAgree input.model input.typeValues
          coreFinalEnv.store interpFinalStore := by
  -- First establish expression soundness and the store/context invariants.
  -- Then match Core steps with interpreter outcomes, generalizing the initial
  -- context/store as needed for sequencing, scope, and loop iterations.
  sorry

/-- Every permitted successful interpreter result has a normally terminating
Core execution with passing checks and corresponding final values.

This direction rules out additional interpreter results. Together, the two
lemmas concern successful completion; they do not establish termination of every
run, equality of intermediate traces, or assertion-failure correspondence. -/
theorem interp_result_has_matching_core_execution
    (input : CheckedStatementInput) :
    ∀ interpFinalStore : Store (toSem input.model input.typeValues),
      (interpStmts (toSem input.model input.typeValues)
        input.variableTypes input.statements input.interpInitialStore).run
          (some interpFinalStore) →
      ∃ (trace : Trace Core.Expression)
        (coreFinalEnv : Env Core.Expression),
        Core.CoreStepStarE input.program.findProcByString?
          (.stmts input.statements
            ⟨input.coreInitialStore, Core.Factory, false⟩)
          trace (.terminal coreFinalEnv) ∧
        ChecksPass trace ∧
        StoresAgree input.model input.typeValues
          coreFinalEnv.store interpFinalStore := by
  -- First resolve evaluator completeness and reification of native choices.
  -- Then decompose interpreter outcomes and construct the corresponding Core
  -- execution, carrying the same store/context invariants as the forward proof.
  sorry

/-- Both successful-execution claims, proved by pairing the directional lemmas.
This inherits their unfinished proofs and provisional input conditions. -/
theorem statement_success_correspondence
    (input : CheckedStatementInput) :
    (∀ (trace : Trace Core.Expression)
      (coreFinalEnv : Env Core.Expression),
      Core.CoreStepStarE input.program.findProcByString?
        (.stmts input.statements
          ⟨input.coreInitialStore, Core.Factory, false⟩)
        trace (.terminal coreFinalEnv) →
      ChecksPass trace →
      ∃ interpFinalStore : Store (toSem input.model input.typeValues),
        (interpStmts (toSem input.model input.typeValues)
          input.variableTypes input.statements input.interpInitialStore).run
            (some interpFinalStore) ∧
        StoresAgree input.model input.typeValues
          coreFinalEnv.store interpFinalStore) ∧
    (∀ interpFinalStore : Store (toSem input.model input.typeValues),
      (interpStmts (toSem input.model input.typeValues)
        input.variableTypes input.statements input.interpInitialStore).run
          (some interpFinalStore) →
      ∃ (trace : Trace Core.Expression)
        (coreFinalEnv : Env Core.Expression),
        Core.CoreStepStarE input.program.findProcByString?
          (.stmts input.statements
            ⟨input.coreInitialStore, Core.Factory, false⟩)
          trace (.terminal coreFinalEnv) ∧
        ChecksPass trace ∧
        StoresAgree input.model input.typeValues
          coreFinalEnv.store interpFinalStore) := by
  exact ⟨core_execution_has_matching_interp_result input,
    interp_result_has_matching_core_execution input⟩

end Strata.Shallow.Interp.Adequacy
