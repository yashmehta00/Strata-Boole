/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.InstWellFormedSemanticsEval
public import Strata.Languages.Core.Program
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryProps
import Strata.Util.Tactics
public import Strata.Languages.Core.Typing.Spec.TypingSpec
import all StrataBoole.Boole.Semantics.Adequacy.Lowering
import all Strata.Languages.Core.Factory
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Denote.LExprDenote

public section
namespace Strata.Boole.Hoare

open Lambda

/-- The initial Core typing context for a closed lowered Boole program. -/
abbrev coreTypingContext : Core.Expression.TyContext :=
  { LContext.default with functions := Core.Factory, knownTypes := Core.KnownTypes }

private theorem addFactory_preserves {F added F' : Factory Core.CoreLParams}
    (success : F.addFactory added = .ok F') {fn : LFunc Core.CoreLParams}
    (found : F[fn.name.name]? = some fn) : F'[fn.name.name]? = some fn := by
  unfold Factory.addFactory Factory.tryAddAll at success
  rw [← Array.foldlM_toList] at success
  generalize added.toArray.toList = items at success
  induction items generalizing F with
  | nil =>
    obtain rfl := Except.ok.inj success
    exact found
  | cons next rest ih =>
    obtain ⟨fresh, continued⟩ := Factory.foldlM_tryPush_cons_inv next rest F F' success
    have different : next.name.name ≠ fn.name.name :=
      fun same => fresh (same ▸ Factory.getElem?_some_implies_mem found)
    have pushed := Factory.get?_pushIfNew_stable F next fn found different
    exact ih (by simpa [Factory.pushIfNew, fresh] using pushed) continued

private theorem decl_preserves_function
    {P : Core.Program} {C C' : Core.Expression.TyContext} {ts : Core.TypeSpec.TypeScopes}
    {decl : Core.Decl} (typed : Core.TypeSpec.DeclWellTyped P C ts decl C')
    {fn : LFunc Core.CoreLParams} (found : C.functions[fn.name.name]? = some fn) :
    C'.functions[fn.name.name]? = some fn := by
  cases typed <;> try exact found
  case type_con =>
    rename_i added
    simp only [LContext.addKnownTypeWithError, bind, Except.bind] at added
    elim_err added
    obtain rfl := Except.ok.inj added
    exact found
  case type_data =>
    rename_i added
    simp only [LContext.addMutualBlock, bind, Except.bind] at added
    elim_err added
    elim_err added
    elim_err added
    elim_err added with functions addedFunctions
    elim_err added
    obtain rfl := Except.ok.inj added
    exact addFactory_preserves addedFunctions found
  case func => exact (by assumption : Core.TypeSpec.FactoryExtendedBy _ _ _ _).preserves_old _ _ found
  case recFuncBlock =>
    exact (by assumption : Core.TypeSpec.FactoryExtendedBy _ _ _ _).preserves_old _ _ found

/-- Extract the procedure's typing derivation and the built-in signatures
in its declaration context from the declarative program typing. -/
theorem wellTypedProcedure_with_builtins
    {program : Core.Program} {name : String} {proc : Core.Procedure}
    (typed : Core.TypeSpec.ProgramWellTyped coreTypingContext [] program)
    (lookup : program.findProcByString? name = some proc) :
    ∃ C, Core.TypeSpec.ProcWellTyped program C [] proc ∧
      ∀ fn : LFunc Core.CoreLParams, Core.Factory[fn.name.name]? = some fn →
        C.functions[fn.name.name]? = some fn := by
  have member : proc ∈ program.decls.filterMap Core.Decl.getProc? := by
    cases program
    rw [findProc_eq_find] at lookup
    exact List.mem_of_find?_eq_some lookup
  obtain ⟨decl, present, isProcedure⟩ := List.mem_filterMap.mp member
  cases decl <;> simp [Core.Decl.getProc?] at isProcedure
  rename_i actual metadata
  subst actual
  clear member lookup
  obtain ⟨_, _, declsTyped⟩ := typed
  have initial : ∀ fn : LFunc Core.CoreLParams, Core.Factory[fn.name.name]? = some fn →
      coreTypingContext.functions[fn.name.name]? = some fn := fun _ h => h
  generalize ([] : Core.TypeSpec.TypeScopes) = scopes at declsTyped ⊢
  generalize coreTypingContext = starting at declsTyped initial
  generalize program.decls = decls at present declsTyped
  induction declsTyped with
  | nil => simp at present
  | cons _ _ _ _ first rest firstTyped _ ih =>
    rcases List.mem_cons.mp present with same | later
    · subst first
      cases firstTyped
      exact ⟨_, by assumption, initial⟩
    · exact ih (fun fn found => decl_preserves_function firstTyped (initial fn found)) later

/-- The procedure's visible factory extends the built-ins without changing
any existing binding. Scalar operator laws therefore apply in any of its models. -/
theorem builtinAtProcedure (program : Core.Program) (name : String)
    (fn : LFunc Core.CoreLParams)
    (builtin : Core.Factory[fn.name.name]? = some fn) :
    (program.factoryBeforeProcedure name)[fn.name.name]? = some fn := by
  have push (factory : Factory Core.CoreLParams) (next : LFunc Core.CoreLParams)
      (lookup : factory[fn.name.name]? = some fn) :
      (factory.pushIfNew next)[fn.name.name]? = some fn := by
    by_cases same : next.name.name = fn.name.name
    · have existsIn := Lambda.Factory.getElem?_some_implies_mem lookup
      have existsNext : next.name.name ∈ factory := same ▸ existsIn
      simpa [Lambda.Factory.pushIfNew, existsNext] using lookup
    · exact Lambda.Factory.get?_pushIfNew_stable factory next fn lookup same
  have extend (decl : Core.Decl) (factory : Factory Core.CoreLParams)
      (lookup : factory[fn.name.name]? = some fn) :
      (decl.addFunctionsToFactory factory)[fn.name.name]? = some fn := by
    cases decl <;> try exact lookup
    · exact push _ _ lookup
    · rename_i functions _
      unfold Core.Decl.addFunctionsToFactory
      induction functions generalizing factory with
      | nil => exact lookup
      | cons first rest ih => exact ih _ (push _ _ lookup)
  unfold Core.Program.factoryBeforeProcedure
  generalize Core.Factory = factory at builtin ⊢
  induction program.declsBeforeProcedure name generalizing factory with
  | nil => exact builtin
  | cons first rest ih => exact ih _ (extend first _ builtin)

private theorem eval_boolBin
    {factory : Core.Expression.Factory} {store : Core.CoreStore}
    {lhs rhs : Core.Expression.Expr} {a b : Bool}
    (fn : WFLFunc Core.CoreLParams) (result : Bool)
    (lookup : factory.factory[fn.func.name.name]? = some fn.func)
    (inputs : fn.func.inputs.map Prod.snd = [.bool, .bool])
    (output : fn.func.output = .bool)
    (operator : fn.opExpr = .op () fn.func.name (some (.arrow .bool (.arrow .bool .bool))))
    (concrete : fn.func.concreteEval.bind
      (fun evaluate => evaluate () [.boolConst () a, .boolConst () b]) = some (.boolConst () result))
    (left : Core.Expression.eval factory store lhs = some (.ofBool factory.model.tcInterp a))
    (right : Core.Expression.eval factory store rhs = some (.ofBool factory.model.tcInterp b)) :
    Core.Expression.eval factory store (.app () (.app () fn.opExpr lhs) rhs) =
      some (.ofBool factory.model.tcInterp result) := by
  have inputTyped : List.Rel₂ (LExpr.HasTypeA (T := Core.CoreLParams) [])
      [.boolConst () a, .boolConst () b]
      ((fn.func.inputs.map Prod.snd).map (LMonoTy.subst Subst.empty)) := by
    rw [inputs]
    exact .cons .const (.cons .const .nil)
  have resultTyped : LExpr.HasTypeA (T := Core.CoreLParams) []
      (.boolConst () result) (fn.func.output.subst Subst.empty) := by
    rw [output]
    exact .const
  let vars : FreeVarVal Core.CoreLParams factory.model.tcInterp := fun _ sort =>
    @default _ (@SortDenote.instInhabited factory.model.tcInterp factory.model.allInhabited sort)
  have evaluated := Core.opInterp_of_concreteEval factory.model lookup rfl concrete
    factory.tyVarVal vars inputTyped resultTyped
  rw [operator]
  apply Core.eval_app2_op (a := .bool) (b := .bool) (c := .bool) _ rfl rfl rfl left right
  have relay (inputTypes : List LMonoTy) (outputType : LMonoTy)
      (hi : inputTypes = [.bool, .bool]) (ho : outputType = .bool)
      (args : List.Rel₂ (LExpr.HasTypeA (T := Core.CoreLParams) [])
        [.boolConst () a, .boolConst () b] (inputTypes.map (LMonoTy.subst Subst.empty)))
      (out : LExpr.HasTypeA (T := Core.CoreLParams) []
        (.boolConst () result) (outputType.subst Subst.empty))
      (eq : LExpr.denote factory.model.tcInterp factory.model.opInterp vars factory.tyVarVal
        .nil (.boolConst () result) _ out =
        SortDenote.applyArgs factory.model.tcInterp
          (factory.model.opInterp fn.func.name.name
            (LSort.mkArrow ((outputType.subst Subst.empty).substTyVars factory.tyVarVal)
              ((inputTypes.map (LMonoTy.subst Subst.empty)).map
                (LMonoTy.substTyVars factory.tyVarVal))))
          (denoteArgs factory.model.tcInterp factory.model.opInterp vars factory.tyVarVal .nil
            [.boolConst () a, .boolConst () b] _ args)) :
      (factory.model.opInterp fn.func.name.name (LSort.mkArrow .bool [.bool, .bool]) : Bool → Bool → Bool)
        a b = result := by
    subst inputTypes outputType
    exact eq.symm
  exact relay _ _ inputs output inputTyped resultTyped evaluated

open _root_.Core in
theorem eval_boolNot {factory : Expression.Factory} {store : CoreStore}
    {expr : Expression.Expr} {b : Bool}
    (lookup : factory.factory["Bool.Not"]? = some (boolNotFunc (T := CoreLParams)).func)
    (eval : Expression.eval factory store expr = some (.ofBool factory.model.tcInterp b)) :
    Expression.eval factory store (.app () boolNotOp expr) =
      some (.ofBool factory.model.tcInterp (!b)) :=
  (LExpr.denoteEval_app_op_bool_iff (T := CoreLParams)).mpr ⟨b, eval,
    (boolNot_opInterp_of_lookup factory.model lookup b).symm⟩

open _root_.Core in
theorem eval_boolAnd {factory : Expression.Factory} {store : CoreStore}
    {lhs rhs : Expression.Expr} {a b : Bool}
    (lookup : factory.factory["Bool.And"]? = some (boolAndFunc (T := CoreLParams)).func)
    (left : Expression.eval factory store lhs = some (.ofBool factory.model.tcInterp a))
    (right : Expression.eval factory store rhs = some (.ofBool factory.model.tcInterp b)) :
    Expression.eval factory store (.app () (.app () boolAndOp lhs) rhs) =
      some (.ofBool factory.model.tcInterp (a && b)) :=
  eval_boolBin boolAndFunc (a && b) lookup rfl rfl rfl
    (by cases a <;> cases b <;> rfl) left right

open _root_.Core in
theorem eval_boolOr {factory : Expression.Factory} {store : CoreStore}
    {lhs rhs : Expression.Expr} {a b : Bool}
    (lookup : factory.factory["Bool.Or"]? = some (boolOrFunc (T := CoreLParams)).func)
    (left : Expression.eval factory store lhs = some (.ofBool factory.model.tcInterp a))
    (right : Expression.eval factory store rhs = some (.ofBool factory.model.tcInterp b)) :
    Expression.eval factory store (.app () (.app () boolOrOp lhs) rhs) =
      some (.ofBool factory.model.tcInterp (a || b)) :=
  eval_boolBin boolOrFunc (a || b) lookup rfl rfl rfl
    (by cases a <;> cases b <;> rfl) left right

open _root_.Core in
theorem eval_boolImplies {factory : Expression.Factory} {store : CoreStore}
    {lhs rhs : Expression.Expr} {a b : Bool}
    (lookup : factory.factory["Bool.Implies"]? = some (boolImpliesFunc (T := CoreLParams)).func)
    (left : Expression.eval factory store lhs = some (.ofBool factory.model.tcInterp a))
    (right : Expression.eval factory store rhs = some (.ofBool factory.model.tcInterp b)) :
    Expression.eval factory store (.app () (.app () boolImpliesOp lhs) rhs) =
      some (.ofBool factory.model.tcInterp (!a || b)) :=
  eval_boolBin boolImpliesFunc (!a || b) lookup rfl rfl rfl
    (by cases a <;> cases b <;> rfl) left right

open _root_.Core in
theorem eval_boolEquiv {factory : Expression.Factory} {store : CoreStore}
    {lhs rhs : Expression.Expr} {a b : Bool}
    (lookup : factory.factory["Bool.Equiv"]? = some (boolEquivFunc (T := CoreLParams)).func)
    (left : Expression.eval factory store lhs = some (.ofBool factory.model.tcInterp a))
    (right : Expression.eval factory store rhs = some (.ofBool factory.model.tcInterp b)) :
    Expression.eval factory store (.app () (.app () boolEquivOp lhs) rhs) =
      some (.ofBool factory.model.tcInterp (a == b)) :=
  eval_boolBin boolEquivFunc (a == b) lookup rfl rfl rfl
    (by cases a <;> cases b <;> rfl) left right

end Strata.Boole.Hoare
