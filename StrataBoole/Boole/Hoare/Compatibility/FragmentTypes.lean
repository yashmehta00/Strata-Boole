/-
Copyright Strata Contributors

SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Hoare.Compatibility.Syntax
import all StrataBoole.Boole.Hoare.Compatibility.Fragment
import all StrataBoole.Boole.Interp
import all StrataBoole.Boole.Semantics.Adequacy.SourceInterface
import all StrataBoole.Boole.Semantics.Adequacy.Lowering
import StrataBoole.Boole.LegacyGlobals

public section

namespace Strata.Boole.Hoare

open StrataDDM Strata.Boole

/-- `sourceSort` treats a nullary free type named `int` or `bool` as that
scalar. `bridgeType` does not, so a successful check forces `bridgeType` only
when the global context has no such alias. -/
def NoScalarAlias (names : GlobalContext) : Prop :=
  ∀ index, names.nameOf? index ≠ some "int" ∧ names.nameOf? index ≠ some "bool"

set_option linter.unusedSimpArgs false

private theorem pureSort_facts {sort : ValueType} {scope final : Scope} {out : ValueType}
    (run : (if (!scope.supportsType sort) = true then
        StateT.bind (reject (α := Unit) default
          (toString "Type has no interpretation in this model: " ++ toString (repr sort)))
          (fun (_ : Unit) => StateT.pure sort)
      else StateT.pure sort) scope = .ok (out, final)) :
    out = sort ∧ final = scope ∧ scope.supportsType sort = true := by
  split at run
  · simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.bind, StateT.lift,
      Functor.map, Except.map, Except.bind, StateT.pure] at run
  · rename_i blocked
    simp only [StateT.pure, pure, Except.pure] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    refine ⟨rfl, rfl, ?_⟩
    cases flag : scope.supportsType sort
    · exact False.elim (blocked (by simp [flag]))
    · rfl

private theorem con_not_scalar (name : String) (args : List ValueType)
    (notInt : name ≠ "int") (notBool : name ≠ "bool") :
    ValueType.con name args ≠ .int ∧ ValueType.con name args ≠ .bool := by
  constructor
  · intro same
    simp [ValueType.int] at same
    exact notInt same.1
  · intro same
    simp [ValueType.bool] at same
    exact notBool same.1

private theorem other_not_scalar {sort : ValueType}
    (different : sort ≠ .int ∧ sort ≠ .bool)
    {supports : ValueType → Bool} {scope : Scope}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    (same : scope.supportsType = supports) (supported : scope.supportsType sort = true) :
    False := by
  rcases onlyScalars _ (same ▸ supported) with h | h
  · exact different.1 h
  · exact different.2 h

set_option hygiene false in
macro "pure_scalar_absurd" : tactic => `(tactic|
  (rw [sourceSort.eq_def] at run
   dsimp only at run
   simp only [bind, StateT.bind, Except.bind, pure, Except.pure, get, getThe,
     MonadStateOf.get, StateT.get] at run
   obtain ⟨eq, _, supported⟩ := pureSort_facts run
   subst eq
   first
     | exact other_not_scalar (con_not_scalar "nat" [] (by decide) (by decide))
         onlyScalars same supported
     | exact other_not_scalar (con_not_scalar "real" [] (by decide) (by decide))
         onlyScalars same supported
     | exact other_not_scalar (con_not_scalar "string" [] (by decide) (by decide))
         onlyScalars same supported
     | exact other_not_scalar (con_not_scalar "regex" [] (by decide) (by decide))
         onlyScalars same supported))

set_option hygiene false in
macro "reject_sort" : tactic => `(tactic|
  (rw [sourceSort.eq_def] at run
   dsimp only at run
   simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, StateT.bind,
     Except.bind] at run))

private theorem sourceSort_bridgeType {supports : ValueType → Bool} {scope : Scope}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    (noAlias : NoScalarAlias scope.names) (same : scope.supportsType = supports)
    {ty : Boole.Type} {final : Scope} {out : ValueType}
    (run : sourceSort ty scope = .ok (out, final)) : bridgeType ty := by
  cases ty
  case int | bool => simp [bridgeType]
  case nat | real | string | regex => pure_scalar_absurd
  case tvar name =>
    rw [sourceSort.eq_def] at run
    dsimp only at run
    simp only [bind, StateT.bind, Except.bind, pure, Except.pure, get, getThe,
      MonadStateOf.get, StateT.get] at run
    obtain ⟨eq, _, supported⟩ := pureSort_facts run
    subst eq
    rcases onlyScalars _ (same ▸ supported) with h | h <;> cases h
  case bvar | W1 | W8 | W16 | W32 | W64 | W128 | Set => reject_sort
  case bv _ width =>
    cases width
    case W1 | W8 | W16 | W32 | W64 | W128 =>
      rw [sourceSort.eq_def] at run
      dsimp only at run
      simp only [bind, StateT.bind, Except.bind, pure, Except.pure, get, getThe,
        MonadStateOf.get, StateT.get] at run
      obtain ⟨eq, _, supported⟩ := pureSort_facts run
      subst eq
      rcases onlyScalars _ (same ▸ supported) with h | h <;> cases h
    all_goals reject_sort
  case arrow _ a b =>
    rw [sourceSort.eq_def] at run
    dsimp only at run
    obtain ⟨produced, mid, built, gated⟩ := split_run run
    rw [seq_eq_bind_map, map_eq_pure_bind] at built
    obtain ⟨left, s1, leftRun, rest⟩ := split_run built
    obtain ⟨raw, s0, aRun, pureArrow⟩ := split_run leftRun
    have := sourceSort_readOnly a _ _ _ aRun
    subst this
    simp only [pure, StateT.pure, Except.pure] at pureArrow
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj pureArrow)
    rw [map_eq_pure_bind] at rest
    obtain ⟨y, s3, bRun, pureApp⟩ := split_run rest
    have := sourceSort_readOnly b _ _ _ bRun
    subst this
    simp only [pure, StateT.pure, Except.pure] at pureApp
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj pureApp)
    simp only [bind, StateT.bind, Except.bind, pure, Except.pure, get, getThe,
      MonadStateOf.get, StateT.get] at gated
    obtain ⟨eq, _, supported⟩ := pureSort_facts gated
    subst eq
    exact other_not_scalar (con_not_scalar "arrow" _ (by decide) (by decide))
      onlyScalars same supported
  case Map _ value key =>
    rw [sourceSort.eq_def] at run
    dsimp only at run
    obtain ⟨produced, mid, built, gated⟩ := split_run run
    rw [seq_eq_bind_map, map_eq_pure_bind] at built
    obtain ⟨left, s1, leftRun, rest⟩ := split_run built
    obtain ⟨raw, s0, keyRun, pureMap⟩ := split_run leftRun
    have := sourceSort_readOnly key _ _ _ keyRun
    subst this
    simp only [pure, StateT.pure, Except.pure] at pureMap
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj pureMap)
    rw [map_eq_pure_bind] at rest
    obtain ⟨y, s3, valueRun, pureApp⟩ := split_run rest
    have := sourceSort_readOnly value _ _ _ valueRun
    subst this
    simp only [pure, StateT.pure, Except.pure] at pureApp
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj pureApp)
    simp only [bind, StateT.bind, Except.bind, pure, Except.pure, get, getThe,
      MonadStateOf.get, StateT.get] at gated
    obtain ⟨eq, _, supported⟩ := pureSort_facts gated
    subst eq
    exact other_not_scalar (con_not_scalar "Map" _ (by decide) (by decide))
      onlyScalars same supported
  case Sequence _ element =>
    rw [sourceSort.eq_def] at run
    dsimp only at run
    obtain ⟨produced, mid, built, gated⟩ := split_run run
    rw [map_eq_pure_bind] at built
    obtain ⟨raw, s0, elemRun, pureSeq⟩ := split_run built
    have := sourceSort_readOnly element _ _ _ elemRun
    subst this
    simp only [pure, StateT.pure, Except.pure] at pureSeq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj pureSeq)
    simp only [bind, StateT.bind, Except.bind, pure, Except.pure, get, getThe,
      MonadStateOf.get, StateT.get] at gated
    obtain ⟨eq, _, supported⟩ := pureSort_facts gated
    subst eq
    exact other_not_scalar (con_not_scalar "Sequence" _ (by decide) (by decide))
      onlyScalars same supported
  case fvar range index arguments =>
    rw [sourceSort.eq_def] at run
    dsimp only at run
    simp only [bind, StateT.bind, Except.bind, pure, Except.pure, get, getThe,
      MonadStateOf.get, StateT.get] at run
    cases found : scope.names.nameOf? index <;> simp [found] at run
    · simp [bind, reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, StateT.bind,
        Except.bind, Functor.map, Except.map, StateT.get, pure, Except.pure] at run
    · rename_i name
      obtain ⟨sorts, mid, mapped, rest⟩ := split_run run
      have midEq := readOnly_mapM _ sourceSort (fun item _ => sourceSort_readOnly item) _ _ _ mapped
      subst midEq
      split at rest
      · cases sorts with
        | nil =>
          simp [bind, reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, StateT.bind,
            Except.bind, Functor.map, Except.map, StateT.get, pure] at rest
        | cons element tail =>
          cases tail with
          | cons _ _ =>
            simp [bind, reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, StateT.bind,
              Except.bind, Functor.map, Except.map, StateT.get, pure] at rest
          | nil =>
            simp only [StateT.pure, StateT.bind, Except.bind, StateT.get, bind, pure,
              Except.pure] at rest
            split at rest
            · simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, StateT.bind,
                Except.bind, bind, Functor.map, Except.map] at rest
            · rename_i kept
              simp only [StateT.pure, Except.pure] at rest
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj rest)
              have supported : mid.supportsType (ValueType.set element) = true := by
                cases flag : mid.supportsType (ValueType.set element)
                · exact False.elim (kept (by simp [flag]))
                · rfl
              exact other_not_scalar (con_not_scalar "Set" _ (by decide) (by decide))
                onlyScalars same supported
      · simp only [StateT.pure, StateT.bind, Except.bind, StateT.get, bind, pure,
          Except.pure] at rest
        split at rest
        · simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, StateT.bind,
            Except.bind, bind, Functor.map, Except.map] at rest
        · rename_i kept
          simp only [StateT.pure, Except.pure] at rest
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj rest)
          have supported : mid.supportsType (ValueType.named name sorts) = true := by
            cases flag : mid.supportsType (ValueType.named name sorts)
            · exact False.elim (kept (by simp [flag]))
            · rfl
          rcases onlyScalars _ (same ▸ supported) with h | h
          · simp [ValueType.named, ValueType.int] at h
            exact (noAlias index).1 (found ▸ congrArg some h.1)
          · simp [ValueType.named, ValueType.bool] at h
            exact (noAlias index).2 (found ▸ congrArg some h.1)

private theorem interpExpr_readOnly (I : Interpretation) (e : Boole.Expr) :
    ReadOnly (interpExpr I e) := by
  cases e
  all_goals rw [interpExpr.eq_def]
  all_goals
    repeat' first
      | exact readOnly_pure _
      | exact readOnly_reject _ _
      | exact readOnly_get
      | exact sourceSort_readOnly _
      | exact interpExpr_readOnly I _
      | apply ReadOnly.bind
      | dsimp only
      | (split <;> skip)
      | (intro value)
termination_by sizeOf e
decreasing_by all_goals simp_all <;> omega

private theorem peel {α β : Type} {action : InterpM α} {next : α → InterpM β}
    {initial final : Scope} {result : β} (kept : ReadOnly action)
    (run : (action >>= next) initial = .ok (result, final)) :
    ∃ value, action initial = .ok (value, initial) ∧
      next value initial = .ok (result, final) := by
  obtain ⟨value, middle, first, second⟩ := split_run run
  have eq := kept _ _ _ first
  subst eq
  exact ⟨value, first, second⟩

set_option maxHeartbeats 2000000 in
private theorem checked_expr_bridgeTyped {supports : ValueType → Bool}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {e : Boole.Expr} {scope final : Scope} {out : Unit}
    (noAlias : NoScalarAlias scope.names) (same : scope.supportsType = supports)
    (run : interpExpr (checkingInterpretation supports) e scope = .ok (out, final)) :
    BridgeTyped e := by
  cases e
  all_goals rw [interpExpr.eq_def] at run
  all_goals dsimp only at run
  case natToInt => exact .natToInt _ _
  case strLit => exact .strLit _ _
  case bv1Lit => exact .bv1Lit _ _
  case bv8Lit => exact .bv8Lit _ _
  case bv16Lit => exact .bv16Lit _ _
  case bv32Lit => exact .bv32Lit _ _
  case bv64Lit => exact .bv64Lit _ _
  case bv128Lit => exact .bv128Lit _ _
  case btrue => exact .btrue _
  case bfalse => exact .bfalse _
  case fvar => exact .fvar _ _
  case bvar => exact .bvar _ _
  case not _ a =>
    obtain ⟨_, sub, _⟩ := peel (interpExpr_readOnly _ a) run
    exact .not _ (checked_expr_bridgeTyped onlyScalars noAlias same sub)
  case app => exact .app _ _ _
  case and _ a b | or _ a b | implies _ a b | equiv _ a b =>
    obtain ⟨_, aRun, rest⟩ := peel (interpExpr_readOnly _ a) run
    obtain ⟨_, bRun, _⟩ := peel (interpExpr_readOnly _ b) rest
    first
      | exact .and _ (checked_expr_bridgeTyped onlyScalars noAlias same aRun)
          (checked_expr_bridgeTyped onlyScalars noAlias same bRun)
      | exact .or _ (checked_expr_bridgeTyped onlyScalars noAlias same aRun)
          (checked_expr_bridgeTyped onlyScalars noAlias same bRun)
      | exact .implies _ (checked_expr_bridgeTyped onlyScalars noAlias same aRun)
          (checked_expr_bridgeTyped onlyScalars noAlias same bRun)
      | exact .equiv _ (checked_expr_bridgeTyped onlyScalars noAlias same aRun)
          (checked_expr_bridgeTyped onlyScalars noAlias same bRun)
  case neg_expr _ ty a | old _ ty a =>
    obtain ⟨_, sorted, rest⟩ := peel (sourceSort_readOnly ty) run
    have typed := sourceSort_bridgeType onlyScalars noAlias same sorted
    obtain ⟨_, sub, _⟩ := peel (interpExpr_readOnly _ a) rest
    first
      | exact .neg _ typed (checked_expr_bridgeTyped onlyScalars noAlias same sub)
      | exact .old _ typed (checked_expr_bridgeTyped onlyScalars noAlias same sub)
  case add_expr _ ty a b | sub_expr _ ty a b | mul_expr _ ty a b
    | le _ ty a b | lt _ ty a b | ge _ ty a b | gt _ ty a b
    | equal _ ty a b | not_equal _ ty a b =>
    obtain ⟨_, sorted, rest⟩ := peel (sourceSort_readOnly ty) run
    have typed := sourceSort_bridgeType onlyScalars noAlias same sorted
    obtain ⟨_, aRun, rest⟩ := peel (interpExpr_readOnly _ a) rest
    obtain ⟨_, bRun, _⟩ := peel (interpExpr_readOnly _ b) rest
    first
      | exact .add _ typed (checked_expr_bridgeTyped onlyScalars noAlias same aRun)
          (checked_expr_bridgeTyped onlyScalars noAlias same bRun)
      | exact .sub _ typed (checked_expr_bridgeTyped onlyScalars noAlias same aRun)
          (checked_expr_bridgeTyped onlyScalars noAlias same bRun)
      | exact .mul _ typed (checked_expr_bridgeTyped onlyScalars noAlias same aRun)
          (checked_expr_bridgeTyped onlyScalars noAlias same bRun)
      | exact .le _ typed (checked_expr_bridgeTyped onlyScalars noAlias same aRun)
          (checked_expr_bridgeTyped onlyScalars noAlias same bRun)
      | exact .lt _ typed (checked_expr_bridgeTyped onlyScalars noAlias same aRun)
          (checked_expr_bridgeTyped onlyScalars noAlias same bRun)
      | exact .ge _ typed (checked_expr_bridgeTyped onlyScalars noAlias same aRun)
          (checked_expr_bridgeTyped onlyScalars noAlias same bRun)
      | exact .gt _ typed (checked_expr_bridgeTyped onlyScalars noAlias same aRun)
          (checked_expr_bridgeTyped onlyScalars noAlias same bRun)
      | exact .equal _ typed (checked_expr_bridgeTyped onlyScalars noAlias same aRun)
          (checked_expr_bridgeTyped onlyScalars noAlias same bRun)
      | exact .notEqual _ typed (checked_expr_bridgeTyped onlyScalars noAlias same aRun)
          (checked_expr_bridgeTyped onlyScalars noAlias same bRun)
  case «if» _ ty c yes no =>
    obtain ⟨_, sorted, rest⟩ := peel (sourceSort_readOnly ty) run
    have typed := sourceSort_bridgeType onlyScalars noAlias same sorted
    obtain ⟨_, cRun, rest⟩ := peel (interpExpr_readOnly _ c) rest
    obtain ⟨_, yesRun, rest⟩ := peel (interpExpr_readOnly _ yes) rest
    obtain ⟨_, noRun, _⟩ := peel (interpExpr_readOnly _ no) rest
    exact .ite _ typed (checked_expr_bridgeTyped onlyScalars noAlias same cRun)
      (checked_expr_bridgeTyped onlyScalars noAlias same yesRun)
      (checked_expr_bridgeTyped onlyScalars noAlias same noRun)
  case nat_fromInt _ a | nat_toInt _ a =>
    obtain ⟨_, sorted, _⟩ := peel (sourceSort_readOnly _) run
    simpa [bridgeType] using sourceSort_bridgeType onlyScalars noAlias same sorted
  case nat_add _ a b | nat_sub _ a b | nat_mul _ a b | nat_div _ a b | nat_mod _ a b
    | nat_lt _ a b | nat_le _ a b | nat_gt _ a b | nat_ge _ a b
    | map_get _ _ _ _ _ | map_set _ _ _ _ _ _ | map_const _ _ _ _
    | seq_empty _ _ | seq_length _ _ _ | seq_append _ _ _ _ | seq_build _ _ _ _ =>
    obtain ⟨_, sorted, _⟩ := peel (sourceSort_readOnly _) run
    simpa [bridgeType] using sourceSort_bridgeType onlyScalars noAlias same sorted
  case seq_empty_int =>
    obtain ⟨_, sorted, _⟩ := peel (sourceSort_readOnly _) run
    simpa [bridgeType] using sourceSort_bridgeType onlyScalars noAlias same sorted
  all_goals
    simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, StateT.bind,
      Except.bind, Functor.map, Except.map] at run
termination_by sizeOf e
decreasing_by all_goals simp_all <;> omega

/-- A loop measure the checker actually evaluates. -/
def BridgeMeasure : Option (BooleDDM.Measure SourceRange) → Prop
  | none => True
  | some (.measure_mk _ expression) => BridgeTyped expression

/-- Loop invariants the checker evaluates, in source order. -/
def BridgeInvariants : BooleDDM.Invariants SourceRange → Prop
  | .nilInvariants _ => True
  | .consInvariants _ _ expression rest => BridgeTyped expression ∧ BridgeInvariants rest

mutual

/-- A statement whose interpreter-visited expressions and sub-blocks stay in the bridge fragment. -/
inductive BridgeStatement : BooleDDM.Statement SourceRange → Prop where
  | var (r a ds) : BridgeStatement (.varStatement r a ds)
  | init (r a ty name expression) : BridgeTyped expression →
      BridgeStatement (.initStatement r a ty name expression)
  | assign (r a b lr name expression) : BridgeTyped expression →
      BridgeStatement (.assign r a b (.lhsIdent lr name) expression)
  | havoc (r a name) : BridgeStatement (.havoc_statement r a name)
  | assert (r a label expression) : BridgeTyped expression →
      BridgeStatement (.assert r a label expression)
  | assume (r a label expression) : BridgeTyped expression →
      BridgeStatement (.assume r a label expression)
  | ifDet0 (r a g expression yes n) : BridgeTyped expression → BridgeBlock yes →
      BridgeStatement (.if_statement r a (.condDet g expression) yes (.else0 n))
  | ifDet1 (r a g expression yes n body) : BridgeTyped expression → BridgeBlock yes → BridgeBlock body →
      BridgeStatement (.if_statement r a (.condDet g expression) yes (.else1 n body))
  | ifNondet0 (r a g yes n) : BridgeBlock yes →
      BridgeStatement (.if_statement r a (.condNondet g) yes (.else0 n))
  | ifNondet1 (r a g yes n body) : BridgeBlock yes → BridgeBlock body →
      BridgeStatement (.if_statement r a (.condNondet g) yes (.else1 n body))
  | whileDet (r a g expression decreases invariants body) :
      BridgeTyped expression → BridgeMeasure decreases.val → BridgeInvariants invariants →
      BridgeBlock body →
      BridgeStatement (.while_statement r a (.condDet g expression) decreases invariants body)
  | whileNondet (r a g decreases invariants body) :
      BridgeMeasure decreases.val → BridgeInvariants invariants → BridgeBlock body →
      BridgeStatement (.while_statement r a (.condNondet g) decreases invariants body)
  | block (r a name body) : BridgeBlock body → BridgeStatement (.block_statement r a name body)
  | exit (r a name) : BridgeStatement (.exit_statement r a name)

/-- Every statement of a block satisfies `BridgeStatement`. -/
inductive BridgeBlock : BooleDDM.Block SourceRange → Prop where
  | block {r r' ss} : (∀ s ∈ ss.toList, BridgeStatement s) → BridgeBlock (.block r ⟨r', ss⟩)

end

theorem BridgeBlock.statements {r r' : SourceRange} {ss : Array (BooleDDM.Statement SourceRange)}
    (h : BridgeBlock (.block r ⟨r', ss⟩)) : ∀ s ∈ ss.toList, BridgeStatement s := by
  cases h
  assumption

theorem BridgeStatement.init_typed {r a ty name expression}
    (h : BridgeStatement (.initStatement r a ty name expression)) : BridgeTyped expression := by
  cases h; assumption

theorem BridgeStatement.assign_typed {r a b lr name expression}
    (h : BridgeStatement (.assign r a b (.lhsIdent lr name) expression)) : BridgeTyped expression := by
  cases h; assumption

theorem BridgeStatement.assert_typed {r a label expression}
    (h : BridgeStatement (.assert r a label expression)) : BridgeTyped expression := by
  cases h; assumption

theorem BridgeStatement.assume_typed {r a label expression}
    (h : BridgeStatement (.assume r a label expression)) : BridgeTyped expression := by
  cases h; assumption

theorem BridgeStatement.ifDet0_inv {r a g expression yes n}
    (h : BridgeStatement (.if_statement r a (.condDet g expression) yes (.else0 n))) :
    BridgeTyped expression ∧ BridgeBlock yes := by
  cases h; exact ⟨by assumption, by assumption⟩

theorem BridgeStatement.ifDet1_inv {r a g expression yes n body}
    (h : BridgeStatement (.if_statement r a (.condDet g expression) yes (.else1 n body))) :
    BridgeTyped expression ∧ BridgeBlock yes ∧ BridgeBlock body := by
  cases h; exact ⟨by assumption, by assumption, by assumption⟩

theorem BridgeStatement.ifNondet0_inv {r a g yes n}
    (h : BridgeStatement (.if_statement r a (.condNondet g) yes (.else0 n))) : BridgeBlock yes := by
  cases h; assumption

theorem BridgeStatement.ifNondet1_inv {r a g yes n body}
    (h : BridgeStatement (.if_statement r a (.condNondet g) yes (.else1 n body))) :
    BridgeBlock yes ∧ BridgeBlock body := by
  cases h; exact ⟨by assumption, by assumption⟩

theorem BridgeStatement.whileDet_inv {r a g expression decreases invariants body}
    (h : BridgeStatement (.while_statement r a (.condDet g expression) decreases invariants body)) :
    BridgeTyped expression ∧ BridgeMeasure decreases.val ∧ BridgeInvariants invariants ∧
      BridgeBlock body := by
  cases h; exact ⟨by assumption, by assumption, by assumption, by assumption⟩

theorem BridgeStatement.whileNondet_inv {r a g decreases invariants body}
    (h : BridgeStatement (.while_statement r a (.condNondet g) decreases invariants body)) :
    BridgeMeasure decreases.val ∧ BridgeInvariants invariants ∧ BridgeBlock body := by
  cases h; exact ⟨by assumption, by assumption, by assumption⟩

theorem BridgeStatement.block_body {r a name body}
    (h : BridgeStatement (.block_statement r a name body)) : BridgeBlock body := by
  cases h; assumption

/-- Requires and ensures conditions of one specification clause. -/
def BridgeSpecElt : BooleDDM.SpecElt SourceRange → Prop
  | .requires_spec _ _ _ expression | .ensures_spec _ _ _ expression => BridgeTyped expression
  | .modifies_spec _ _ => True

/-- Every requires and ensures expression of a procedure specification. -/
def BridgeSpec : Option (BooleDDM.Spec SourceRange) → Prop
  | none => True
  | some (.spec_mk _ elements) => ∀ element ∈ elements.val.toList, BridgeSpecElt element

private theorem addLocal_iface {range : SourceRange} {name : String} {ty : Boole.Type}
    {initial final : Scope} {binding : Binding}
    (success : addLocal range name ty initial = .ok (binding, final)) :
    final.names = initial.names ∧ final.supportsType = initial.supportsType := by
  unfold addLocal at success
  obtain ⟨_, middle, resolved, added⟩ := split_run success
  have := sourceSort_readOnly ty _ _ _ resolved
  subst middle
  obtain ⟨_, afterFresh, checked, installed⟩ := split_run added
  have restored := (fresh_names checked).2.2
  subst afterFresh
  obtain ⟨_, mid, modified, ended⟩ := split_run installed
  simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, StateT.pure,
    Except.pure] at modified
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj modified)
  simp only [pure, StateT.pure, Except.pure] at ended
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj ended)
  exact ⟨rfl, rfl⟩

private theorem pure_state {α : Type} {value : α} {scope final : Scope} {out : α}
    (run : (pure value : InterpM α) scope = .ok (out, final)) : final = scope := by
  simp only [pure, StateT.pure, Except.pure] at run
  exact (congrArg Prod.snd (Except.ok.inj run)).symm

private theorem resolveVariable_readOnly (range : SourceRange) (name : String) (writing : Bool) :
    ReadOnly (resolveVariable range name writing) := by
  unfold resolveVariable
  apply ReadOnly.bind readOnly_get
  intro _
  repeat' first
    | exact readOnly_pure _
    | exact readOnly_reject _ _
    | (split <;> skip)

private theorem condition_readOnly (I : Interpretation) (guard : BooleDDM.ExprOrNondet SourceRange) :
    ReadOnly (condition I guard) := by
  cases guard
  · exact (interpExpr_readOnly I _).bind fun _ => readOnly_pure _
  · exact readOnly_pure _

private theorem checkInvariants_readOnly (I : Interpretation) (invariants : BooleDDM.Invariants SourceRange) :
    ReadOnly (checkInvariants I invariants) := by
  induction invariants with
  | nilInvariants => exact readOnly_pure ()
  | consInvariants _ _ expression _ ih => exact (interpExpr_readOnly I expression).bind fun _ => ih

private theorem withScope_readOnly (action : InterpM α) : ReadOnly (withScope action) :=
  fun _ _ _ success => withScope_restores success

private theorem interpBlock_restores (I : Interpretation) (block : BooleDDM.Block SourceRange) :
    ReadOnly (interpBlock I block) := by
  intro _ _ _ success
  unfold interpBlock at success
  exact withScope_restores success

private theorem declarations_iface (I : Interpretation)
    (declarations : List (BooleDDM.Bind SourceRange)) (range : SourceRange)
    (entry final : Scope) (body : I.Statement)
    (success : (forIn declarations I.skip (fun (declaration : BooleDDM.Bind SourceRange)
        (result : I.Statement) =>
        match declaration with
        | .bind_mk _ name _ ty => do
          let binding ← addLocal range name.val ty
          pure (ForInStep.yield (I.seq result (I.declare binding none))))) entry =
        Except.ok (body, final)) :
    final.names = entry.names ∧ final.supportsType = entry.supportsType := by
  apply forIn_invariant _ _ (fun scope _ =>
      scope.names = entry.names ∧ scope.supportsType = entry.supportsType) ?_ _ _ _ _ ⟨rfl, rfl⟩ success
  intro declaration _ state _ next kept ran
  cases declaration
  simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
  split at ran
  · contradiction
  · rename_i _ added
    obtain ⟨names, types⟩ := addLocal_iface added
    have equal := Except.ok.inj ran
    exact ⟨(congrArg (fun result : _ × Scope => result.2.names) equal).symm.trans (names.trans kept.1),
      (congrArg (fun result : _ × Scope => result.2.supportsType) equal).symm.trans (types.trans kept.2)⟩

private theorem checked_invariants {supports : ValueType → Bool}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {inv : BooleDDM.Invariants SourceRange} {scope final : Scope} {out : Unit}
    (noAlias : NoScalarAlias scope.names) (same : scope.supportsType = supports)
    (run : checkInvariants (checkingInterpretation supports) inv scope = .ok (out, final)) :
    BridgeInvariants inv ∧ final = scope := by
  induction inv with
  | nilInvariants _ =>
    rw [checkInvariants] at run
    exact ⟨trivial, pure_state run⟩
  | consInvariants _ _ expression _ ih =>
    rw [checkInvariants] at run
    obtain ⟨_, exprRun, restRun⟩ := peel (interpExpr_readOnly _ expression) run
    obtain ⟨restTyped, eq⟩ := ih restRun
    exact ⟨⟨checked_expr_bridgeTyped onlyScalars noAlias same exprRun, restTyped⟩, eq⟩

private theorem det_guard {supports : ValueType → Bool}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {g : SourceRange} {expression : Boole.Expr} {scope final : Scope} {out}
    (noAlias : NoScalarAlias scope.names) (same : scope.supportsType = supports)
    (run : condition (checkingInterpretation supports) (.condDet g expression) scope = .ok (out, final)) :
    BridgeTyped expression := by
  rw [condition] at run
  obtain ⟨_, exprRun, _⟩ := peel (interpExpr_readOnly _ expression) run
  exact checked_expr_bridgeTyped onlyScalars noAlias same exprRun

private theorem kept_scope {scope final : Scope} (eq : final = scope) :
    final.supportsType = scope.supportsType ∧ final.names = scope.names := by
  cases eq
  exact ⟨rfl, rfl⟩

private theorem block_statements_smaller (r r' : SourceRange)
    (ss : Array (BooleDDM.Statement SourceRange)) :
    sizeOf ss.toList < sizeOf
      (BooleDDM.Block.block r (⟨r', ss⟩ : Ann (Array (BooleDDM.Statement SourceRange)) SourceRange)) := by
  have : sizeOf ss = 1 + sizeOf ss.toList := rfl
  first
    | simp [BooleDDM.Block.block.sizeOf_spec, StrataDDM.Ann.mk.sizeOf_spec, this]
    | simp [BooleDDM.Block.block.sizeOf_spec, this]
    | fail "no spec"
  omega

set_option maxHeartbeats 2000000 in
mutual

private theorem checked_stmt {supports : ValueType → Bool}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {names : GlobalContext} {statement : BooleDDM.Statement SourceRange} {scope final : Scope} {out : Unit}
    (noAlias : NoScalarAlias names) (types : scope.supportsType = supports)
    (sameNames : scope.names = names)
    (run : interpStmt (checkingInterpretation supports) statement scope = .ok (out, final)) :
    BridgeStatement statement ∧ final.supportsType = scope.supportsType ∧
      final.names = scope.names := by
  have alias : NoScalarAlias scope.names := sameNames.symm ▸ noAlias
  cases statement
  case varStatement range _ declarations =>
    rw [interpStmt.eq_def] at run
    dsimp only at run
    obtain ⟨_, mid, looped, done⟩ := split_run run
    obtain ⟨namesEq, typesEq⟩ :=
      declarations_iface _ (bindings declarations) range scope mid _ looped
    have eq := pure_state done
    rw [eq]
    exact ⟨.var _ _ _, typesEq, namesEq⟩
  case initStatement _ _ _ _ expression =>
    rw [interpStmt.eq_def] at run
    dsimp only at run
    obtain ⟨_, exprRun, rest⟩ := peel (interpExpr_readOnly _ expression) run
    obtain ⟨_, _, added, done⟩ := split_run rest
    obtain ⟨namesEq, typesEq⟩ := addLocal_iface added
    have eq := pure_state done
    rw [eq]
    exact ⟨.init _ _ _ _ _ (checked_expr_bridgeTyped onlyScalars alias types exprRun), typesEq, namesEq⟩
  case assign _ _ _ lhs expression =>
    rw [interpStmt.eq_def] at run
    cases lhs with
    | lhsIdent _ _ =>
      dsimp only at run
      obtain ⟨_, mid, resolved, rest⟩ := split_run run
      have := resolveVariable_readOnly _ _ _ _ _ _ resolved
      subst mid
      obtain ⟨_, exprRun, done⟩ := peel (interpExpr_readOnly _ expression) rest
      exact ⟨.assign _ _ _ _ _ _ (checked_expr_bridgeTyped onlyScalars alias types exprRun),
        kept_scope (pure_state done)⟩
    | lhsArray _ _ _ _ =>
      dsimp only at run
      simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, StateT.bind,
        Except.bind, Functor.map, Except.map] at run
  case havoc_statement _ _ _ =>
    rw [interpStmt.eq_def] at run
    dsimp only at run
    obtain ⟨_, mid, resolved, done⟩ := split_run run
    have := resolveVariable_readOnly _ _ _ _ _ _ resolved
    subst mid
    exact ⟨.havoc _ _ _, kept_scope (pure_state done)⟩
  case assert _ annotations _ expression =>
    cases ann : annotations.val with
    | some _ =>
      rw [interpStmt.eq_def] at run
      simp [ann, Option.isSome, reject, bind, StateT.bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw, StateT.lift, Function.comp_apply] at run
    | none =>
      rw [interpStmt.eq_def] at run
      simp only [ann, Option.isSome, Bool.false_eq_true, ite_false, bind, StateT.bind, Except.bind] at run
      obtain ⟨_, exprRun, done⟩ := peel (interpExpr_readOnly _ expression) run
      exact ⟨.assert _ _ _ _ (checked_expr_bridgeTyped onlyScalars alias types exprRun),
        kept_scope (pure_state done)⟩
  case assume _ _ _ expression =>
    rw [interpStmt.eq_def] at run
    dsimp only at run
    obtain ⟨_, exprRun, done⟩ := peel (interpExpr_readOnly _ expression) run
    exact ⟨.assume _ _ _ _ (checked_expr_bridgeTyped onlyScalars alias types exprRun),
      kept_scope (pure_state done)⟩
  case if_statement r a guard yes no =>
    rw [interpStmt.eq_def] at run
    dsimp only at run
    obtain ⟨_, guardRun, rest⟩ := peel (condition_readOnly _ guard) run
    obtain ⟨_, yesRun, rest⟩ := peel (interpBlock_restores _ yes) rest
    obtain ⟨yesTyped, _, _⟩ := checked_block onlyScalars noAlias types sameNames yesRun
    cases no with
    | else0 n =>
      simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at rest
      have eq := (congrArg Prod.snd (Except.ok.inj rest)).symm
      subst eq
      cases guard with
      | condDet g expression =>
        exact ⟨.ifDet0 r a g expression yes n (det_guard onlyScalars alias types guardRun) yesTyped,
          rfl, rfl⟩
      | condNondet g => exact ⟨.ifNondet0 r a g yes n yesTyped, rfl, rfl⟩
    | else1 n body =>
      obtain ⟨_, noRun, done⟩ := peel (interpBlock_restores _ body) rest
      obtain ⟨noTyped, _, _⟩ := checked_block onlyScalars noAlias types sameNames noRun
      simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at done
      have eq := (congrArg Prod.snd (Except.ok.inj done)).symm
      subst eq
      cases guard with
      | condDet g expression =>
        exact ⟨.ifDet1 r a g expression yes n body (det_guard onlyScalars alias types guardRun)
          yesTyped noTyped, rfl, rfl⟩
      | condNondet g => exact ⟨.ifNondet1 r a g yes n body yesTyped noTyped, rfl, rfl⟩
  case while_statement r a guard decreases invariants body =>
    rw [interpStmt.eq_def] at run
    dsimp only at run
    obtain ⟨_, guardRun, rest⟩ := peel (condition_readOnly _ guard) run
    cases mv : decreases.val with
    | none =>
      simp only [mv] at rest
      obtain ⟨_, invRun, rest⟩ := peel (checkInvariants_readOnly _ invariants) rest
      obtain ⟨invTyped, _⟩ := checked_invariants onlyScalars alias types invRun
      obtain ⟨_, bodyRun, done⟩ := peel (interpBlock_restores _ body) rest
      obtain ⟨bodyTyped, _, _⟩ := checked_block onlyScalars noAlias types sameNames bodyRun
      simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at done
      have eq := (congrArg Prod.snd (Except.ok.inj done)).symm
      subst eq
      cases guard with
      | condDet g expression =>
        exact ⟨.whileDet r a g expression decreases invariants body
          (det_guard onlyScalars alias types guardRun) (by simp [BridgeMeasure, mv]) invTyped bodyTyped,
          rfl, rfl⟩
      | condNondet g =>
        exact ⟨.whileNondet r a g decreases invariants body (by simp [BridgeMeasure, mv])
          invTyped bodyTyped, rfl, rfl⟩
    | some m =>
      cases m with
      | measure_mk _ expression =>
        simp only [mv] at rest
        obtain ⟨_, exprRun, rest⟩ := peel (interpExpr_readOnly _ expression) rest
        have measured : BridgeMeasure decreases.val := by
          simpa [BridgeMeasure, mv] using checked_expr_bridgeTyped onlyScalars alias types exprRun
        obtain ⟨_, invRun, rest⟩ := peel (checkInvariants_readOnly _ invariants) rest
        obtain ⟨invTyped, _⟩ := checked_invariants onlyScalars alias types invRun
        obtain ⟨_, bodyRun, done⟩ := peel (interpBlock_restores _ body) rest
        obtain ⟨bodyTyped, _, _⟩ := checked_block onlyScalars noAlias types sameNames bodyRun
        simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at done
        have eq := (congrArg Prod.snd (Except.ok.inj done)).symm
        subst eq
        cases guard with
        | condDet g guardExpr =>
          exact ⟨.whileDet r a g guardExpr decreases invariants body
            (det_guard onlyScalars alias types guardRun) measured invTyped bodyTyped, rfl, rfl⟩
        | condNondet g =>
          exact ⟨.whileNondet r a g decreases invariants body measured invTyped bodyTyped, rfl, rfl⟩
  case block_statement _ _ name body =>
    rw [interpStmt.eq_def] at run
    dsimp only at run
    obtain ⟨_, saved, done⟩ := peel (withScope_readOnly _) run
    obtain ⟨_, inner⟩ := withScope_success saved
    simp only [bind, StateT.bind, Except.bind, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet] at inner
    obtain ⟨typed, _, _⟩ := checked_block onlyScalars noAlias (by simp [types]) (by simp [sameNames]) inner
    exact ⟨.block _ _ _ _ typed, kept_scope (pure_state done)⟩
  case exit_statement _ _ _ =>
    rw [interpStmt.eq_def] at run
    dsimp only at run
    obtain ⟨_, mid, got, rest⟩ := split_run run
    have := readOnly_get _ _ _ got
    subst mid
    split at rest
    · simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, StateT.bind,
        Except.bind, Functor.map, Except.map] at rest
    · exact ⟨.exit _ _ _, kept_scope (pure_state rest)⟩
  all_goals
    rw [interpStmt.eq_def] at run
    dsimp only at run
    simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, StateT.bind,
      Except.bind, Functor.map, Except.map] at run
  termination_by sizeOf statement

private theorem checked_stmts {supports : ValueType → Bool}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {names : GlobalContext} (statements : List (BooleDDM.Statement SourceRange)) {scope final : Scope}
    {out : Unit} (noAlias : NoScalarAlias names) (types : scope.supportsType = supports)
    (sameNames : scope.names = names)
    (run : interpStmts (checkingInterpretation supports) statements scope = .ok (out, final)) :
    (∀ s ∈ statements, BridgeStatement s) ∧ final.supportsType = scope.supportsType ∧
      final.names = scope.names := by
  match statements with
  | [] =>
    rw [interpStmts.eq_def] at run
    exact ⟨fun _ mem => by simp at mem, kept_scope (pure_state run)⟩
  | statement :: rest =>
    rw [interpStmts.eq_def] at run
    dsimp only at run
    obtain ⟨_, mid, headRun, tail⟩ := split_run run
    obtain ⟨typed, midTypes, midNames⟩ :=
      checked_stmt onlyScalars noAlias types sameNames headRun
    obtain ⟨_, _, tailRun, done⟩ := split_run tail
    have midSupport : mid.supportsType = supports := midTypes.trans types
    have midNamesEq : mid.names = names := midNames.trans sameNames
    obtain ⟨restTyped, lastTypes, lastNames⟩ :=
      checked_stmts onlyScalars rest noAlias midSupport midNamesEq tailRun
    have eq := pure_state done
    rw [eq]
    refine ⟨?_, lastTypes.trans midTypes, lastNames.trans midNames⟩
    intro s mem
    rcases List.mem_cons.mp mem with rfl | later
    · exact typed
    · exact restTyped s later
  termination_by sizeOf statements

private theorem checked_block {supports : ValueType → Bool}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {names : GlobalContext} {block : BooleDDM.Block SourceRange} {scope final : Scope} {out : Unit}
    (noAlias : NoScalarAlias names) (types : scope.supportsType = supports)
    (sameNames : scope.names = names)
    (run : interpBlock (checkingInterpretation supports) block scope = .ok (out, final)) :
    BridgeBlock block ∧ final.supportsType = scope.supportsType ∧ final.names = scope.names := by
  have restored := interpBlock_restores _ block _ _ _ run
  unfold interpBlock at run
  obtain ⟨_, inner⟩ := withScope_success run
  cases block with
  | block r ann =>
    cases ann with
    | mk r' ss =>
      dsimp only at inner
      obtain ⟨_, _, stmtsRun, _⟩ := split_run inner
      obtain ⟨all, _, _⟩ := checked_stmts onlyScalars ss.toList noAlias types sameNames stmtsRun
      exact ⟨.block all, kept_scope restored⟩
  termination_by sizeOf block
  decreasing_by
    subst_eqs
    exact block_statements_smaller r r' ss

end

private theorem forIn_preservesScope {α β : Type} (items : List α)
    (step : α → β → InterpM (ForInStep β))
    (stepPreserves : ∀ item before state control after,
      step item before state = .ok (control, after) → after = state)
    (before : β) (entry final : Scope) (result : β)
    (ran : forIn items before step entry = .ok (result, final)) : final = entry := by
  induction items generalizing before entry with
  | nil => exact (congrArg Prod.snd (Except.ok.inj ran)).symm
  | cons head tail ih =>
    simp only [List.forIn_cons, bind, StateT.bind, Except.bind, pure] at ran
    cases first : step head before entry with
    | error _ => simp [first] at ran
    | ok pair =>
      obtain ⟨control, middle⟩ := pair
      have same := stepPreserves head before entry control middle first
      subst middle
      cases control with
      | done value =>
        simp only [first] at ran
        exact (congrArg Prod.snd (Except.ok.inj ran)).symm
      | yield next =>
        exact ih next entry (by simp only [first, bind, StateT.bind, Except.bind, pure] at ran; exact ran)

private def modifiedNameStep (I : Interpretation) (range : SourceRange)
    (name : StrataDDM.Ann String SourceRange) (before : Contract I.Expression) :
    InterpM (ForInStep (Contract I.Expression)) := do
  if (findBinding name.val (← (get : InterpM Scope)).globals).isNone then
    reject range s!"Unknown modified global '{name.val}'"
  if !before.modifies.contains name.val then
    pure (.yield { before with modifies := before.modifies ++ [name.val] })
  else pure (.yield before)

private theorem modifiedNameStep_scope (I : Interpretation) (range : SourceRange)
    (name : StrataDDM.Ann String SourceRange) (before : Contract I.Expression)
    (state : Scope) (control : ForInStep (Contract I.Expression)) (after : Scope)
    (ran : modifiedNameStep I range name before state = .ok (control, after)) : after = state := by
  unfold modifiedNameStep at ran
  simp only [bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, Except.pure, reject, throw, throwThe, MonadExceptOf.throw,
    Function.comp_apply, StateT.lift, Functor.map, Except.map] at ran
  repeat' first
    | contradiction
    | exact (congrArg Prod.snd (Except.ok.inj ran)).symm
    | split at ran

private theorem forIn_spec {supports : ValueType → Bool}
    (elements : List (BooleDDM.SpecElt SourceRange))
    (step : BooleDDM.SpecElt SourceRange →
      Contract (checkingInterpretation supports).Expression →
      InterpM (ForInStep (Contract (checkingInterpretation supports).Expression)))
    (before : Contract (checkingInterpretation supports).Expression)
    (initial final : Scope) (result : Contract (checkingInterpretation supports).Expression)
    (noAlias : NoScalarAlias initial.names) (same : initial.supportsType = supports)
    (each : ∀ element acc state control next,
      step element acc state = .ok (control, next) →
      NoScalarAlias state.names → state.supportsType = supports →
      next = state ∧ BridgeSpecElt element ∧ ∃ updated, control = .yield updated)
    (success : (forIn elements before step) initial = .ok (result, final)) :
    (∀ element ∈ elements, BridgeSpecElt element) ∧ final = initial := by
  induction elements generalizing before initial with
  | nil =>
    have samePair : (before, initial) = (result, final) := Except.ok.inj success
    cases samePair
    exact ⟨fun _ mem => by simp at mem, rfl⟩
  | cons element rest ih =>
    simp only [List.forIn_cons, bind, StateT.bind, Except.bind, pure] at success
    cases ran : step element before initial with
    | error _ => simp [ran] at success
    | ok pair =>
      obtain ⟨control, next⟩ := pair
      obtain ⟨stable, typed, found⟩ := each element before initial control next ran noAlias same
      obtain ⟨updated, yielded⟩ := found
      have continued : (forIn rest updated step) next = .ok (result, final) := by
        simp only [ran, yielded, bind, StateT.bind, Except.bind, pure] at success
        exact success
      have nextAlias : NoScalarAlias next.names := by
        simp [stable]
        exact noAlias
      have nextTypes : next.supportsType = supports := by
        simp [stable, same]
      refine ⟨?_, ?_⟩
      · intro target member
        rcases List.mem_cons.mp member with rfl | later
        · exact typed
        · exact (ih updated next nextAlias nextTypes continued).1 target later
      · exact ((ih updated next nextAlias nextTypes continued).2).trans stable

private theorem checked_contract {supports : ValueType → Bool}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {specification : Option (BooleDDM.Spec SourceRange)} {scope final : Scope}
    {contract : Contract (checkingInterpretation supports).Expression}
    (noAlias : NoScalarAlias scope.names) (same : scope.supportsType = supports)
    (run : interpContract (checkingInterpretation supports) specification scope =
      .ok (contract, final)) :
    BridgeSpec specification ∧ final = scope := by
  cases specification with
  | none =>
    unfold interpContract at run
    simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at run
    exact ⟨by simp [BridgeSpec], pure_state run⟩
  | some spec =>
    cases spec with
    | spec_mk _ elements =>
      unfold interpContract at run
      simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at run
      split at run
      · contradiction
      · rename_i result loop
        rw [← Array.toArray_toList (xs := elements.val), List.forIn_toArray] at loop
        let step : BooleDDM.SpecElt SourceRange →
            Contract (checkingInterpretation supports).Expression →
            InterpM (ForInStep (Contract (checkingInterpretation supports).Expression)) :=
          fun element before =>
          match element with
          | .modifies_spec range names => do
              let updated ← forIn names.val before
                (modifiedNameStep (checkingInterpretation supports) range)
              pure (.yield updated)
          | .requires_spec range label free expression => do
              let clause ← interpExpr (checkingInterpretation supports) expression
              pure (.yield { before with requires := before.requires ++
                [⟨sourceLabel range label.val, free.val.isSome, clause⟩] })
          | .ensures_spec range label free expression => do
              let clause ← interpExpr (checkingInterpretation supports) expression
              pure (.yield { before with ensures := before.ensures ++
                [⟨sourceLabel range label.val, free.val.isSome, clause⟩] })
        have loopPair : (forIn elements.val.toList
            ({} : Contract (checkingInterpretation supports).Expression) step) scope =
            .ok (result.1, result.2) := by
          cases result with
          | mk accumulator last =>
            change forIn elements.val.toList
              ({} : Contract (checkingInterpretation supports).Expression) step scope =
              .ok (accumulator, last) at loop
            exact loop
        have collected := forIn_spec elements.val.toList step {} scope result.2 result.1
          noAlias same ?each loopPair
        have back : result.2 = final := congrArg Prod.snd (Except.ok.inj run)
        exact ⟨by simpa [BridgeSpec] using collected.1, back.symm.trans collected.2⟩
        case each =>
          intro element before state control next ran alias typesEq
          cases element with
          | modifies_spec range names =>
            simp only [step, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
            cases inner : forIn names.val before
                (modifiedNameStep (checkingInterpretation supports) range) state with
            | error _ =>
              rw [inner] at ran
              simp at ran
            | ok pair =>
              obtain ⟨updated, afterInner⟩ := pair
              have listRun : forIn names.val.toList before
                  (modifiedNameStep (checkingInterpretation supports) range) state =
                  .ok (updated, afterInner) := by
                have inner0 := inner
                have sameArray : names.val.toList.toArray = names.val :=
                  Array.toArray_toList (xs := names.val)
                have rewriteFor := List.forIn_toArray (m := InterpM)
                  (β := Contract (checkingInterpretation supports).Expression)
                  (f := modifiedNameStep (checkingInterpretation supports) range)
                  names.val.toList before
                rw [← sameArray] at inner0
                exact rewriteFor ▸ inner0
              have stable := forIn_preservesScope names.val.toList
                (modifiedNameStep (checkingInterpretation supports) range)
                (fun n acc s c t h => modifiedNameStep_scope _ _ n acc s c t h)
                before state afterInner updated listRun
              simp only [inner, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
              have fields := Except.ok.inj ran
              exact ⟨(congrArg Prod.snd fields).symm.trans stable, trivial,
                updated, (congrArg Prod.fst fields).symm⟩
          | requires_spec range label free expression =>
            cases exprRun : interpExpr (checkingInterpretation supports) expression state with
            | error _ => simp [step, bind, StateT.bind, Except.bind, exprRun] at ran
            | ok pair =>
              obtain ⟨_, afterExpr⟩ := pair
              have back : afterExpr = state := interpExpr_readOnly _ _ _ _ _ exprRun
              subst back
              simp only [step, bind, StateT.bind, Except.bind, exprRun, pure, StateT.pure,
                Except.pure] at ran
              have fields := Except.ok.inj ran
              have typed := checked_expr_bridgeTyped onlyScalars alias typesEq exprRun
              exact ⟨(congrArg Prod.snd fields).symm, by simpa [BridgeSpecElt] using typed,
                _, (congrArg Prod.fst fields).symm⟩
          | ensures_spec range label free expression =>
            cases exprRun : interpExpr (checkingInterpretation supports) expression state with
            | error _ => simp [step, bind, StateT.bind, Except.bind, exprRun] at ran
            | ok pair =>
              obtain ⟨_, afterExpr⟩ := pair
              have back : afterExpr = state := interpExpr_readOnly _ _ _ _ _ exprRun
              subst back
              simp only [step, bind, StateT.bind, Except.bind, exprRun, pure, StateT.pure,
                Except.pure] at ran
              have fields := Except.ok.inj ran
              have typed := checked_expr_bridgeTyped onlyScalars alias typesEq exprRun
              exact ⟨(congrArg Prod.snd fields).symm, by simpa [BridgeSpecElt] using typed,
                _, (congrArg Prod.fst fields).symm⟩

private theorem inputBindings_iface (parameters : BooleDDM.Bindings SourceRange)
    {scope final : Scope} {bindings : List Binding}
    (run : inputBindings parameters scope = .ok (bindings, final)) :
    final.names = scope.names ∧ final.supportsType = scope.supportsType := by
  cases parameters with
  | mkBindings _ parameters =>
    change (parameters.val.toList.mapM fun (parameter : BooleDDM.Binding SourceRange) =>
      match parameter with
      | BooleDDM.Binding.mkBinding range name (.expr ty) => addLocal range name.val ty
      | parameter => reject default s!"Unsupported parameter: {repr parameter}") scope =
      Except.ok (bindings, final) at run
    generalize parameters.val.toList = items at run
    induction items generalizing scope bindings final with
    | nil =>
      rw [List.mapM_nil] at run
      have back := pure_state run
      cases back
      exact ⟨rfl, rfl⟩
    | cons parameter rest ih =>
      rw [List.mapM_cons] at run
      obtain ⟨_, middle, checked, tail⟩ := split_run run
      have kept : middle.names = scope.names ∧ middle.supportsType = scope.supportsType := by
        cases parameter
        case' mkBinding range name type => cases type
        all_goals try contradiction
        exact addLocal_iface checked
      obtain ⟨_, last, ran, ended⟩ := split_run tail
      obtain ⟨names, types⟩ := ih ran
      have same : _ = (bindings, final) := Except.ok.inj ended
      cases same
      exact ⟨names.trans kept.1, types.trans kept.2⟩

private theorem outputBindings_iface (outputs : BooleDDM.MonoDeclList SourceRange)
    {scope final : Scope} {bindings : List Binding}
    (run : outputBindings outputs scope = .ok (bindings, final)) :
    final.names = scope.names ∧ final.supportsType = scope.supportsType := by
  induction outputs generalizing scope bindings final with
  | monoDeclAtom range binding =>
    cases binding
    rw [outputBindings] at run
    obtain ⟨_, middle, checked, ended⟩ := split_run run
    have same : _ = (bindings, final) := Except.ok.inj ended
    cases same
    exact addLocal_iface checked
  | monoDeclPush range rest binding ih =>
    cases binding
    rw [outputBindings] at run
    obtain ⟨_, middle, prior, added⟩ := split_run run
    obtain ⟨keptNames, keptTypes⟩ := ih prior
    obtain ⟨_, _, checked, ended⟩ := split_run added
    have same : _ = (bindings, final) := Except.ok.inj ended
    cases same
    obtain ⟨names, types⟩ := addLocal_iface checked
    exact ⟨names.trans keptNames, types.trans keptTypes⟩

private theorem checked_proc {supports : ValueType → Bool}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {range : SourceRange} {name : String}
    {typeArgs : Option (BooleDDM.TypeArgs SourceRange)}
    {parameters : BooleDDM.Bindings SourceRange}
    {outputs : Option (BooleDDM.MonoDeclList SourceRange)}
    {specification : Option (BooleDDM.Spec SourceRange)}
    {block : BooleDDM.Block SourceRange} {scope final : Scope}
    {procedure : InterpProcedure (checkingInterpretation supports).Expression
      (checkingInterpretation supports).Statement}
    (noAlias : NoScalarAlias scope.names) (same : scope.supportsType = supports)
    (run : interpProc (checkingInterpretation supports) range name typeArgs parameters outputs
      specification (some block) scope = .ok (procedure, final)) :
    BridgeBlock block ∧ BridgeSpec specification := by
  unfold interpProc at run
  obtain ⟨_, ran⟩ := withScope_success run
  cases typeArgs with
  | some _ => contradiction
  | none =>
    simp only [Option.isSome, Bool.false_eq_true, ite_false] at ran
    obtain ⟨_, afterInputs, readInputs, ran⟩ := split_run ran
    obtain ⟨inputNames, inputTypes⟩ := inputBindings_iface parameters readInputs
    cases outputs
    all_goals
      obtain ⟨_, afterOutputs, readOutputs, ran⟩ := split_run ran
      have outputKept : afterOutputs.names = afterInputs.names ∧
          afterOutputs.supportsType = afterInputs.supportsType := by
        first
        | have back := pure_state readOutputs
          cases back
          exact ⟨rfl, rfl⟩
        | exact outputBindings_iface _ readOutputs
      obtain ⟨outNames, outTypes⟩ := outputKept
      obtain ⟨contract, afterContract, readContract, ran⟩ := split_run ran
      have alias' : NoScalarAlias afterOutputs.names := by
        simp [outNames, inputNames]
        exact noAlias
      have types' : afterOutputs.supportsType = supports := by
        simp [outTypes, inputTypes, same]
      obtain ⟨specTyped, contractSame⟩ :=
        checked_contract onlyScalars alias' types' readContract
      subst afterContract
      let bodyEntry : Scope :=
        { afterOutputs with modifies := contract.modifies, labels := [name] }
      have entryEq : bodyEntry =
          { afterOutputs with modifies := contract.modifies, labels := [name] } := rfl
      simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
      rw [← entryEq] at ran
      have entryTypes : bodyEntry.supportsType = supports := by
        simp [bodyEntry, types']
      have entryNames : bodyEntry.names = scope.names := by
        simp [bodyEntry, outNames, inputNames]
      cases bodyRan : interpBlock (checkingInterpretation supports) block bodyEntry with
      | error _ => simp [bodyRan] at ran
      | ok _ =>
        obtain ⟨typed, _, _⟩ := checked_block onlyScalars (names := scope.names)
          noAlias entryTypes entryNames bodyRan
        exact ⟨typed, specTyped⟩

private def ScopeCarried (supports : ValueType → Bool) (names : GlobalContext) (scope : Scope) : Prop :=
  scope.supportsType = supports ∧ scope.names = names

private theorem yield_carried {β : Type} {supports : ValueType → Bool} {names : GlobalContext}
    {state next : Scope} {control : ForInStep β} {value : β}
    (carried : ScopeCarried supports names state)
    (ran : (pure (ForInStep.yield value) : InterpM (ForInStep β)) state = .ok (control, next)) :
    ∃ updated, control = ForInStep.yield updated ∧ ScopeCarried supports names next := by
  simp only [pure, StateT.pure, Except.pure] at ran
  have fields := Except.ok.inj ran
  have back : next = state := (congrArg Prod.snd fields).symm
  exact ⟨value, (congrArg Prod.fst fields).symm, back ▸ carried⟩

private def varStep (I : Interpretation)
    (procedures : List (InterpProcedure I.Expression I.Statement))
    (range : SourceRange) (name : StrataDDM.Ann String SourceRange) (ty : Boole.Type)
    (globals : GlobalContext) : InterpM (ForInStep (List (InterpProcedure I.Expression I.Statement))) := do
  if retainLegacyGlobal globals ty then
    if !procedures.isEmpty then
      reject range "Declare globals before procedures"
    let binding := { name := name.val, sort := ← sourceSort ty : Binding }
    fresh range binding
    modify fun scope => { scope with globals := scope.globals ++ [binding] }
  pure (.yield procedures)

private theorem varStep_carried {supports : ValueType → Bool} {globals : GlobalContext}
    (I : Interpretation) (procedures : List (InterpProcedure I.Expression I.Statement))
    (range : SourceRange) (name : StrataDDM.Ann String SourceRange) (ty : Boole.Type)
    {state next : Scope} {control : ForInStep (List (InterpProcedure I.Expression I.Statement))}
    (carried : ScopeCarried supports globals state)
    (ran : varStep I procedures range name ty globals state = .ok (control, next)) :
    ∃ updated, control = .yield updated ∧ ScopeCarried supports globals next := by
  unfold varStep at ran
  simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
  split at ran
  · split at ran
    · simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, Function.comp_apply,
        Functor.map, Except.map] at ran
      contradiction
    · obtain ⟨_, midSort, sorted, ran⟩ := split_run ran
      have sortBack := sourceSort_readOnly ty _ _ _ sorted
      subst midSort
      obtain ⟨_, midFresh, freshened, ran⟩ := split_run ran
      have freshBack := (fresh_names freshened).2.2
      subst midFresh
      simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
        bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
      have fields := Except.ok.inj ran
      refine ⟨procedures, (congrArg Prod.fst fields).symm, ?_⟩
      have back := (congrArg Prod.snd fields).symm
      cases back
      exact carried
  · exact yield_carried carried ran

private def booleStep (I : Interpretation) (range : SourceRange)
    (name : StrataDDM.Ann String SourceRange) (types : StrataDDM.Ann (Option (BooleDDM.TypeArgs SourceRange)) SourceRange)
    (inputs : BooleDDM.Bindings SourceRange)
    (outputs : StrataDDM.Ann (Option (BooleDDM.MonoDeclList SourceRange)) SourceRange)
    (decreases : StrataDDM.Ann (Option (BooleDDM.Measure SourceRange)) SourceRange)
    (spec : StrataDDM.Ann (Option (BooleDDM.Spec SourceRange)) SourceRange)
    (body : StrataDDM.Ann (Option (BooleDDM.Block SourceRange)) SourceRange)
    (procedures : List (InterpProcedure I.Expression I.Statement)) :
    InterpM (ForInStep (List (InterpProcedure I.Expression I.Statement))) := do
  if decreases.val.isSome then
    reject range "Procedure decreases clauses are outside this fragment"
  if procedures.any (fun p => p.name == name.val) then
    reject range "Duplicate procedure name"
  let procedure ← interpProc I range name.val types.val inputs outputs.val spec.val body.val
  pure (.yield (procedures ++ [procedure]))

private theorem booleStep_carried {supports : ValueType → Bool} {globals : GlobalContext}
    (I : Interpretation) (range : SourceRange)
    (name : StrataDDM.Ann String SourceRange)
    (types : StrataDDM.Ann (Option (BooleDDM.TypeArgs SourceRange)) SourceRange)
    (inputs : BooleDDM.Bindings SourceRange)
    (outputs : StrataDDM.Ann (Option (BooleDDM.MonoDeclList SourceRange)) SourceRange)
    (decreases : StrataDDM.Ann (Option (BooleDDM.Measure SourceRange)) SourceRange)
    (spec : StrataDDM.Ann (Option (BooleDDM.Spec SourceRange)) SourceRange)
    (body : StrataDDM.Ann (Option (BooleDDM.Block SourceRange)) SourceRange)
    (procedures : List (InterpProcedure I.Expression I.Statement))
    {state next : Scope} {control : ForInStep (List (InterpProcedure I.Expression I.Statement))}
    (carried : ScopeCarried supports globals state)
    (ran : booleStep I range name types inputs outputs decreases spec body procedures state =
      .ok (control, next)) :
    ∃ updated, control = .yield updated ∧ ScopeCarried supports globals next := by
  unfold booleStep at ran
  simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
  split at ran
  · simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, Function.comp_apply,
      Functor.map, Except.map] at ran
    contradiction
  · split at ran
    · simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, Function.comp_apply,
        Functor.map, Except.map] at ran
      contradiction
    · obtain ⟨_, middle, called, rest⟩ := split_run ran
      have back : middle = state := withScope_restores called
      subst middle
      exact yield_carried carried rest

private theorem booleStep_proc (I : Interpretation) (range : SourceRange)
    (name : StrataDDM.Ann String SourceRange)
    (types : StrataDDM.Ann (Option (BooleDDM.TypeArgs SourceRange)) SourceRange)
    (inputs : BooleDDM.Bindings SourceRange)
    (outputs : StrataDDM.Ann (Option (BooleDDM.MonoDeclList SourceRange)) SourceRange)
    (decreases : StrataDDM.Ann (Option (BooleDDM.Measure SourceRange)) SourceRange)
    (spec : StrataDDM.Ann (Option (BooleDDM.Spec SourceRange)) SourceRange)
    (body : StrataDDM.Ann (Option (BooleDDM.Block SourceRange)) SourceRange)
    (procedures : List (InterpProcedure I.Expression I.Statement))
    {state next : Scope} {control : ForInStep (List (InterpProcedure I.Expression I.Statement))}
    {block : BooleDDM.Block SourceRange}
    (isBody : body.val = some block)
    (ran : booleStep I range name types inputs outputs decreases spec body procedures state =
      .ok (control, next)) :
    ∃ procedure middle,
      interpProc I range name.val types.val inputs outputs.val spec.val (some block) state =
        .ok (procedure, middle) := by
  unfold booleStep at ran
  simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
  split at ran
  · simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, Function.comp_apply,
      Functor.map, Except.map] at ran
    contradiction
  · split at ran
    · simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, Function.comp_apply,
        Functor.map, Except.map] at ran
      contradiction
    · obtain ⟨procedure, middle, called, _⟩ := split_run ran
      exact ⟨procedure, middle, isBody ▸ called⟩

private def coreStep (I : Interpretation) (range : SourceRange)
    (name : StrataDDM.Ann String SourceRange)
    (types : StrataDDM.Ann (Option (BooleDDM.TypeArgs SourceRange)) SourceRange)
    (inputs : BooleDDM.Bindings SourceRange)
    (spec : StrataDDM.Ann (Option (BooleDDM.Spec SourceRange)) SourceRange)
    (body : StrataDDM.Ann (Option (BooleDDM.Block SourceRange)) SourceRange)
    (procedures : List (InterpProcedure I.Expression I.Statement)) :
    InterpM (ForInStep (List (InterpProcedure I.Expression I.Statement))) := do
  if procedures.any (fun p => p.name == name.val) then
    reject range "Duplicate procedure name"
  let procedure ← interpProc I range name.val types.val inputs none spec.val body.val
  pure (.yield (procedures ++ [procedure]))

private theorem coreStep_carried {supports : ValueType → Bool} {globals : GlobalContext}
    (I : Interpretation) (range : SourceRange) (name : StrataDDM.Ann String SourceRange)
    (types : StrataDDM.Ann (Option (BooleDDM.TypeArgs SourceRange)) SourceRange)
    (inputs : BooleDDM.Bindings SourceRange)
    (spec : StrataDDM.Ann (Option (BooleDDM.Spec SourceRange)) SourceRange)
    (body : StrataDDM.Ann (Option (BooleDDM.Block SourceRange)) SourceRange)
    (procedures : List (InterpProcedure I.Expression I.Statement))
    {state next : Scope} {control : ForInStep (List (InterpProcedure I.Expression I.Statement))}
    (carried : ScopeCarried supports globals state)
    (ran : coreStep I range name types inputs spec body procedures state = .ok (control, next)) :
    ∃ updated, control = .yield updated ∧ ScopeCarried supports globals next := by
  unfold coreStep at ran
  simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
  split at ran
  · simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, Function.comp_apply,
      Functor.map, Except.map] at ran
    contradiction
  · obtain ⟨_, middle, called, rest⟩ := split_run ran
    have back : middle = state := withScope_restores called
    subst middle
    exact yield_carried carried rest

private theorem coreStep_proc (I : Interpretation) (range : SourceRange)
    (name : StrataDDM.Ann String SourceRange)
    (types : StrataDDM.Ann (Option (BooleDDM.TypeArgs SourceRange)) SourceRange)
    (inputs : BooleDDM.Bindings SourceRange)
    (spec : StrataDDM.Ann (Option (BooleDDM.Spec SourceRange)) SourceRange)
    (body : StrataDDM.Ann (Option (BooleDDM.Block SourceRange)) SourceRange)
    (procedures : List (InterpProcedure I.Expression I.Statement))
    {state next : Scope} {control : ForInStep (List (InterpProcedure I.Expression I.Statement))}
    {block : BooleDDM.Block SourceRange}
    (isBody : body.val = some block)
    (ran : coreStep I range name types inputs spec body procedures state = .ok (control, next)) :
    ∃ procedure middle,
      interpProc I range name.val types.val inputs none spec.val (some block) state =
        .ok (procedure, middle) := by
  unfold coreStep at ran
  simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
  split at ran
  · simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, Function.comp_apply,
      Functor.map, Except.map] at ran
    contradiction
  · obtain ⟨procedure, middle, called, _⟩ := split_run ran
    exact ⟨procedure, middle, isBody ▸ called⟩

private def programStep (I : Interpretation) (globals : GlobalContext)
    (command : BooleDDM.Command SourceRange)
    (procedures : List (InterpProcedure I.Expression I.Statement)) :
    InterpM (ForInStep (List (InterpProcedure I.Expression I.Statement))) :=
  match command with
  | .command_typedecl .. => pure (.yield procedures)
  | .command_var range (.bind_mk _ name _ ty) => varStep I procedures range name ty globals
  | .boole_procedure range name types inputs outputs decreases spec body =>
      booleStep I range name types inputs outputs decreases spec body procedures
  | .command_procedure range _ name types inputs spec body =>
      coreStep I range name types inputs spec body procedures
  | _ => reject default s!"Unsupported declaration: {repr command}"

private theorem programStep_carried {supports : ValueType → Bool} {globals : GlobalContext}
    (I : Interpretation) (command : BooleDDM.Command SourceRange)
    (procedures : List (InterpProcedure I.Expression I.Statement))
    {state next : Scope} {control : ForInStep (List (InterpProcedure I.Expression I.Statement))}
    (carried : ScopeCarried supports globals state)
    (ran : programStep I globals command procedures state = .ok (control, next)) :
    ∃ updated, control = .yield updated ∧ ScopeCarried supports globals next := by
  unfold programStep at ran
  split at ran <;> first
    | exact yield_carried carried ran
    | exact varStep_carried I procedures _ _ _ carried ran
    | exact booleStep_carried I _ _ _ _ _ _ _ _ _ carried ran
    | exact coreStep_carried I _ _ _ _ _ _ _ carried ran
    | simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, Function.comp_apply,
        Functor.map, Except.map, bind, StateT.bind, Except.bind] at ran

private theorem forIn_member_carried {α β : Type} {supports : ValueType → Bool}
    {names : GlobalContext} (items : List α) (step : α → β → InterpM (ForInStep β))
    (before : β) (initial final : Scope) (result : β)
    (start : ScopeCarried supports names initial)
    (success : (forIn items before step) initial = .ok (result, final))
    (keeps : ∀ item acc state control next,
      ScopeCarried supports names state →
      step item acc state = .ok (control, next) →
      ∃ updated, control = .yield updated ∧ ScopeCarried supports names next)
    {item : α} (member : item ∈ items) :
    ∃ acc state control next, ScopeCarried supports names state ∧
      step item acc state = .ok (control, next) := by
  induction items generalizing before initial with
  | nil => simp at member
  | cons head tail ih =>
    simp only [List.forIn_cons, bind, StateT.bind, Except.bind, pure] at success
    cases ran : step head before initial with
    | error _ => simp [ran] at success
    | ok pair =>
      obtain ⟨control, next⟩ := pair
      obtain ⟨updated, yielded, carriedNext⟩ := keeps head before initial control next start ran
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨before, initial, control, next, start, ran⟩
      · have continued : (forIn tail updated step) next = .ok (result, final) := by
          simp only [ran, yielded, bind, StateT.bind, Except.bind, pure] at success
          exact success
        exact ih updated next carriedNext continued later

private theorem onlyIntBool {ty : ValueType}
    (ok : (ty == .int || ty == .bool) = true) : ty = .int ∨ ty = .bool := by
  simpa [Bool.or_eq_true, beq_iff_eq] using ok

private theorem fragment_procedure_bridge {source : Boole.Program} {names : GlobalContext}
    {command : BooleDDM.Command SourceRange}
    (fragment : sourceInFragment source names) (noAlias : NoScalarAlias names)
    (member : match source with | .prog _ declarations => command ∈ declarations.val.toList) :
    match command with
    | .boole_procedure _ _ _ _ _ _ spec body =>
        ∀ block, body.val = some block → BridgeBlock block ∧ BridgeSpec spec.val
    | .command_procedure _ _ _ _ _ spec body =>
        ∀ block, body.val = some block → BridgeBlock block ∧ BridgeSpec spec.val
    | _ => True := by
  let supports := fun ty : ValueType => ty == .int || ty == .bool
  have onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool :=
    fun _ ok => onlyIntBool ok
  cases source with
  | prog range declarations =>
    dsimp [sourceInFragment] at fragment
    have present : command ∈ declarations.val.toList := by simpa using member
    have checked : checkFragment supports (.prog range declarations) names = true := by
      simpa [supports] using fragment.2
    cases programRun : interpProgram (checkingInterpretation supports) (.prog range declarations) names with
    | error _ =>
      simp [checkFragment, Except.isOk, Except.toBool, programRun] at checked
    | ok _ =>
      simp only [interpProgram, StateT.run', Functor.map, Except.map, bind, StateT.bind, Except.bind,
        get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure] at programRun
      split at programRun
      · contradiction
      · rename_i result executed
        split at executed
        · contradiction
        · rename_i stepResult loopRan
          rw [← (Array.toArray_toList (xs := declarations.val)), List.forIn_toArray] at loopRan
          let entry : Scope := { names := names, supportsType := supports }
          change (forIn declarations.val.toList ([] : List _)
            (programStep (checkingInterpretation supports) names) entry) = .ok stepResult at loopRan
          have start : ScopeCarried supports names entry := by
            simp [ScopeCarried, entry, checkingInterpretation]
          obtain ⟨acc, state, _, _, carriedState, stepped⟩ := forIn_member_carried
            declarations.val.toList (programStep (checkingInterpretation supports) names)
            [] entry stepResult.2 stepResult.1 start loopRan
            (fun command procedures state control next carried ran =>
              programStep_carried (checkingInterpretation supports) command procedures carried ran)
            present
          cases command
          case boole_procedure range name types inputs outputs decreases spec body =>
            intro block isBody
            obtain ⟨procedure, _, called⟩ := booleStep_proc (checkingInterpretation supports)
              range name types inputs outputs decreases spec body acc isBody
              (by simpa [programStep] using stepped)
            exact checked_proc onlyScalars (carriedState.2.symm ▸ noAlias) carriedState.1 called
          case command_procedure range _ name types inputs spec body =>
            intro block isBody
            obtain ⟨procedure, _, called⟩ := coreStep_proc (checkingInterpretation supports)
              range name types inputs spec body acc isBody
              (by simpa [programStep] using stepped)
            exact checked_proc onlyScalars (carriedState.2.symm ▸ noAlias) carriedState.1 called
          all_goals trivial

end Strata.Boole.Hoare
