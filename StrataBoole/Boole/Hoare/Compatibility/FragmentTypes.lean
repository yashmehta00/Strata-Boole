/-
Copyright Strata Contributors

SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Boole.Hoare.Compatibility.Syntax
import all StrataBoole.Boole.Hoare.Compatibility.Syntax
import all StrataBoole.Boole.Hoare.Compatibility.Fragment
import all StrataBoole.Boole.Interp
import all StrataBoole.Boole.Semantics.Adequacy.SourceInterface
import all StrataBoole.Boole.Semantics.Adequacy.Lowering
import StrataBoole.Boole.LegacyGlobals

public section

namespace Strata.Boole.Hoare

open StrataDDM Strata.Boole

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

mutual
private def typeRank : Boole.Type → Nat
  | .arrow _ a b => typeRank a + typeRank b + 1
  | .Map _ value key => typeRank value + typeRank key + 1
  | .Sequence _ element => typeRank element + 1
  | .fvar _ _ arguments => listRank arguments.toList + 1
  | _ => 0
private def listRank : List Boole.Type → Nat
  | [] => 0
  | ty :: rest => typeRank ty + listRank rest + 1
end

private theorem listRank_append (xs ys : List Boole.Type) :
    listRank (xs ++ ys) = listRank xs + listRank ys := by
  induction xs with
  | nil => simp [listRank]
  | cons head tail ih =>
    simp only [List.cons_append, listRank, ih]
    omega

private theorem listRank_reverse (l : List Boole.Type) : listRank l.reverse = listRank l := by
  induction l with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.reverse_cons, listRank_append, listRank, ih]
    omega

-- The value `sourceSort` returns, ignoring the supports check that only gates success.
mutual
private def evalSort (names : GlobalContext) : Boole.Type → Option ValueType
  | .bool _ => some .bool
  | .int _ => some .int
  | .nat _ => some .nat
  | .real _ => some .real
  | .string _ => some .string
  | .regex _ => some .regex
  | .tvar _ name => some (.variable name)
  | .bv _ width =>
    match width with
    | .W1 _ => some (.bitvec 1) | .W8 _ => some (.bitvec 8) | .W16 _ => some (.bitvec 16)
    | .W32 _ => some (.bitvec 32) | .W64 _ => some (.bitvec 64) | .W128 _ => some (.bitvec 128)
    | _ => none
  | .arrow _ a b => do let x ← evalSort names a; let y ← evalSort names b; pure (.arrow x y)
  | .Map _ value key => do let k ← evalSort names key; let v ← evalSort names value; pure (.map k v)
  | .Sequence _ element => (evalSort names element).map .sequence
  | .fvar _ index arguments => do
      let some name := names.nameOf? index | none
      let sorts ← evalArgs names arguments.toList.reverse
      if name == "Set" then
        match sorts with
        | [element] => pure (.set element)
        | _ => none
      else pure (.named name sorts)
  | _ => none
termination_by ty => typeRank ty
decreasing_by
  all_goals simp_wf
  all_goals try simp [typeRank, listRank, listRank_reverse]
  all_goals omega

private def evalArgs (names : GlobalContext) : List Boole.Type → Option (List ValueType)
  | [] => some []
  | ty :: rest => do let sort ← evalSort names ty; let sorts ← evalArgs names rest; pure (sort :: sorts)
termination_by items => listRank items
decreasing_by
  all_goals simp_wf
  all_goals try simp [listRank]
  all_goals omega
end

private theorem fmap_value {α β : Type} {f : α → β} {action : InterpM α} {scope final : Scope} {out : β}
    (read : ReadOnly action) (run : (f <$> action) scope = .ok (out, final)) :
    ∃ value, action scope = .ok (value, scope) ∧ out = f value ∧ final = scope := by
  rw [map_eq_pure_bind] at run
  obtain ⟨value, mid, acted, pureOut⟩ := split_run run
  have back : mid = scope := read _ _ _ acted
  simp only [back, pure, StateT.pure, Except.pure] at pureOut
  obtain ⟨valueEq, stateEq⟩ := Prod.mk.inj (Except.ok.inj pureOut)
  exact ⟨value, back ▸ acted, valueEq.symm, stateEq.symm⟩

private theorem fmap_ap_value {α β γ : Type} {f : α → β → γ} {left : InterpM α} {right : InterpM β}
    {scope final : Scope} {out : γ} (readL : ReadOnly left) (readR : ReadOnly right)
    (run : (f <$> left <*> right) scope = .ok (out, final)) :
    ∃ a b, left scope = .ok (a, scope) ∧ right scope = .ok (b, scope) ∧ out = f a b ∧
      final = scope := by
  rw [seq_eq_bind_map] at run
  obtain ⟨applied, mid, made, rest⟩ := split_run run
  obtain ⟨a, aRun, fa, midEq⟩ := fmap_value readL made
  subst midEq
  subst fa
  obtain ⟨b, bRun, app, back⟩ := fmap_value readR rest
  exact ⟨a, b, aRun, bRun, app, back⟩

mutual

private theorem sourceSort_eval {ty : Boole.Type} {scope : Scope} {out : ValueType} {final : Scope}
    (run : sourceSort ty scope = .ok (out, final)) :
    evalSort scope.names ty = some out ∧ scope.supportsType out = true := by
  match ty with
  | .bool _ | .int _ | .nat _ | .real _ | .string _ | .regex _ | .tvar _ _ =>
    rw [sourceSort.eq_def] at run
    dsimp only at run
    simp only [bind, StateT.bind, Except.bind, pure, Except.pure, get, getThe,
      MonadStateOf.get, StateT.get] at run
    obtain ⟨rfl, _, supported⟩ := pureSort_facts run
    exact ⟨by simp [evalSort], supported⟩
  | .bvar _ _ | .W1 _ | .W8 _ | .W16 _ | .W32 _ | .W64 _ | .W128 _ | .Set _ _ =>
    rw [sourceSort.eq_def] at run
    dsimp only at run
    simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, StateT.bind, Except.bind] at run
  | .bv _ width =>
    cases width with
    | W1 _ | W8 _ | W16 _ | W32 _ | W64 _ | W128 _ =>
      rw [sourceSort.eq_def] at run
      dsimp only at run
      simp only [bind, StateT.bind, Except.bind, pure, Except.pure, get, getThe,
        MonadStateOf.get, StateT.get] at run
      obtain ⟨rfl, _, supported⟩ := pureSort_facts run
      exact ⟨by simp [evalSort], supported⟩
    | _ =>
      rw [sourceSort.eq_def] at run
      dsimp only at run
      simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, StateT.bind, Except.bind] at run
  | .arrow _ domain range =>
    rw [sourceSort.eq_def] at run
    dsimp only at run
    obtain ⟨_, _, built, gated⟩ := split_run run
    obtain ⟨x, y, xRun, yRun, produced, back⟩ :=
      fmap_ap_value (sourceSort_readOnly domain) (sourceSort_readOnly range) built
    subst back
    simp only [bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, Except.pure] at gated
    obtain ⟨rfl, _, supported⟩ := pureSort_facts gated
    exact ⟨by simp [evalSort, produced, (sourceSort_eval xRun).1, (sourceSort_eval yRun).1], supported⟩
  | .Map _ value key =>
    rw [sourceSort.eq_def] at run
    dsimp only at run
    obtain ⟨_, _, built, gated⟩ := split_run run
    obtain ⟨k, v, kRun, vRun, produced, back⟩ :=
      fmap_ap_value (sourceSort_readOnly key) (sourceSort_readOnly value) built
    subst back
    simp only [bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, Except.pure] at gated
    obtain ⟨rfl, _, supported⟩ := pureSort_facts gated
    exact ⟨by simp [evalSort, produced, (sourceSort_eval kRun).1, (sourceSort_eval vRun).1], supported⟩
  | .Sequence _ element =>
    rw [sourceSort.eq_def] at run
    dsimp only at run
    obtain ⟨_, _, built, gated⟩ := split_run run
    obtain ⟨elem, elemRun, produced, back⟩ := fmap_value (sourceSort_readOnly element) built
    subst back
    simp only [bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get,
      pure, Except.pure] at gated
    obtain ⟨rfl, _, supported⟩ := pureSort_facts gated
    exact ⟨by simp [evalSort, produced, (sourceSort_eval elemRun).1], supported⟩
  | .fvar _ index arguments =>
    rw [sourceSort.eq_def] at run
    dsimp only at run
    simp only [bind, StateT.bind, Except.bind, pure, Except.pure, get, getThe,
      MonadStateOf.get, StateT.get] at run
    cases found : scope.names.nameOf? index <;> simp [found] at run
    · simp [bind, reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, StateT.bind,
        Except.bind, Functor.map, Except.map, StateT.get, pure, Except.pure] at run
    · rename_i name
      obtain ⟨sorts, mid, mapped, rest⟩ := split_run run
      have listed := (args_eval mapped).1
      have back := (args_eval mapped).2
      subst back
      split at rest
      · rename_i setName
        cases sorts with
        | nil =>
          simp [bind, reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, StateT.bind,
            Except.bind, Functor.map, Except.map] at rest
        | cons element tail =>
          cases tail with
          | cons _ _ =>
            simp [bind, reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, StateT.bind,
              Except.bind, Functor.map, Except.map] at rest
          | nil =>
            simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, get, getThe,
              MonadStateOf.get, StateT.get, ← Bool.not_eq_true'] at rest
            obtain ⟨rfl, _, supported⟩ := pureSort_facts rest
            exact ⟨by simp [evalSort, evalArgs, found, listed, setName], supported⟩
      · rename_i notSet
        simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, get, getThe,
          MonadStateOf.get, StateT.get, ← Bool.not_eq_true'] at rest
        obtain ⟨rfl, _, supported⟩ := pureSort_facts rest
        exact ⟨by simp [evalSort, found, listed, notSet], supported⟩
termination_by typeRank ty
decreasing_by
  all_goals simp_wf
  all_goals try simp [typeRank, listRank, listRank_reverse]
  all_goals omega

private theorem args_eval {items : List Boole.Type} {scope : Scope} {out : List ValueType} {final : Scope}
    (run : items.mapM sourceSort scope = .ok (out, final)) :
    evalArgs scope.names items = some out ∧ final = scope := by
  match items with
  | [] =>
    rw [List.mapM_nil] at run
    simp only [pure, StateT.pure, Except.pure] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    exact ⟨by simp [evalArgs], rfl⟩
  | ty :: rest =>
    rw [List.mapM_cons] at run
    obtain ⟨sort, mid, sorted, tail⟩ := split_run run
    have back := sourceSort_readOnly ty _ _ _ sorted
    subst back
    obtain ⟨sorts, last, restRun, done⟩ := split_run tail
    obtain ⟨restEq, restored⟩ := args_eval restRun
    subst restored
    simp only [pure, StateT.pure, Except.pure] at done
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj done)
    exact ⟨by simp [evalArgs, (sourceSort_eval sorted).1, restEq], rfl⟩
termination_by listRank items
decreasing_by
  all_goals simp_wf
  all_goals try simp [listRank]
  all_goals omega

end

private theorem sourceSort_scalar {supports : ValueType → Bool}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {scope : Scope} (same : scope.supportsType = supports) {ty : Boole.Type} {out : ValueType}
    {final : Scope} (run : sourceSort ty scope = .ok (out, final)) :
    out = .int ∨ out = .bool :=
  onlyScalars _ (same ▸ (sourceSort_eval run).2)

private theorem sourceSort_determined {ty : Boole.Type} {s1 s2 : Scope} {a b : ValueType}
    {f1 f2 : Scope} (r1 : sourceSort ty s1 = .ok (a, f1)) (r2 : sourceSort ty s2 = .ok (b, f2))
    (same : s1.names = s2.names) : a = b := by
  have left := (sourceSort_eval r1).1
  have right := (sourceSort_eval r2).1
  rw [same] at left
  exact Option.some.inj (left.symm.trans right)

private theorem sourceSort_bridgeType {supports : ValueType → Bool} {names : GlobalContext}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {checkScope : Scope} (types : checkScope.supportsType = supports)
    (sameNames : checkScope.names = names) {ty : Boole.Type} {out : ValueType} {final : Scope}
    (run : sourceSort ty checkScope = .ok (out, final)) : bridgeType names ty := by
  intro scope sort final' namesEq ran
  exact sourceSort_determined run ran (sameNames.trans namesEq.symm) ▸
    sourceSort_scalar onlyScalars types run

private theorem con_ne {n1 n2 : String} {as bs : List ValueType}
    (h : ValueType.con n1 as = ValueType.con n2 bs) (diff : n1 ≠ n2) : False := by
  simp at h
  exact diff h.1

private theorem sort_clash {supports : ValueType → Bool}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {scope : Scope} (same : scope.supportsType = supports) {ty : Boole.Type} {out : ValueType}
    {final : Scope} (run : sourceSort ty scope = .ok (out, final))
    (bad : out ≠ .int ∧ out ≠ .bool) : False := by
  rcases sourceSort_scalar onlyScalars same run with h | h
  · exact bad.1 h
  · exact bad.2 h

private theorem interpExpr_readOnly (I : Interpretation) (e : Boole.Expr) : ReadOnly (interpExpr I e) := by
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
    ∃ value, action initial = .ok (value, initial) ∧ next value initial = .ok (result, final) := by
  obtain ⟨value, middle, first, second⟩ := split_run run
  exact ⟨value, by simpa [kept _ _ _ first] using first, by simpa [kept _ _ _ first] using second⟩

set_option hygiene false in
macro "leaf" : tactic => `(tactic| first
  | exact .natToInt _ _ | exact .strLit _ _ | exact .bv1Lit _ _ | exact .bv8Lit _ _ | exact .bv16Lit _ _
  | exact .bv32Lit _ _ | exact .bv64Lit _ _ | exact .bv128Lit _ _ | exact .app _ _ _ | exact .btrue _
  | exact .bfalse _ | exact .fvar _ _ | exact .bvar _ _)

set_option hygiene false in
macro "boolBin" : tactic => `(tactic|
  (obtain ⟨_, aRun, rest⟩ := peel (interpExpr_readOnly _ _) run
   obtain ⟨_, bRun, _⟩ := peel (interpExpr_readOnly _ _) rest
   first
     | exact .and _ (checked_expr_bridgeTyped onlyScalars sameNames same aRun)
         (checked_expr_bridgeTyped onlyScalars sameNames same bRun)
     | exact .or _ (checked_expr_bridgeTyped onlyScalars sameNames same aRun)
         (checked_expr_bridgeTyped onlyScalars sameNames same bRun)
     | exact .implies _ (checked_expr_bridgeTyped onlyScalars sameNames same aRun)
         (checked_expr_bridgeTyped onlyScalars sameNames same bRun)
     | exact .equiv _ (checked_expr_bridgeTyped onlyScalars sameNames same aRun)
         (checked_expr_bridgeTyped onlyScalars sameNames same bRun)))

set_option hygiene false in
macro "typedBin" : tactic => `(tactic|
  (obtain ⟨_, sorted, rest⟩ := peel (sourceSort_readOnly _) run
   have typed := sourceSort_bridgeType onlyScalars same sameNames sorted
   obtain ⟨_, aRun, rest⟩ := peel (interpExpr_readOnly _ _) rest
   obtain ⟨_, bRun, _⟩ := peel (interpExpr_readOnly _ _) rest
   first
     | exact .add _ typed (checked_expr_bridgeTyped onlyScalars sameNames same aRun)
         (checked_expr_bridgeTyped onlyScalars sameNames same bRun)
     | exact .sub _ typed (checked_expr_bridgeTyped onlyScalars sameNames same aRun)
         (checked_expr_bridgeTyped onlyScalars sameNames same bRun)
     | exact .mul _ typed (checked_expr_bridgeTyped onlyScalars sameNames same aRun)
         (checked_expr_bridgeTyped onlyScalars sameNames same bRun)
     | exact .le _ typed (checked_expr_bridgeTyped onlyScalars sameNames same aRun)
         (checked_expr_bridgeTyped onlyScalars sameNames same bRun)
     | exact .lt _ typed (checked_expr_bridgeTyped onlyScalars sameNames same aRun)
         (checked_expr_bridgeTyped onlyScalars sameNames same bRun)
     | exact .ge _ typed (checked_expr_bridgeTyped onlyScalars sameNames same aRun)
         (checked_expr_bridgeTyped onlyScalars sameNames same bRun)
     | exact .gt _ typed (checked_expr_bridgeTyped onlyScalars sameNames same aRun)
         (checked_expr_bridgeTyped onlyScalars sameNames same bRun)
     | exact .equal _ typed (checked_expr_bridgeTyped onlyScalars sameNames same aRun)
         (checked_expr_bridgeTyped onlyScalars sameNames same bRun)
     | exact .notEqual _ typed (checked_expr_bridgeTyped onlyScalars sameNames same aRun)
         (checked_expr_bridgeTyped onlyScalars sameNames same bRun)))

set_option hygiene false in
macro "unaryTyped" : tactic => `(tactic|
  (obtain ⟨_, sorted, rest⟩ := peel (sourceSort_readOnly _) run
   have typed := sourceSort_bridgeType onlyScalars same sameNames sorted
   obtain ⟨_, sub, _⟩ := peel (interpExpr_readOnly _ _) rest
   first
     | exact .neg _ typed (checked_expr_bridgeTyped onlyScalars sameNames same sub)
     | exact .old _ typed (checked_expr_bridgeTyped onlyScalars sameNames same sub)))

private theorem evalSort_nat (names : GlobalContext) (r : SourceRange) :
    evalSort names (.nat r) = some .nat := by
  unfold evalSort
  rfl

private theorem evalSort_map (names : GlobalContext) (r : SourceRange) (value key : Boole.Type) :
    evalSort names (.Map r value key) =
      (do let k ← evalSort names key; let v ← evalSort names value; pure (k.map v)) := by
  conv => lhs; unfold evalSort

private theorem evalSort_seq (names : GlobalContext) (r : SourceRange) (element : Boole.Type) :
    evalSort names (.Sequence r element) = (evalSort names element).map ValueType.sequence := by
  conv => lhs; unfold evalSort

private theorem clash_produced {supports : ValueType → Bool}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {scope : Scope} (same : scope.supportsType = supports) {ty : Boole.Type} {out produced : ValueType}
    {final : Scope} (run : sourceSort ty scope = .ok (out, final)) (eq : out = produced)
    (bad : produced ≠ .int ∧ produced ≠ .bool) : False :=
  sort_clash onlyScalars same run (by simpa [eq] using bad)

private theorem nat_blocked {supports : ValueType → Bool}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {scope : Scope} (same : scope.supportsType = supports) {out : ValueType} {final : Scope}
    (run : sourceSort (.nat default) scope = .ok (out, final)) : False := by
  have ev := (sourceSort_eval run).1
  have outNat : out = .nat :=
    (Option.some.inj ((evalSort_nat scope.names default).symm.trans ev)).symm
  exact clash_produced onlyScalars same run outNat (by
    simp [ValueType.nat, ValueType.int, ValueType.bool])

private theorem map_blocked {supports : ValueType → Bool}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {scope : Scope} (same : scope.supportsType = supports) {r : SourceRange} {value key : Boole.Type}
    {out : ValueType} {final : Scope}
    (run : sourceSort (.Map r value key) scope = .ok (out, final)) : False := by
  have ev := (sourceSort_eval run).1
  rw [evalSort_map] at ev
  cases hk : evalSort scope.names key <;> simp [hk, Option.bind] at ev
  cases hv : evalSort scope.names value <;> simp [hv, Option.bind, Option.map] at ev
  exact clash_produced onlyScalars same run ev.symm (by
    simp [ValueType.map, ValueType.int, ValueType.bool])

private theorem seq_blocked {supports : ValueType → Bool}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {scope : Scope} (same : scope.supportsType = supports) {r : SourceRange} {element : Boole.Type}
    {out : ValueType} {final : Scope}
    (run : sourceSort (.Sequence r element) scope = .ok (out, final)) : False := by
  have ev := (sourceSort_eval run).1
  rw [evalSort_seq] at ev
  cases he : evalSort scope.names element <;> simp [he, Option.map] at ev
  exact clash_produced onlyScalars same run ev.symm (by
    simp [ValueType.sequence, ValueType.int, ValueType.bool])

set_option maxHeartbeats 2000000 in
private theorem checked_expr_bridgeTyped {supports : ValueType → Bool} {names : GlobalContext}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {e : Boole.Expr} {scope final : Scope} {out : Unit}
    (sameNames : scope.names = names) (same : scope.supportsType = supports)
    (run : interpExpr (checkingInterpretation supports) e scope = .ok (out, final)) :
    BridgeTyped names e := by
  cases e
  all_goals rw [interpExpr.eq_def] at run
  all_goals dsimp only at run
  case natToInt | strLit | bv1Lit | bv8Lit | bv16Lit | bv32Lit | bv64Lit | bv128Lit | app | btrue
    | bfalse | fvar | bvar => leaf
  case not _ a =>
    obtain ⟨_, sub, _⟩ := peel (interpExpr_readOnly _ a) run
    exact .not _ (checked_expr_bridgeTyped onlyScalars sameNames same sub)
  case and _ _ _ | or _ _ _ | implies _ _ _ | equiv _ _ _ => boolBin
  case neg_expr _ _ _ | old _ _ _ => unaryTyped
  case add_expr _ _ _ _ | sub_expr _ _ _ _ | mul_expr _ _ _ _ | le _ _ _ _ | lt _ _ _ _ | ge _ _ _ _
    | gt _ _ _ _ | equal _ _ _ _ | not_equal _ _ _ _ => typedBin
  case «if» _ _ _ _ _ =>
    obtain ⟨_, sorted, rest⟩ := peel (sourceSort_readOnly _) run
    have typed := sourceSort_bridgeType onlyScalars same sameNames sorted
    obtain ⟨_, cRun, rest⟩ := peel (interpExpr_readOnly _ _) rest
    obtain ⟨_, yesRun, rest⟩ := peel (interpExpr_readOnly _ _) rest
    obtain ⟨_, noRun, _⟩ := peel (interpExpr_readOnly _ _) rest
    exact .ite _ typed (checked_expr_bridgeTyped onlyScalars sameNames same cRun)
      (checked_expr_bridgeTyped onlyScalars sameNames same yesRun)
      (checked_expr_bridgeTyped onlyScalars sameNames same noRun)
  case nat_fromInt _ _ | nat_toInt _ _ | nat_add _ _ _ | nat_sub _ _ _ | nat_mul _ _ _ | nat_div _ _ _
    | nat_mod _ _ _ | nat_lt _ _ _ | nat_le _ _ _ | nat_gt _ _ _ | nat_ge _ _ =>
    obtain ⟨_, sorted, _⟩ := peel (sourceSort_readOnly _) run
    exact False.elim (nat_blocked onlyScalars same sorted)
  case map_get _ _ _ _ _ | map_set _ _ _ _ _ _ | map_const _ _ _ _ =>
    obtain ⟨_, sorted, _⟩ := peel (sourceSort_readOnly _) run
    exact False.elim (map_blocked onlyScalars same sorted)
  case seq_empty _ _ | seq_length _ _ _ | seq_append _ _ _ _ | seq_build _ _ _ _ | seq_empty_int _ =>
    obtain ⟨_, sorted, _⟩ := peel (sourceSort_readOnly _) run
    exact False.elim (seq_blocked onlyScalars same sorted)
  all_goals
    simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, StateT.bind, Except.bind,
      Functor.map, Except.map] at run
termination_by sizeOf e
decreasing_by all_goals simp_all <;> omega

def BridgeMeasure (names : GlobalContext) : Option (BooleDDM.Measure SourceRange) → Prop
  | none => True
  | some (.measure_mk _ expression) => BridgeTyped names expression

def BridgeInvariants (names : GlobalContext) : BooleDDM.Invariants SourceRange → Prop
  | .nilInvariants _ => True
  | .consInvariants _ _ expression rest =>
      BridgeTyped names expression ∧ BridgeInvariants names rest

/-- A deterministic guard carries its condition; a nondeterministic guard does not. -/
def BridgeGuard (names : GlobalContext) : BooleDDM.ExprOrNondet SourceRange → Prop
  | .condDet _ expression => BridgeTyped names expression
  | .condNondet _ => True

mutual

/-- The else branch of a conditional, when it has a block. -/
inductive BridgeElse (names : GlobalContext) : BooleDDM.Else SourceRange → Prop where
  | none {r} : BridgeElse names (.else0 r)
  | some {r body} : BridgeBlock names body → BridgeElse names (.else1 r body)

inductive BridgeStatement (names : GlobalContext) : BooleDDM.Statement SourceRange → Prop where
  | var (r a ds) : BridgeStatement names (.varStatement r a ds)
  | init (r a ty name expression) : BridgeTyped names expression →
      BridgeStatement names (.initStatement r a ty name expression)
  | assign (r a b lr name expression) : BridgeTyped names expression →
      BridgeStatement names (.assign r a b (.lhsIdent lr name) expression)
  | havoc (r a name) : BridgeStatement names (.havoc_statement r a name)
  | assert (r a label expression) : BridgeTyped names expression →
      BridgeStatement names (.assert r a label expression)
  | assume (r a label expression) : BridgeTyped names expression →
      BridgeStatement names (.assume r a label expression)
  | branch (r a guard yes no) : BridgeGuard names guard → BridgeBlock names yes →
      BridgeElse names no → BridgeStatement names (.if_statement r a guard yes no)
  | «while» (r a guard decreases invariants body) : BridgeGuard names guard →
      BridgeMeasure names decreases.val → BridgeInvariants names invariants → BridgeBlock names body →
      BridgeStatement names (.while_statement r a guard decreases invariants body)
  | block (r a name body) : BridgeBlock names body →
      BridgeStatement names (.block_statement r a name body)
  | exit (r a name) : BridgeStatement names (.exit_statement r a name)

inductive BridgeBlock (names : GlobalContext) : BooleDDM.Block SourceRange → Prop where
  | block {r r' ss} : (∀ s ∈ ss.toList, BridgeStatement names s) →
      BridgeBlock names (.block r ⟨r', ss⟩)

end

theorem BridgeBlock.statements {names} {r r' : SourceRange}
    {ss : Array (BooleDDM.Statement SourceRange)} (h : BridgeBlock names (.block r ⟨r', ss⟩)) :
    ∀ s ∈ ss.toList, BridgeStatement names s := by
  cases h; assumption

theorem BridgeStatement.init_typed {names r a ty name expression}
    (h : BridgeStatement names (.initStatement r a ty name expression)) :
    BridgeTyped names expression := by cases h; assumption

theorem BridgeStatement.assign_typed {names r a b lr name expression}
    (h : BridgeStatement names (.assign r a b (.lhsIdent lr name) expression)) :
    BridgeTyped names expression := by cases h; assumption

theorem BridgeStatement.assert_typed {names r a label expression}
    (h : BridgeStatement names (.assert r a label expression)) : BridgeTyped names expression := by
  cases h; assumption

theorem BridgeStatement.assume_typed {names r a label expression}
    (h : BridgeStatement names (.assume r a label expression)) : BridgeTyped names expression := by
  cases h; assumption

theorem BridgeStatement.branch_inv {names r a guard yes no}
    (h : BridgeStatement names (.if_statement r a guard yes no)) :
    BridgeGuard names guard ∧ BridgeBlock names yes ∧ BridgeElse names no := by
  cases h; exact ⟨by assumption, by assumption, by assumption⟩

theorem BridgeStatement.while_inv {names r a guard decreases invariants body}
    (h : BridgeStatement names (.while_statement r a guard decreases invariants body)) :
    BridgeGuard names guard ∧ BridgeMeasure names decreases.val ∧
      BridgeInvariants names invariants ∧ BridgeBlock names body := by
  cases h; exact ⟨by assumption, by assumption, by assumption, by assumption⟩

theorem BridgeStatement.block_body {names r a name body}
    (h : BridgeStatement names (.block_statement r a name body)) : BridgeBlock names body := by
  cases h; assumption

theorem BridgeGuard.typed {names g expression}
    (h : BridgeGuard names (.condDet g expression)) : BridgeTyped names expression := by
  simpa [BridgeGuard] using h

theorem BridgeElse.block {names n body} (h : BridgeElse names (.else1 n body)) :
    BridgeBlock names body := by
  cases h; assumption

def BridgeSpecElt (names : GlobalContext) : BooleDDM.SpecElt SourceRange → Prop
  | .requires_spec _ _ _ expression | .ensures_spec _ _ _ expression => BridgeTyped names expression
  | .modifies_spec _ _ => True

def BridgeSpec (names : GlobalContext) : Option (BooleDDM.Spec SourceRange) → Prop
  | none => True
  | some (.spec_mk _ elements) => ∀ element ∈ elements.val.toList, BridgeSpecElt names element

private theorem addLocal_iface {range : SourceRange} {name : String} {ty : Boole.Type}
    {initial final : Scope} {binding : Binding}
    (success : addLocal range name ty initial = .ok (binding, final)) :
    final.names = initial.names ∧ final.supportsType = initial.supportsType := by
  unfold addLocal at success
  obtain ⟨_, middle, resolved, added⟩ := split_run success
  have sorted := sourceSort_readOnly ty _ _ _ resolved
  subst sorted
  obtain ⟨_, afterFresh, checked, installed⟩ := split_run added
  have freshened := (fresh_names checked).2.2
  subst freshened
  obtain ⟨_, _, modified, ended⟩ := split_run installed
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
  repeat' first | exact readOnly_pure _ | exact readOnly_reject _ _ | (split <;> skip)

private theorem condition_readOnly (I : Interpretation) (guard : BooleDDM.ExprOrNondet SourceRange) :
    ReadOnly (condition I guard) := by
  cases guard
  · exact (interpExpr_readOnly I _).bind fun _ => readOnly_pure _
  · exact readOnly_pure _

private theorem checkInvariants_readOnly (I : Interpretation)
    (invariants : BooleDDM.Invariants SourceRange) : ReadOnly (checkInvariants I invariants) := by
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

private theorem checked_invariants {supports : ValueType → Bool} {names : GlobalContext}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {inv : BooleDDM.Invariants SourceRange} {scope final : Scope} {out : Unit}
    (sameNames : scope.names = names) (same : scope.supportsType = supports)
    (run : checkInvariants (checkingInterpretation supports) inv scope = .ok (out, final)) :
    BridgeInvariants names inv ∧ final = scope := by
  induction inv with
  | nilInvariants _ =>
    rw [checkInvariants] at run
    exact ⟨trivial, pure_state run⟩
  | consInvariants _ _ expression _ ih =>
    rw [checkInvariants] at run
    obtain ⟨_, exprRun, restRun⟩ := peel (interpExpr_readOnly _ expression) run
    obtain ⟨restTyped, eq⟩ := ih restRun
    exact ⟨⟨checked_expr_bridgeTyped onlyScalars sameNames same exprRun, restTyped⟩, eq⟩

private theorem guard_bridge {supports : ValueType → Bool} {names : GlobalContext}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {guard : BooleDDM.ExprOrNondet SourceRange} {scope final : Scope} {out}
    (sameNames : scope.names = names) (same : scope.supportsType = supports)
    (run : condition (checkingInterpretation supports) guard scope = .ok (out, final)) :
    BridgeGuard names guard := by
  cases guard with
  | condNondet _ => simp [BridgeGuard]
  | condDet _ expression =>
    rw [condition] at run
    obtain ⟨_, exprRun, _⟩ := peel (interpExpr_readOnly _ expression) run
    simpa [BridgeGuard] using checked_expr_bridgeTyped onlyScalars sameNames same exprRun

private theorem block_statements_smaller (r r' : SourceRange)
    (ss : Array (BooleDDM.Statement SourceRange)) :
    sizeOf ss.toList < sizeOf (BooleDDM.Block.block r
      (⟨r', ss⟩ : Ann (Array (BooleDDM.Statement SourceRange)) SourceRange)) := by
  have : sizeOf ss = 1 + sizeOf ss.toList := rfl
  first
    | simp [BooleDDM.Block.block.sizeOf_spec, StrataDDM.Ann.mk.sizeOf_spec, this]
    | simp [BooleDDM.Block.block.sizeOf_spec, this]
  omega

private theorem kept_scope {scope final : Scope} (eq : final = scope) :
    final.supportsType = scope.supportsType ∧ final.names = scope.names := by
  cases eq; exact ⟨rfl, rfl⟩

set_option maxHeartbeats 2000000 in
mutual

private theorem checked_stmt {supports : ValueType → Bool} {names : GlobalContext}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {statement : BooleDDM.Statement SourceRange} {scope final : Scope} {out : Unit}
    (sameNames : scope.names = names) (types : scope.supportsType = supports)
    (run : interpStmt (checkingInterpretation supports) statement scope = .ok (out, final)) :
    BridgeStatement names statement ∧ final.supportsType = scope.supportsType ∧
      final.names = scope.names := by
  cases statement with
  | varStatement range _ declarations =>
    rw [interpStmt.eq_def] at run; dsimp only at run
    obtain ⟨_, mid, looped, done⟩ := split_run run
    obtain ⟨namesEq, typesEq⟩ :=
      declarations_iface _ (bindings declarations) range scope mid _ looped
    rw [pure_state done]
    exact ⟨.var _ _ _, typesEq, namesEq⟩
  | initStatement _ _ _ _ expression =>
    rw [interpStmt.eq_def] at run; dsimp only at run
    obtain ⟨_, exprRun, rest⟩ := peel (interpExpr_readOnly _ expression) run
    obtain ⟨_, _, added, done⟩ := split_run rest
    obtain ⟨namesEq, typesEq⟩ := addLocal_iface added
    rw [pure_state done]
    exact ⟨.init _ _ _ _ _ (checked_expr_bridgeTyped onlyScalars sameNames types exprRun),
      typesEq, namesEq⟩
  | assign _ _ _ lhs expression =>
    rw [interpStmt.eq_def] at run
    cases lhs with
    | lhsIdent _ _ =>
      dsimp only at run
      obtain ⟨_, mid, resolved, rest⟩ := split_run run
      have back := resolveVariable_readOnly _ _ _ _ _ _ resolved
      subst back
      obtain ⟨_, exprRun, done⟩ := peel (interpExpr_readOnly _ expression) rest
      exact ⟨.assign _ _ _ _ _ _ (checked_expr_bridgeTyped onlyScalars sameNames types exprRun),
        kept_scope (pure_state done)⟩
    | lhsArray _ _ _ _ =>
      dsimp only at run
      simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, StateT.bind, Except.bind,
        Functor.map, Except.map] at run
  | havoc_statement _ _ _ =>
    rw [interpStmt.eq_def] at run; dsimp only at run
    obtain ⟨_, mid, resolved, done⟩ := split_run run
    have back := resolveVariable_readOnly _ _ _ _ _ _ resolved
    subst back
    exact ⟨.havoc _ _ _, kept_scope (pure_state done)⟩
  | assert _ annotations _ expression =>
    cases ann : annotations.val with
    | some _ =>
      rw [interpStmt.eq_def] at run
      simp [ann, Option.isSome, reject, bind, StateT.bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw, StateT.lift, Function.comp_apply] at run
    | none =>
      rw [interpStmt.eq_def] at run
      simp only [ann, Option.isSome, Bool.false_eq_true, ite_false, bind, StateT.bind, Except.bind] at run
      obtain ⟨_, exprRun, done⟩ := peel (interpExpr_readOnly _ expression) run
      exact ⟨.assert _ _ _ _ (checked_expr_bridgeTyped onlyScalars sameNames types exprRun),
        kept_scope (pure_state done)⟩
  | assume _ _ _ expression =>
    rw [interpStmt.eq_def] at run; dsimp only at run
    obtain ⟨_, exprRun, done⟩ := peel (interpExpr_readOnly _ expression) run
    exact ⟨.assume _ _ _ _ (checked_expr_bridgeTyped onlyScalars sameNames types exprRun),
      kept_scope (pure_state done)⟩
  | if_statement _ _ guard yes no =>
    rw [interpStmt.eq_def] at run; dsimp only at run
    obtain ⟨_, guardRun, rest⟩ := peel (condition_readOnly _ guard) run
    obtain ⟨_, yesRun, rest⟩ := peel (interpBlock_restores _ yes) rest
    obtain ⟨yesTyped, _, _⟩ := checked_block onlyScalars sameNames types yesRun
    have guarded := guard_bridge onlyScalars sameNames types guardRun
    cases no with
    | else0 _ =>
      simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at rest
      have eq := (congrArg Prod.snd (Except.ok.inj rest)).symm
      subst eq
      exact ⟨.branch _ _ _ _ _ guarded yesTyped .none, rfl, rfl⟩
    | else1 _ body =>
      obtain ⟨_, noRun, done⟩ := peel (interpBlock_restores _ body) rest
      obtain ⟨noTyped, _, _⟩ := checked_block onlyScalars sameNames types noRun
      simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at done
      have eq := (congrArg Prod.snd (Except.ok.inj done)).symm
      subst eq
      exact ⟨.branch _ _ _ _ _ guarded yesTyped (.some noTyped), rfl, rfl⟩
  | while_statement _ _ guard decreases invariants body =>
    rw [interpStmt.eq_def] at run; dsimp only at run
    obtain ⟨_, guardRun, rest⟩ := peel (condition_readOnly _ guard) run
    have guarded := guard_bridge onlyScalars sameNames types guardRun
    cases mv : decreases.val with
    | none =>
      simp only [mv] at rest
      obtain ⟨_, invRun, rest⟩ := peel (checkInvariants_readOnly _ invariants) rest
      obtain ⟨invTyped, _⟩ := checked_invariants onlyScalars sameNames types invRun
      obtain ⟨_, bodyRun, done⟩ := peel (interpBlock_restores _ body) rest
      obtain ⟨bodyTyped, _, _⟩ := checked_block onlyScalars sameNames types bodyRun
      simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at done
      have eq := (congrArg Prod.snd (Except.ok.inj done)).symm
      subst eq
      exact ⟨.«while» _ _ _ _ _ _ guarded (by simp [BridgeMeasure, mv]) invTyped bodyTyped, rfl, rfl⟩
    | some m =>
      cases m with
      | measure_mk _ expression =>
        simp only [mv] at rest
        obtain ⟨_, exprRun, rest⟩ := peel (interpExpr_readOnly _ expression) rest
        have measured : BridgeMeasure names decreases.val := by
          simpa [BridgeMeasure, mv] using checked_expr_bridgeTyped onlyScalars sameNames types exprRun
        obtain ⟨_, invRun, rest⟩ := peel (checkInvariants_readOnly _ invariants) rest
        obtain ⟨invTyped, _⟩ := checked_invariants onlyScalars sameNames types invRun
        obtain ⟨_, bodyRun, done⟩ := peel (interpBlock_restores _ body) rest
        obtain ⟨bodyTyped, _, _⟩ := checked_block onlyScalars sameNames types bodyRun
        simp only [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at done
        have eq := (congrArg Prod.snd (Except.ok.inj done)).symm
        subst eq
        exact ⟨.«while» _ _ _ _ _ _ guarded measured invTyped bodyTyped, rfl, rfl⟩
  | block_statement _ _ _ body =>
    rw [interpStmt.eq_def] at run; dsimp only at run
    obtain ⟨_, saved, done⟩ := peel (withScope_readOnly _) run
    obtain ⟨_, inner⟩ := withScope_success saved
    simp only [bind, StateT.bind, Except.bind, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, pure, StateT.pure, Except.pure] at inner
    obtain ⟨typed, _, _⟩ :=
      checked_block onlyScalars (by simpa using sameNames) (by simpa using types) inner
    exact ⟨.block _ _ _ _ typed, kept_scope (pure_state done)⟩
  | exit_statement _ _ _ =>
    rw [interpStmt.eq_def] at run; dsimp only at run
    obtain ⟨_, mid, got, rest⟩ := split_run run
    have fetched := readOnly_get _ _ _ got
    subst fetched
    split at rest
    · simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, StateT.bind, Except.bind,
        Functor.map, Except.map] at rest
    · exact ⟨.exit _ _ _, kept_scope (pure_state rest)⟩
  | _ =>
    rw [interpStmt.eq_def] at run; dsimp only at run
    simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, StateT.bind, Except.bind,
      Functor.map, Except.map] at run
termination_by sizeOf statement

private theorem checked_stmts {supports : ValueType → Bool} {names : GlobalContext}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    (statements : List (BooleDDM.Statement SourceRange)) {scope final : Scope} {out : Unit}
    (sameNames : scope.names = names) (types : scope.supportsType = supports)
    (run : interpStmts (checkingInterpretation supports) statements scope = .ok (out, final)) :
    (∀ s ∈ statements, BridgeStatement names s) ∧ final.supportsType = scope.supportsType ∧
      final.names = scope.names := by
  match statements with
  | [] =>
    rw [interpStmts.eq_def] at run
    exact ⟨fun _ mem => by simp at mem, kept_scope (pure_state run)⟩
  | statement :: rest =>
    rw [interpStmts.eq_def] at run; dsimp only at run
    obtain ⟨_, mid, headRun, tail⟩ := split_run run
    obtain ⟨typed, midTypes, midNames⟩ := checked_stmt onlyScalars sameNames types headRun
    obtain ⟨_, _, tailRun, done⟩ := split_run tail
    obtain ⟨restTyped, lastTypes, lastNames⟩ :=
      checked_stmts onlyScalars rest (midNames.trans sameNames) (midTypes.trans types) tailRun
    rw [pure_state done]
    refine ⟨?_, lastTypes.trans midTypes, lastNames.trans midNames⟩
    intro s mem
    rcases List.mem_cons.mp mem with rfl | later
    · exact typed
    · exact restTyped s later
termination_by sizeOf statements

private theorem checked_block {supports : ValueType → Bool} {names : GlobalContext}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {block : BooleDDM.Block SourceRange} {scope final : Scope} {out : Unit}
    (sameNames : scope.names = names) (types : scope.supportsType = supports)
    (run : interpBlock (checkingInterpretation supports) block scope = .ok (out, final)) :
    BridgeBlock names block ∧ final.supportsType = scope.supportsType ∧ final.names = scope.names := by
  have restored := interpBlock_restores _ block _ _ _ run
  unfold interpBlock at run
  obtain ⟨_, inner⟩ := withScope_success run
  cases block with
  | block r ann =>
    cases ann with
    | mk r' ss =>
      dsimp only at inner
      obtain ⟨_, _, stmtsRun, _⟩ := split_run inner
      obtain ⟨all, _, _⟩ := checked_stmts onlyScalars ss.toList sameNames types stmtsRun
      exact ⟨.block all, kept_scope restored⟩
termination_by sizeOf block
decreasing_by subst_eqs; exact block_statements_smaller r r' ss

end

private theorem forIn_preservesScope {α β : Type} (items : List α) (step : α → β → InterpM (ForInStep β))
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
      have stable := stepPreserves head before entry control middle first
      cases control with
      | done _ =>
        simp only [first, stable] at ran
        exact (congrArg Prod.snd (Except.ok.inj ran)).symm
      | yield next =>
        exact ih next entry
          (by simp only [first, stable, bind, StateT.bind, Except.bind, pure] at ran; exact ran)

private def modifiedNameStep (I : Interpretation) (range : SourceRange)
    (name : StrataDDM.Ann String SourceRange) (before : Contract I.Expression) :
    InterpM (ForInStep (Contract I.Expression)) := do
  if (findBinding name.val (← (get : InterpM Scope)).globals).isNone then
    reject range s!"Unknown modified global '{name.val}'"
  if !before.modifies.contains name.val then
    pure (.yield { before with modifies := before.modifies ++ [name.val] })
  else pure (.yield before)

private theorem modifiedNameStep_scope (I : Interpretation) (range : SourceRange)
    (name : StrataDDM.Ann String SourceRange) (before : Contract I.Expression) (state : Scope)
    (control : ForInStep (Contract I.Expression)) (after : Scope)
    (ran : modifiedNameStep I range name before state = .ok (control, after)) : after = state := by
  unfold modifiedNameStep at ran
  simp only [bind, StateT.bind, Except.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
    StateT.pure, Except.pure, reject, throw, throwThe, MonadExceptOf.throw, Function.comp_apply,
    StateT.lift, Functor.map, Except.map] at ran
  repeat' first
    | contradiction
    | exact (congrArg Prod.snd (Except.ok.inj ran)).symm
    | split at ran

private theorem forIn_spec {supports : ValueType → Bool} {names : GlobalContext}
    (elements : List (BooleDDM.SpecElt SourceRange))
    (step : BooleDDM.SpecElt SourceRange →
      Contract (checkingInterpretation supports).Expression →
      InterpM (ForInStep (Contract (checkingInterpretation supports).Expression)))
    (before : Contract (checkingInterpretation supports).Expression)
    (initial final : Scope) (result : Contract (checkingInterpretation supports).Expression)
    (sameNames : initial.names = names) (same : initial.supportsType = supports)
    (each : ∀ element acc state control next,
      step element acc state = .ok (control, next) →
      state.names = names → state.supportsType = supports →
      next = state ∧ BridgeSpecElt names element ∧ ∃ updated, control = .yield updated)
    (success : (forIn elements before step) initial = .ok (result, final)) :
    (∀ element ∈ elements, BridgeSpecElt names element) ∧ final = initial := by
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
      obtain ⟨stable, typed, found⟩ := each element before initial control next ran sameNames same
      obtain ⟨updated, yielded⟩ := found
      have continued : (forIn rest updated step) next = .ok (result, final) := by
        simp only [ran, yielded, bind, StateT.bind, Except.bind, pure] at success
        exact success
      have nextNames : next.names = names := by simp [stable, sameNames]
      have nextTypes : next.supportsType = supports := by simp [stable, same]
      exact ⟨fun target member => by
        rcases List.mem_cons.mp member with rfl | later
        · exact typed
        · exact (ih updated next nextNames nextTypes continued).1 target later,
        ((ih updated next nextNames nextTypes continued).2).trans stable⟩

private theorem checked_contract {supports : ValueType → Bool} {names : GlobalContext}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {specification : Option (BooleDDM.Spec SourceRange)} {scope final : Scope}
    {contract : Contract (checkingInterpretation supports).Expression}
    (sameNames : scope.names = names) (same : scope.supportsType = supports)
    (run : interpContract (checkingInterpretation supports) specification scope = .ok (contract, final)) :
    BridgeSpec names specification ∧ final = scope := by
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
          | .modifies_spec range modified => do
              let updated ← forIn modified.val before
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
          sameNames same ?each loopPair
        exact ⟨by simpa [BridgeSpec] using collected.1,
          (congrArg Prod.snd (Except.ok.inj run)).symm.trans collected.2⟩
        case each =>
          intro element before state control next ran hereNames hereTypes
          cases element with
          | modifies_spec range modified =>
            simp only [step, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
            cases inner : forIn modified.val before
                (modifiedNameStep (checkingInterpretation supports) range) state with
            | error _ => rw [inner] at ran; simp at ran
            | ok pair =>
              obtain ⟨updated, afterInner⟩ := pair
              have listRun : forIn modified.val.toList before
                  (modifiedNameStep (checkingInterpretation supports) range) state =
                  .ok (updated, afterInner) := by
                have inner0 := inner
                have sameArray : modified.val.toList.toArray = modified.val :=
                  Array.toArray_toList (xs := modified.val)
                have rewriteFor := List.forIn_toArray (m := InterpM)
                  (β := Contract (checkingInterpretation supports).Expression)
                  (f := modifiedNameStep (checkingInterpretation supports) range)
                  modified.val.toList before
                rw [← sameArray] at inner0
                exact rewriteFor ▸ inner0
              have stable := forIn_preservesScope _ _
                (fun n acc s c t h => modifiedNameStep_scope _ _ n acc s c t h) _ _ _ _ listRun
              simp only [inner, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure] at ran
              have fields := Except.ok.inj ran
              exact ⟨(congrArg Prod.snd fields).symm.trans stable, trivial, updated,
                (congrArg Prod.fst fields).symm⟩
          | requires_spec _ _ _ expression | ensures_spec _ _ _ expression =>
            cases exprRun : interpExpr (checkingInterpretation supports) expression state with
            | error _ => simp [step, bind, StateT.bind, Except.bind, exprRun] at ran
            | ok pair =>
              obtain ⟨_, afterExpr⟩ := pair
              have back := interpExpr_readOnly _ _ _ _ _ exprRun
              subst back
              simp only [step, bind, StateT.bind, Except.bind, exprRun, pure, StateT.pure,
                Except.pure] at ran
              have fields := Except.ok.inj ran
              exact ⟨(congrArg Prod.snd fields).symm,
                by simpa [BridgeSpecElt] using
                  checked_expr_bridgeTyped onlyScalars hereNames hereTypes exprRun,
                _, (congrArg Prod.fst fields).symm⟩

private theorem inputBindings_iface (parameters : BooleDDM.Bindings SourceRange) {scope final : Scope}
    {bindings : List Binding} (run : inputBindings parameters scope = .ok (bindings, final)) :
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
      cases pure_state run
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
      obtain ⟨namesEq, typesEq⟩ := ih ran
      cases Except.ok.inj ended
      exact ⟨namesEq.trans kept.1, typesEq.trans kept.2⟩

private theorem outputBindings_iface (outputs : BooleDDM.MonoDeclList SourceRange) {scope final : Scope}
    {bindings : List Binding} (run : outputBindings outputs scope = .ok (bindings, final)) :
    final.names = scope.names ∧ final.supportsType = scope.supportsType := by
  induction outputs generalizing scope bindings final with
  | monoDeclAtom range binding =>
    cases binding
    rw [outputBindings] at run
    obtain ⟨_, middle, checked, ended⟩ := split_run run
    cases Except.ok.inj ended
    exact addLocal_iface checked
  | monoDeclPush range rest binding ih =>
    cases binding
    rw [outputBindings] at run
    obtain ⟨_, middle, prior, added⟩ := split_run run
    obtain ⟨keptNames, keptTypes⟩ := ih prior
    obtain ⟨_, _, checked, ended⟩ := split_run added
    cases Except.ok.inj ended
    obtain ⟨namesEq, typesEq⟩ := addLocal_iface checked
    exact ⟨namesEq.trans keptNames, typesEq.trans keptTypes⟩

private theorem checked_proc {supports : ValueType → Bool} {names : GlobalContext}
    (onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool)
    {range : SourceRange} {name : String} {typeArgs : Option (BooleDDM.TypeArgs SourceRange)}
    {parameters : BooleDDM.Bindings SourceRange}
    {outputs : Option (BooleDDM.MonoDeclList SourceRange)}
    {specification : Option (BooleDDM.Spec SourceRange)} {block : BooleDDM.Block SourceRange}
    {scope final : Scope}
    {procedure : InterpProcedure (checkingInterpretation supports).Expression
      (checkingInterpretation supports).Statement}
    (sameNames : scope.names = names) (same : scope.supportsType = supports)
    (run : interpProc (checkingInterpretation supports) range name typeArgs parameters outputs
      specification (some block) scope = .ok (procedure, final)) :
    BridgeBlock names block ∧ BridgeSpec names specification := by
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
        | cases pure_state readOutputs; exact ⟨rfl, rfl⟩
        | exact outputBindings_iface _ readOutputs
      obtain ⟨outNames, outTypes⟩ := outputKept
      obtain ⟨contract, afterContract, readContract, ran⟩ := split_run ran
      have entryNames : afterOutputs.names = names := outNames.trans (inputNames.trans sameNames)
      have entryTypes : afterOutputs.supportsType = supports := outTypes.trans (inputTypes.trans same)
      obtain ⟨specTyped, contractSame⟩ := checked_contract onlyScalars entryNames entryTypes readContract
      subst afterContract
      let bodyEntry : Scope := { afterOutputs with modifies := contract.modifies, labels := [name] }
      have entryEq : bodyEntry = { afterOutputs with modifies := contract.modifies, labels := [name] } := rfl
      simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, bind, StateT.bind,
        Except.bind, pure, StateT.pure, Except.pure] at ran
      rw [← entryEq] at ran
      cases bodyRan : interpBlock (checkingInterpretation supports) block bodyEntry with
      | error _ => simp [bodyRan] at ran
      | ok _ =>
        obtain ⟨typed, _, _⟩ := checked_block onlyScalars
          (by simpa [bodyEntry] using entryNames) (by simpa [bodyEntry] using entryTypes) bodyRan
        exact ⟨typed, specTyped⟩

private def ScopeCarried (supports : ValueType → Bool) (names : GlobalContext) (scope : Scope) : Prop :=
  scope.supportsType = supports ∧ scope.names = names

private theorem yield_carried {β : Type} {supports : ValueType → Bool} {names : GlobalContext}
    {state next : Scope} {control : ForInStep β} {value : β} (carried : ScopeCarried supports names state)
    (ran : (pure (ForInStep.yield value) : InterpM (ForInStep β)) state = .ok (control, next)) :
    ∃ updated, control = ForInStep.yield updated ∧ ScopeCarried supports names next := by
  simp only [pure, StateT.pure, Except.pure] at ran
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj ran)
  exact ⟨value, rfl, carried⟩

private def varStep (I : Interpretation) (procedures : List (InterpProcedure I.Expression I.Statement))
    (range : SourceRange) (name : StrataDDM.Ann String SourceRange) (ty : Boole.Type)
    (globals : GlobalContext) : InterpM (ForInStep (List (InterpProcedure I.Expression I.Statement))) := do
  if retainLegacyGlobal globals ty then
    if !procedures.isEmpty then reject range "Declare globals before procedures"
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
  split at ran
  · split at ran
    · simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, Function.comp_apply,
        Functor.map, Except.map, bind, StateT.bind, Except.bind] at ran
    · obtain ⟨_, midSort, sorted, rest⟩ := split_run ran
      have sortedBack := sourceSort_readOnly ty _ _ _ sorted
      subst sortedBack
      obtain ⟨_, midFresh, freshened, rest⟩ := split_run rest
      have freshBack := (fresh_names freshened).2.2
      simp [freshened] at rest
      obtain ⟨controlEq, nextEq⟩ := Prod.mk.inj (Except.ok.inj rest)
      refine ⟨procedures, controlEq.symm, ?_⟩
      cases nextEq
      subst freshBack
      simpa [ScopeCarried] using carried
  · exact yield_carried carried ran

private def procStep (I : Interpretation) (range : SourceRange) (name : String) (rejectDecreases : Bool)
    (types : Option (BooleDDM.TypeArgs SourceRange)) (inputs : BooleDDM.Bindings SourceRange)
    (outputs : Option (BooleDDM.MonoDeclList SourceRange))
    (spec : Option (BooleDDM.Spec SourceRange)) (body : Option (BooleDDM.Block SourceRange))
    (procedures : List (InterpProcedure I.Expression I.Statement)) :
    InterpM (ForInStep (List (InterpProcedure I.Expression I.Statement))) := do
  if rejectDecreases then reject range "Procedure decreases clauses are outside this fragment"
  if procedures.any (fun p => p.name == name) then reject range "Duplicate procedure name"
  let procedure ← interpProc I range name types inputs outputs spec body
  pure (.yield (procedures ++ [procedure]))

private theorem procStep_facts {supports : ValueType → Bool} {globals : GlobalContext}
    (I : Interpretation) (range : SourceRange) (name : String) (rejectDecreases : Bool)
    (types : Option (BooleDDM.TypeArgs SourceRange)) (inputs : BooleDDM.Bindings SourceRange)
    (outputs : Option (BooleDDM.MonoDeclList SourceRange))
    (spec : Option (BooleDDM.Spec SourceRange)) (body : Option (BooleDDM.Block SourceRange))
    (procedures : List (InterpProcedure I.Expression I.Statement)) {state next : Scope}
    {control : ForInStep (List (InterpProcedure I.Expression I.Statement))}
    (carried : ScopeCarried supports globals state)
    (ran : procStep I range name rejectDecreases types inputs outputs spec body procedures state =
      .ok (control, next)) :
    (∃ updated, control = .yield updated ∧ ScopeCarried supports globals next) ∧
      ∃ procedure middle, interpProc I range name types inputs outputs spec body state =
        .ok (procedure, middle) := by
  unfold procStep at ran
  split at ran
  · simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, Function.comp_apply,
      Functor.map, Except.map, bind, StateT.bind, Except.bind] at ran
  · split at ran
    · simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, Function.comp_apply,
        Functor.map, Except.map, bind, StateT.bind, Except.bind] at ran
    · obtain ⟨procedure, middle, called, rest⟩ := split_run ran
      have back : middle = state := withScope_restores called
      subst middle
      exact ⟨yield_carried carried rest, procedure, state, called⟩

private def programStep (I : Interpretation) (globals : GlobalContext)
    (command : BooleDDM.Command SourceRange)
    (procedures : List (InterpProcedure I.Expression I.Statement)) :
    InterpM (ForInStep (List (InterpProcedure I.Expression I.Statement))) :=
  match command with
  | .command_typedecl .. => pure (.yield procedures)
  | .command_var range (.bind_mk _ name _ ty) => varStep I procedures range name ty globals
  | .boole_procedure range name types inputs outputs decreases spec body =>
      procStep I range name.val decreases.val.isSome types.val inputs outputs.val spec.val body.val
        procedures
  | .command_procedure range _ name types inputs spec body =>
      procStep I range name.val false types.val inputs none spec.val body.val procedures
  | _ => reject default s!"Unsupported declaration: {repr command}"

private theorem programStep_carried {supports : ValueType → Bool} {globals : GlobalContext}
    (I : Interpretation) (command : BooleDDM.Command SourceRange)
    (procedures : List (InterpProcedure I.Expression I.Statement)) {state next : Scope}
    {control : ForInStep (List (InterpProcedure I.Expression I.Statement))}
    (carried : ScopeCarried supports globals state)
    (ran : programStep I globals command procedures state = .ok (control, next)) :
    ∃ updated, control = .yield updated ∧ ScopeCarried supports globals next := by
  unfold programStep at ran
  split at ran <;> first
    | exact yield_carried carried ran
    | exact varStep_carried I procedures _ _ _ carried ran
    | exact (procStep_facts I _ _ _ _ _ _ _ _ _ carried ran).1
    | (simp [reject, throw, throwThe, MonadExceptOf.throw, StateT.lift, Function.comp_apply,
        Functor.map, Except.map, bind, StateT.bind, Except.bind] at ran <;> contradiction)

private theorem forIn_member_carried {α β : Type} {supports : ValueType → Bool} {names : GlobalContext}
    (items : List α) (step : α → β → InterpM (ForInStep β)) (before : β) (initial final : Scope)
    (result : β) (start : ScopeCarried supports names initial)
    (success : (forIn items before step) initial = .ok (result, final))
    (keeps : ∀ item acc state control next, ScopeCarried supports names state →
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
      · exact ih updated next carriedNext
          (by simp only [ran, yielded, bind, StateT.bind, Except.bind, pure] at success; exact success)
          later

private theorem fragment_procedure_bridge {source : Boole.Program} {names : GlobalContext}
    {command : BooleDDM.Command SourceRange} (fragment : sourceInFragment source names)
    (member : match source with | .prog _ declarations => command ∈ declarations.val.toList) :
    match command with
    | .boole_procedure _ _ _ _ _ _ spec body =>
        ∀ block, body.val = some block → BridgeBlock names block ∧ BridgeSpec names spec.val
    | .command_procedure _ _ _ _ _ spec body =>
        ∀ block, body.val = some block → BridgeBlock names block ∧ BridgeSpec names spec.val
    | _ => True := by
  let supports := fun ty : ValueType => ty == .int || ty == .bool
  have onlyScalars : ∀ ty, supports ty = true → ty = .int ∨ ty = .bool := by
    intro _ ok; simpa [supports, Bool.or_eq_true, beq_iff_eq] using ok
  cases source with
  | prog range declarations =>
    dsimp [sourceInFragment] at fragment
    have present : command ∈ declarations.val.toList := by simpa using member
    have checked : checkFragment supports (.prog range declarations) names = true := by
      simpa [supports] using fragment.2
    cases programRun : interpProgram (checkingInterpretation supports) (.prog range declarations) names with
    | error _ => simp [checkFragment, Except.isOk, Except.toBool, programRun] at checked
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
            declarations.val.toList (programStep (checkingInterpretation supports) names) [] entry
            stepResult.2 stepResult.1 start loopRan
            (fun command procedures state control next carried ran =>
              programStep_carried (checkingInterpretation supports) command procedures carried ran)
            present
          cases command
          case boole_procedure range name types inputs outputs decreases spec body =>
            intro block isBody
            have facts := procStep_facts (checkingInterpretation supports) range name.val
              decreases.val.isSome types.val inputs outputs.val spec.val body.val acc carriedState
              (by simpa [programStep] using stepped)
            rw [isBody] at facts
            obtain ⟨_, _, called⟩ := facts.2
            exact checked_proc onlyScalars carriedState.2 carriedState.1 called
          case command_procedure range _ name types inputs spec body =>
            intro block isBody
            have facts := procStep_facts (checkingInterpretation supports) range name.val false
              types.val inputs none spec.val body.val acc carriedState
              (by simpa [programStep] using stepped)
            rw [isBody] at facts
            obtain ⟨_, _, called⟩ := facts.2
            exact checked_proc onlyScalars carriedState.2 carriedState.1 called
          all_goals trivial

end Strata.Boole.Hoare
