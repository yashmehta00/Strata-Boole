/-
Copyright Strata Contributors
SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataBoole.Tagless.Hoare.Certificate
import StrataBoole.Tagless.Hoare.Guarantees.CoreState

/-! # Soundness with respect to original Core execution

`verified_implies_core_correct` is the overall guarantee. Every other theorem
in this file is a typing, transformer, expression, statement, framing, or
contract fact used to support the source connection. Supporting facts precede
the overall theorem so its proof can use them in Lean declaration order. Proofs under construction
use `sorry`.

The guarantee covers assertions on all finite execution prefixes and ordinary
ensures on normal completion. It does not assert progress, termination, exact
weakestness, or correctness of the source-text frontend. Input admission is a
separate guarantee in `EntryAdmission.lean`.
-/

namespace Strata.Tagless.Hoare

/-- If expression embedding succeeds with type `ty`, Core's annotated type
checker accepts the original expression at the corresponding Core type. -/
theorem embedExpr_typed {context : List Binding} {e : Core.Expression.Expr}
    {ty : Ty} {recipe : ExprRecipe ty}
    (h : embedExpr context e = .ok ⟨ty, recipe⟩) :
    Lambda.LExpr.typeCheck [] e = some ty.core := by
  unfold embedExpr at h
  cases hr : embedExprRaw context e with
  | error message => simp [hr, bind, Except.bind] at h
  | ok result =>
    simp only [hr, bind, Except.bind] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      cases h
      assumption
    · simp [throw] at h

/-- A successfully embedded expression has the inferred type according to
Core's declarative typing rules. -/
theorem embedExpr_hasType {context : List Binding} {e : Core.Expression.Expr}
    {ty : Ty} {recipe : ExprRecipe ty}
    (h : embedExpr context e = .ok ⟨ty, recipe⟩) :
    Lambda.LExpr.HasTypeA [] e ty.core :=
  Lambda.LExpr.typeCheck_to_HasTypeA (embedExpr_typed h)

/-- A successfully embedded Boolean expression has Core's Boolean type.
This applies to guards, assertions, invariants, and specification clauses. -/
theorem embedBool_hasType {context : List Binding} {e : Core.Expression.Expr}
    {recipe : ExprRecipe .bool} (h : embedBool context e = .ok recipe) :
    Lambda.LExpr.HasTypeA [] e (.tcons "bool" []) := by
  unfold embedBool at h
  cases hr : embedExpr context e with
  | error message => simp [hr, bind, Except.bind] at h
  | ok result =>
    obtain ⟨ty, expression⟩ := result
    simp only [hr, bind, Except.bind, expect] at h
    split at h
    · next hty =>
        cases hty
        exact embedExpr_hasType hr
    · simp at h

/-- If procedure embedding succeeds, the source procedure has a structured
statement body rather than a control-flow-graph body. -/
theorem embedCore_structured {p : Core.Procedure} {recipes}
    (h : embedCore p = .ok recipes) : ∃ body, p.body = .structured body := by
  cases hb : p.body with
  | structured body => exact ⟨body, rfl⟩
  | cfg graph =>
    cases hh : embedHeader p.header with
    | error message => simp [embedCore, hh, liftCheck, bind, Except.bind, Except.map] at h
    | ok header =>
      cases hp : embedRequires header.before p.spec.preconditions with
      | error message => simp [embedCore, hh, hp, liftCheck, bind, Except.bind, Except.map] at h
      | ok pre =>
        simp [embedCore, hh, hp, embedProcWithHeader, hb, liftCheck,
          bind, Except.bind, Except.map] at h

/-- A `Verified` certificate contains successful procedure embedding and a
proof that the interpreted requires predicate implies the program transformer's
condition for establishing the interpreted ensures predicate, for every native
initial state. -/
theorem verified_formula {p : Core.Procedure} (h : Verified p) :
    ∃ recipes, embedCore p = .ok recipes ∧
      let (P, command, Q) := interpret recipes
      ∀ σ, P σ → command.transform Q σ := by
  obtain ⟨recipes, hembed, htriple⟩ := h
  exact ⟨recipes, hembed, triple_iff.mp htriple⟩

/-- If the transformer for `assert e` establishes postcondition `Q` from a
state, `e` is defined and true in that state, and `Q` holds there. The assertion
does not change the state. -/
theorem assert_requires_check (info : ClauseInfo) (e : Expr .bool)
    (Q : State → Prop) (σ : State)
    (h : (Transformer.assert info e).transform Q σ) : e.Holds σ ∧ Q σ := h

/-- If the transformer for `assume e` establishes `Q` from a state, `Q`
holds whenever the assumption is not false. An undefined assumption is ignored,
so it supplies no additional information about the state. -/
theorem assume_requires_continuation (info : ClauseInfo) (e : Expr .bool)
    (Q : State → Prop) (σ : State)
    (h : (Transformer.assume info e).transform Q σ) : e.MayHold σ → Q σ := h

/-- No state satisfies the requirements for a false assertion followed by
a false assumption, regardless of the requested postcondition. An assumption
that occurs later cannot justify an earlier assertion. -/
theorem false_assert_before_assume (assertInfo assumeInfo : ClauseInfo)
    (Q : State → Prop) (σ : State) :
    ¬ (Transformer.seq (Transformer.assert assertInfo (Expr.total fun _ => false))
        (Transformer.assume assumeInfo (Expr.total fun _ => false))).transform Q σ := by
  simp [Transformer.seq, Transformer.assert, Obligation, Expr.Holds, Expr.total]

/-- No state satisfies the requirements for a false assertion followed by
any command, regardless of the requested postcondition. -/
theorem false_assert_before_anything (info : ClauseInfo) (rest : Transformer)
    (Q : State → Prop) (σ : State) :
    ¬ (Transformer.seq (Transformer.assert info (Expr.total fun _ => false)) rest).transform Q σ := by
  simp [Transformer.seq, Transformer.assert, Obligation, Expr.Holds, Expr.total]

/-- Replacing the variables in a loop's write set with arbitrary values
preserves both native value slots of every variable outside that set. -/
theorem loop_frame (entry arbitrary : State) (writes : List String) (x : String)
    (hx : x ∉ writes) :
    (entry.havoc writes arbitrary).ints x = entry.ints x ∧
    (entry.havoc writes arbitrary).bools x = entry.bools x := by
  simp [State.havoc, hx]

/-- If a candidate state agrees with the entry state outside the write set,
replacing just the written variables with the candidate's values produces
exactly the candidate state. -/
theorem havoc_of_agrees (entry candidate : State) (writes : List String)
    (h : ∀ x, x ∉ writes → candidate.ints x = entry.ints x ∧
      candidate.bools x = entry.bools x) :
    entry.havoc writes candidate = candidate := by
  apply State.ext <;> funext x <;> by_cases hx : x ∈ writes
  · simp [State.havoc, hx]
  · simp [State.havoc, hx, (h x hx).1]
  · simp [State.havoc, hx]
  · simp [State.havoc, hx, (h x hx).2]

/-- The loop transformer's requirement is exactly: its invariants and
optional measure bound hold on entry; at every framed loop head satisfying
those checks, the guard is defined; an iteration re-establishes the checks and
decreases the optional measure; and an exit establishes the postcondition. -/
theorem loop_obligations (writes : List String) (guard : Expr .bool)
    (invariants : List (ClauseInfo × Expr .bool)) (measure : Option (Expr .int))
    (body : Transformer) (Q : State → Prop) (entry : State) :
    (Transformer.loop writes guard invariants measure body).transform Q entry ↔
      Transformer.loopHead invariants measure entry ∧
      ∀ arbitrary,
        let before := entry.havoc writes arbitrary
        Transformer.loopHead invariants measure before →
        guard.defined before ∧
        (guard before = true → body.transform (fun after =>
          Transformer.loopHead invariants measure after ∧
          Transformer.measureDrops measure before after) before) ∧
        (guard before = false → Q before) := Iff.rfl

/-- A command preserves variables outside `writes` if every postcondition it
establishes can be strengthened with equality of the unwritten entry and final
value slots. -/
def Frames (writes : List String) (body : Transformer) : Prop :=
  ∀ (Q : State → Prop) before, body.transform Q before →
    body.transform (fun after => Q after ∧
      ∀ x, x ∉ writes → after.ints x = before.ints x ∧
        after.bools x = before.bools x) before

/-- Suppose the body preserves variables outside the loop's write set and
the loop's generated requirements hold. Its guard is then defined. If the guard
is true, the body establishes those same loop requirements for the next
iteration; otherwise the requested postcondition already holds. -/
theorem loop_unroll (writes : List String) (guard : Expr .bool)
    (invariants : List (ClauseInfo × Expr .bool)) (measure : Option (Expr .int))
    (body : Transformer) (framing : Frames writes body) (Q : State → Prop) (entry : State)
    (h : (Transformer.loop writes guard invariants measure body).transform Q entry) :
    guard.defined entry ∧
      (if guard entry then
        body.transform ((Transformer.loop writes guard invariants measure body).transform Q) entry
       else Q entry) := by
  have self : entry.havoc writes entry = entry := by
    apply State.ext <;> funext x <;> simp [State.havoc]
  have head := h.2 entry (by simpa only [self] using h.1)
  rw [self] at head
  refine ⟨head.1, ?_⟩
  by_cases hg : guard entry = true
  · simp only [hg, ite_true]
    have step := framing _ entry (head.2.1 hg)
    apply body.monotone _ _ _ entry step
    intro after ha
    refine ⟨ha.1.1, fun arbitrary hi => ?_⟩
    have same : after.havoc writes arbitrary = entry.havoc writes arbitrary := by
      apply State.ext <;> funext x <;> by_cases hx : x ∈ writes
      · simp [State.havoc, hx]
      · simp [State.havoc, hx, (ha.2 x hx).1]
      · simp [State.havoc, hx]
      · simp [State.havoc, hx, (ha.2 x hx).2]
    rw [same] at hi ⊢
    exact h.2 arbitrary hi
  · have hf : guard entry = false := Bool.eq_false_iff.mpr hg
    simpa [hf] using head.2.2 hf

/-- For a successfully embedded expression, a Core store and a native state
that agree on the variables in scope give the same value whenever the native
expression is defined. The Core expression is read after substituting its store,
and the equality holds in every consistent Core model and semantic valuation. -/
theorem embedded_expression_denotes_core_value
    (context : List Binding) (e : Core.Expression.Expr) (ty : Ty)
    (recipe : ExprRecipe ty) (hembed : embedExpr context e = .ok ⟨ty, recipe⟩)
    (model : Lambda.Interp Core.Factory) (world : Core.Logic.DenoteValuation model)
    (store : Core.CoreStore) (state : State)
    (hstore : StoreDenotes model world context store state)
    (hdefined : (recipe interpretation).defined state) :
    let captured := Core.Logic.capturedExpr
      { factory := Core.Factory, store := store, expr := e, label := "", metadata := #[] }
    ∃ h : Lambda.LExpr.HasTypeA [] captured ty.core,
      denoteNative model world ty captured h = (recipe interpretation).value state := by
  sorry

/-- Suppose statement embedding succeeds and, in every Core model and
semantic valuation, the initial Core store has a matching native state satisfying
the interpreted requirement for `Q`. Every finite Core execution prefix then
has valid assertions under their preceding assumptions. On normal completion,
each valuation satisfying the run's assumptions has a matching final native
state satisfying `Q`. -/
theorem interpreted_statements_preserve_core_assertions_and_postcondition
    (context : List Binding) (statements : List Core.Statement)
    (recipe : CmdRecipe) (after : List Binding)
    (hembed : embedStmts context statements = .ok (recipe, after))
    (lookup : String → Option Core.Procedure) (initial : Imperative.Env Core.Expression)
    (Q : State → Prop)
    (hfactory : initial.factory = Core.Factory)
    (hwf : Core.Logic.BlockInitEnvWF entryParams statements initial)
    (hrequirement : ∀ (model : Lambda.Interp Core.Factory)
        (world : Core.Logic.DenoteValuation model),
      ∃ state, StoreDenotes model world context initial.store state ∧
        (recipe interpretation).transform Q state)
    (trace : Imperative.Trace Core.Expression) (cfg : Core.CoreConfig)
    (hexec : Core.CoreStepStarE lookup (.stmts statements initial) trace cfg) :
    (∀ model : Lambda.Interp Core.Factory,
      Imperative.Trace.AssertionsValid Core.Expression
        (Core.Logic.DenoteBasedInterp model) trace) ∧
    (∀ final, cfg = .terminal final →
      ∀ (model : Lambda.Interp Core.Factory) (world : Core.Logic.DenoteValuation model),
        Imperative.Trace.AssumptionsHold Core.Expression
          (Core.Logic.DenoteBasedInterp model) world trace →
        ∃ state, StoreDenotes model world after final.store state ∧ Q state) := by
  sorry

/-- Every normally completed Core execution of a successfully embedded
block preserves the initial store binding of each variable outside the block's
computed write set. -/
theorem core_block_preserves_unwritten_variables
    (context : List Binding) (statements : List Core.Statement) (recipe : CmdRecipe)
    (hembed : embedBlock context statements = .ok recipe)
    (lookup : String → Option Core.Procedure)
    (initial : Imperative.Env Core.Expression) (trace : Imperative.Trace Core.Expression)
    (final : Imperative.Env Core.Expression)
    (hexec : Core.CoreStepStarE lookup
      (.stmt (Imperative.Stmt.block "" statements #[]) initial) trace (.terminal final))
    (x : Core.CoreIdent)
    (hunwritten : x.name ∉
      (Imperative.Block.modifiedOrDefinedVars statements false).map (·.name)) :
    final.store x = initial.store x := by
  sorry

/-- Suppose output initialization establishes `Q` from a native state whose
inputs agree with a permitted Core procedure-entry environment. There is then a
native body-entry state that also agrees on outputs and old-value snapshots
and satisfies `Q`. Thus initialization covers every permitted initial output
value, rather than fixing a particular output value. -/
theorem output_initialization_covers_core_entry_states
    (p : Core.Procedure) (header : HeaderContext)
    (hheader : embedHeader p.header = .ok header)
    (Q : State → Prop) (before : State)
    (hsetup : (outputInitialization header interpretation).transform Q before)
    (initial : Imperative.Env Core.Expression)
    (hfactory : initial.factory = Core.Factory)
    (hentry : Core.Specification.ProcEnvWF entryParams p initial)
    (model : Lambda.Interp Core.Factory) (world : Core.Logic.DenoteValuation model)
    (hinputs : StoreDenotes model world header.before initial.store before) :
    ∃ bodyEntry, StoreDenotes model world header.inside initial.store bodyEntry ∧ Q bodyEntry := by
  sorry

/-- If a permitted Core procedure-entry environment and a native state
agree on the input variables, the native state satisfies the interpreted
requires predicate. The result holds in every consistent Core model and
semantic valuation. -/
theorem core_requires_imply_interpreted_precondition
    (p : Core.Procedure) (header : HeaderContext) (recipe : PredRecipe)
    (hheader : embedHeader p.header = .ok header)
    (hembed : embedRequires header.before p.spec.preconditions = .ok recipe)
    (initial : Imperative.Env Core.Expression)
    (hfactory : initial.factory = Core.Factory)
    (hentry : Core.Specification.ProcEnvWF entryParams p initial)
    (model : Lambda.Interp Core.Factory) (world : Core.Logic.DenoteValuation model)
    (inputs : State)
    (hinputs : StoreDenotes model world header.before initial.store inputs) :
    recipe interpretation inputs := by
  sorry

/-- If a final Core store agrees with a native state satisfying the
interpreted ensures predicate, each ordinary ensures clause holds when read in
that Core environment and semantic valuation. Free ensures clauses are excluded
from the guarantees established by body verification. -/
theorem interpreted_postcondition_implies_core_ensures
    (context : List Binding) (clauses : List (String × Core.Procedure.Check))
    (recipe : PredRecipe) (hembed : embedEnsures context clauses = .ok recipe)
    (model : Lambda.Interp Core.Factory) (world : Core.Logic.DenoteValuation model)
    (final : Imperative.Env Core.Expression) (state : State)
    (hfactory : final.factory = Core.Factory)
    (hstore : StoreDenotes model world context final.store state)
    (hpostcondition : recipe interpretation state)
    (label : String) (check : Core.Procedure.Check)
    (hclause : (label, check) ∈ clauses) (hordinary : check.attr = .Default) :
    (Core.Logic.DenoteBasedInterp model).holds world
      { factory := final.factory, store := final.store, expr := check.expr,
        label := label, metadata := check.md } := by
  sorry

/-- Soundness of tagless Hoare verification with respect to Core execution.
If a procedure has a `Verified` certificate, every finite execution prefix from
an admissible Core entry environment satisfies the assertions encountered so
far, under their preceding assumptions. On normal completion, its ordinary
(non-free) ensures clauses hold under the run's assumptions as well.

The guarantee holds in every consistent model of `Core.Factory`, covers prefixes
of nonterminating runs, and does not require the procedure to terminate. -/
theorem verified_implies_core_correct
    (program : Core.Program) (name : String) (p : Core.Procedure)
    (hlookup : program.findProcByString? name = some p)
    (hverified : Verified p) :
    ∃ body, p.body = .structured body ∧
      ∀ (model : Lambda.Interp Core.Factory) (initial : Imperative.Env Core.Expression),
        initial.factory = Core.Factory →
        Core.Specification.ProcEnvWF entryParams p initial →
        ∀ (trace : Imperative.Trace Core.Expression) (cfg : Core.CoreConfig),
          Core.CoreStepStarE program.findProcByString?
            (.stmt (Imperative.Stmt.block "" body #[]) initial) trace cfg →
          Imperative.Trace.AssertionsValid Core.Expression
            (Core.Logic.DenoteBasedInterp model) trace ∧
          (∀ final, cfg = .terminal final →
            Imperative.Trace.AssertionsValid Core.Expression
              (Core.Logic.DenoteBasedInterp model)
              (trace ++ Core.defaultAssertEvents final.factory final.store p.spec.postconditions)) := by
  sorry

end Strata.Tagless.Hoare
