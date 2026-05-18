import CPLMonitor.MonitorState

/-!
Coherent pre-evaluation states and first correctness lemmas for the local
evaluator.
-/

namespace CPLMonitor

variable {L Event Var Val Pred : Type}

/-- The monitor state of owner lifeline `A` is coherent before evaluating
formulas at event `e`.

This is the Lean version of the paper's "Coherent pre-evaluation state".
The condition is intentionally local to the evaluator:

* the local store represents the current event valuation;
* latest-visible variable views represent the latest visible event on
  each lifeline;
* latest-value Boolean views are required for non-owner lifelines;
* `old` represents the previous local event, or false if no such event
  exists.

The current-owner Boolean views are not required here, because `@A(phi)`
is non-strict and Algorithm 2 evaluates it recursively at the current
event rather than reading a pre-existing view.
-/
structure CoherentPreEval [DecidableEq L]
    (interp : Pred → List Val → Prop)
    (M : MSC L Event Var Val) (A : L) (e : Event)
    (st : MonitorState L Var Val Pred) : Prop where
  owner_eq : M.lifeline e = A
  store_eq : ∀ x, st.store x = M.val e x
  clock_some :
    ∀ {B f}, M.latestVisible e B = some f →
      st.clock B = M.localIndex f
  clock_none :
    ∀ {B}, M.latestVisible e B = none →
      st.clock B = 0
  var_some :
    ∀ {B x f}, M.latestVisible e B = some f →
      st.varView B x = some (M.val f x)
  var_none :
    ∀ {B x}, M.latestVisible e B = none →
      st.varView B x = none
  view_some :
    ∀ {B φ f}, B ≠ A → M.latestVisible e B = some f →
      st.view B φ = some (Sat interp M φ f)
  view_none :
    ∀ {B φ}, B ≠ A → M.latestVisible e B = none →
      st.view B φ = none
  old_some :
    ∀ {φ f}, M.prevLocal e = some f →
      (st.old φ ↔ Sat interp M φ f)
  old_none :
    ∀ {φ}, M.prevLocal e = none →
      (st.old φ ↔ False)

namespace CoherentPreEval

variable [DecidableEq L]
variable (interp : Pred → List Val → Prop)
variable (M : MSC L Event Var Val) (A : L) (e : Event)
variable (st : MonitorState L Var Val Pred)

/-- Monitor term evaluation agrees with the MSC term semantics under a
coherent pre-evaluation state. -/
theorem term_value_correct
    (h : CoherentPreEval interp M A e st)
    (t : Term L Var) :
    MonitorState.termValue st t = Term.value M e t := by
  cases t with
  | var x =>
      simp [MonitorState.termValue, Term.value, h.store_eq x]
  | atField B x =>
      cases hVis : M.latestVisible e B with
      | none =>
          simp [MonitorState.termValue, Term.value, hVis,
            h.var_none (B := B) (x := x) hVis]
      | some f =>
          simp [MonitorState.termValue, Term.value, hVis,
            h.var_some (B := B) (x := x) (f := f) hVis]

/-- Monitor term-list evaluation agrees with the MSC term-list semantics
under a coherent pre-evaluation state. -/
theorem term_values_correct
    (h : CoherentPreEval interp M A e st)
    (ts : List (Term L Var)) :
    MonitorState.termValues st ts = Term.values M e ts := by
  induction ts with
  | nil =>
      simp [MonitorState.termValues, Term.values]
  | cons t ts ih =>
      rw [MonitorState.termValues, Term.values,
        term_value_correct (interp := interp) (M := M) (A := A) (e := e) (st := st) h t,
        ih]
      rfl

/-- Monitor atom evaluation agrees with the MSC atom semantics under a
coherent pre-evaluation state. -/
theorem atom_eval_correct
    (h : CoherentPreEval interp M A e st)
    (α : Atom L Var Pred) :
    MonitorState.atomEval interp st α ↔ Atom.Sat interp M e α := by
  unfold MonitorState.atomEval Atom.Sat
  rw [term_values_correct (interp := interp) (M := M) (A := A) (e := e) (st := st) h α.args]

/-- Local monitor evaluation agrees with the denotational CPL semantics
under a coherent pre-evaluation state. -/
theorem local_eval_correct
    (h : CoherentPreEval interp M A e st)
    (φ : Formula L Var Pred) :
    MonitorState.Eval A interp st φ ↔ Sat interp M φ e := by
  induction φ with
  | truth =>
      simp [MonitorState.Eval, Sat]
  | falsity =>
      simp [MonitorState.Eval, Sat]
  | atom α =>
      exact atom_eval_correct
        (interp := interp) (M := M) (A := A) (e := e) (st := st) h α
  | not φ ih =>
      simp [MonitorState.Eval, Sat, ih]
  | and φ ψ ihφ ihψ =>
      simp [MonitorState.Eval, Sat, ihφ, ihψ]
  | or φ ψ ihφ ihψ =>
      simp [MonitorState.Eval, Sat, ihφ, ihψ]
  | prev φ _ =>
      cases hPrev : M.prevLocal e with
      | none =>
          have hold := h.old_none (φ := φ) hPrev
          simp [MonitorState.Eval, Sat, hPrev, hold]
      | some f =>
          have hold := h.old_some (φ := φ) hPrev
          simp [MonitorState.Eval, Sat, hPrev, hold]
  | since φ ψ ihφ ihψ =>
      rw [Sat.sat_since_rec (interp := interp) (M := M) φ ψ e]
      cases hPrev : M.prevLocal e with
      | none =>
          have hold := h.old_none (φ := Formula.since φ ψ) hPrev
          simp [MonitorState.Eval, ihφ, ihψ, hold]
      | some f =>
          have hold := h.old_some (φ := Formula.since φ ψ) hPrev
          simp [MonitorState.Eval, ihφ, ihψ, hold]
  | atL B φ ih =>
      by_cases hBA : B = A
      · subst hBA
        have hVis : M.latestVisible e B = some e := by
          rw [← h.owner_eq]
          exact M.latestVisible_self e
        simp [MonitorState.Eval, Sat, hVis, ih]
      · cases hVis : M.latestVisible e B with
        | none =>
            have hview := h.view_none (B := B) (φ := φ) hBA hVis
            simp [MonitorState.Eval, Sat, hBA, hVis, hview]
        | some f =>
            have hview := h.view_some (B := B) (φ := φ) (f := f) hBA hVis
            simp [MonitorState.Eval, Sat, hBA, hVis, hview]

end CoherentPreEval

end CPLMonitor
