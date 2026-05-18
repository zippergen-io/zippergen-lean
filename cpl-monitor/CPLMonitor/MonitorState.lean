import CPLMonitor.CPLSemantics

/-!
Monitor state and the local evaluator used by Algorithm 2.

This first version is Prop-valued: Boolean monitor entries are represented
as propositions.  A later executable refinement can replace these by
booleans under decidability assumptions for application predicates.
-/

namespace CPLMonitor

variable {L Event Var Val Pred : Type}

/-- State maintained by one lifeline monitor for the finite set of
formulas under consideration.

`clock` is included because the paper monitor stores vector clocks.  The
local-evaluation proof below uses the semantic views directly; the clock
will become important in the event-update invariant proof.
-/
structure MonitorState (L Var Val Pred : Type) where
  clock : L → Nat
  store : Var → Val
  old : Formula L Var Pred → Prop
  view : L → Formula L Var Pred → Option Prop
  varView : L → Var → Option Val

namespace MonitorState

/-- Value of a term according to the monitor state. -/
def termValue (st : MonitorState L Var Val Pred) :
    Term L Var → Option Val
  | Term.var x => some (st.store x)
  | Term.atField A x => st.varView A x

/-- Values of a term list according to the monitor state. -/
def termValues (st : MonitorState L Var Val Pred) :
    List (Term L Var) → Option (List Val)
  | [] => some []
  | t :: ts =>
      match termValue st t, termValues st ts with
      | some v, some vs => some (v :: vs)
      | _, _ => none

/-- Monitor-side evaluation of an atom.  Undefined field terms make the
whole atom false because `termValues` returns `none`. -/
def atomEval (interp : Pred → List Val → Prop)
    (st : MonitorState L Var Val Pred) (α : Atom L Var Pred) : Prop :=
  ∃ vs, termValues st α.args = some vs ∧ interp α.pred vs

/-- Local monitor evaluator.  This follows Algorithm 2 at the level of
propositions:

* unqualified variables read the current local store;
* latest-visible field terms read `varView`;
* `Y` reads the saved previous-local value `old`;
* `S` uses the standard past-time recurrence;
* `@A` is non-strict, so at the owner lifeline it evaluates recursively
  at the current event; otherwise it reads the latest-value view.
-/
def Eval [DecidableEq L] (owner : L)
    (interp : Pred → List Val → Prop)
    (st : MonitorState L Var Val Pred) :
    Formula L Var Pred → Prop
  | Formula.truth => True
  | Formula.falsity => False
  | Formula.atom α => atomEval interp st α
  | Formula.not φ => ¬ Eval owner interp st φ
  | Formula.and φ ψ => Eval owner interp st φ ∧ Eval owner interp st ψ
  | Formula.or φ ψ => Eval owner interp st φ ∨ Eval owner interp st ψ
  | Formula.prev φ => st.old φ
  | Formula.since φ ψ =>
      Eval owner interp st ψ ∨
      (Eval owner interp st φ ∧ st.old (Formula.since φ ψ))
  | Formula.atL A φ =>
      if A = owner then
        Eval owner interp st φ
      else
        match st.view A φ with
        | none => False
        | some p => p

end MonitorState

end CPLMonitor
