import CPLMonitor.Basic

/-!
Syntax of Causal Past Logic.
-/

namespace CPLMonitor

/-- Terms are either local variables at the current formula position or
latest-visible fields from another lifeline. -/
inductive Term (L Var : Type) where
  | var : Var → Term L Var
  | atField : L → Var → Term L Var
deriving Repr

/-- Atomic predicates are application-level predicate symbols applied to
a finite list of terms.  Comparisons are represented by choosing suitable
predicate symbols and interpretations. -/
structure Atom (L Var Pred : Type) where
  pred : Pred
  args : List (Term L Var)
deriving Repr

/-- CPL formulas.  `prev` is local previous, `since` is local since, and
`at A phi` jumps to the latest causally visible event on lifeline `A`. -/
inductive Formula (L Var Pred : Type) where
  | truth : Formula L Var Pred
  | falsity : Formula L Var Pred
  | atom : Atom L Var Pred → Formula L Var Pred
  | not : Formula L Var Pred → Formula L Var Pred
  | and : Formula L Var Pred → Formula L Var Pred → Formula L Var Pred
  | or : Formula L Var Pred → Formula L Var Pred → Formula L Var Pred
  | prev : Formula L Var Pred → Formula L Var Pred
  | since : Formula L Var Pred → Formula L Var Pred → Formula L Var Pred
  | atL : L → Formula L Var Pred → Formula L Var Pred
deriving Repr

namespace Formula

/-- Derived strict past on the current lifeline. -/
def past {L Var Pred : Type} (φ : Formula L Var Pred) : Formula L Var Pred :=
  Formula.prev (Formula.since Formula.truth φ)

/-- Derived non-strict causal past on lifeline `A`. -/
def pastAt {L Var Pred : Type} (A : L) (φ : Formula L Var Pred) : Formula L Var Pred :=
  Formula.atL A (Formula.since Formula.truth φ)

end Formula

end CPLMonitor
