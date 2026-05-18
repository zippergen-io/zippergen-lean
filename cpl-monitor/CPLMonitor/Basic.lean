/-!
Basic shared definitions for the CPL monitor formalization.
-/

namespace CPLMonitor

/-- Binary comparisons used in the first formalization of atomic conditions. -/
inductive Cmp where
  | eq
  | ne
deriving DecidableEq, Repr

namespace Cmp

/-- Propositional semantics of comparisons. -/
def Sat {Val : Type} : Cmp → Val → Val → Prop
  | eq, x, y => x = y
  | ne, x, y => x ≠ y

end Cmp

end CPLMonitor

