/- 
  MSCAgents/WellFormed.lean
  =========================
  Formalization of Definition `def:well-formed` from:
  "Provable Coordination for LLM Agents via Message Sequence Charts"

  Paper section: §2.2

  A global program is well formed if every message subterm
  `msg A(x⃗) → B(y⃗)` satisfies `match(x⃗, y⃗)`.
-/

import MSCAgents.Syntax
import MSCAgents.PayloadMatching

/-- Definition `def:well-formed`: every message node in the program tree uses
    compatible sender and receiver payloads. -/
def WellFormedProgram {L C F Payload : Type} [PayloadCompatiblePred Payload] :
    Prog L C F Payload → Prop
  | .eps => True
  | .msg _ xs _ ys _ => PayloadCompatible Payload xs ys
  | .act .. => True
  | .ite _ _ pTrue pFalse =>
      WellFormedProgram pTrue ∧ WellFormedProgram pFalse
  | .whileLoop _ _ pBody pExit =>
      WellFormedProgram pBody ∧ WellFormedProgram pExit
  | .seq p1 p2 =>
      WellFormedProgram p1 ∧ WellFormedProgram p2
