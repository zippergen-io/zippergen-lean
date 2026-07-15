/- 
  MSCAgents/ConcretePayload.lean
  =================================
  Concrete inhabitance witnesses for the abstract control-payload interface.
-/

import MSCAgents.Correctness
import MSCAgents.DeadlockFreeness

namespace ConcretePayloadWitness

/-- A small payload domain with ordinary user payloads, syntactic control tags,
    and generated control messages carrying a Boolean decision plus a tag. -/
inductive ConcretePayload : Type where
  | user (n : Nat)
  | tag (n : Nat)
  | ctrl (decision : Bool) (tag : ConcretePayload)
  deriving DecidableEq, Repr

def ConcretePayload.isControl : ConcretePayload → Bool
  | .ctrl .. => true
  | _ => false

def concreteCtrlPatternFor {L C F : Type} :
    Prog L C F ConcretePayload → ConcretePayload
  | .ite .. => .tag 0
  | .whileLoop .. => .tag 1
  | .eps => .tag 2
  | .msg .. => .tag 3
  | .act .. => .tag 4
  | .seq .. => .tag 5

instance : PayloadCompatiblePred ConcretePayload where
  compat xs ys := xs = ys

/-- A concrete, inhabited control-payload specification. -/
instance : ControlPayloadSpec ConcretePayload where
  ctrlPattern := .tag 99
  ctrlPatternFor := fun {L} {C} {F} P => concreteCtrlPatternFor P
  setDecision b tag := .ctrl b tag
  isControl := ConcretePayload.isControl
  isControl_true := rfl
  isControl_false := rfl
  compat_ctrl_true := rfl
  compat_ctrl_false := rfl
  isControl_tagged := by
    intro decision tag
    rfl
  compat_tagged := by
    intro decision tag
    rfl
  compat_preserves_isControl := by
    intro xs ys h
    cases h
    rfl
  compat_decision_eq := by
    intro b1 b2 tag1 tag2 h
    cases h
    rfl
  setDecision_injective := by
    intro b1 b2 p h
    cases h
    rfl

#check (inferInstance : ControlPayloadSpec ConcretePayload)

inductive ConcreteLifeline : Type where
  | A
  | B
  deriving DecidableEq, Repr

instance : Fintype ConcreteLifeline where
  elems := [ConcreteLifeline.A, ConcreteLifeline.B]
  nodup := by
    simp
  complete := by
    intro x
    cases x <;> simp

open ConcreteLifeline

/-- A finite witness program with two syntactic control constructs whose tags
    are distinct in the concrete payload model. -/
def concreteProg : Prog ConcreteLifeline Bool Unit ConcretePayload :=
  Prog.ite true A Prog.eps Prog.eps ;;
  Prog.whileLoop false B Prog.eps Prog.eps

theorem concreteProg_wellTyped :
    WellTypedProgram concreteProg := by
  simp [concreteProg, WellTypedProgram]

theorem concreteProg_controlDistinguishable :
    ControlDistinguishableProgram concreteProg := by
  simp [concreteProg, ControlDistinguishableProgram]

#check concreteProg_controlDistinguishable

#check (realization_complete
  (L := ConcreteLifeline) (C := Bool) (F := Unit) (Payload := ConcretePayload)
  concreteProg concreteProg_wellTyped concreteProg_controlDistinguishable)

#check (realization_sound
  (L := ConcreteLifeline) (C := Bool) (F := Unit) (Payload := ConcretePayload)
  concreteProg concreteProg_wellTyped concreteProg_controlDistinguishable)

#check (projectDist_deadlockFree
  (L := ConcreteLifeline) (C := Bool) (F := Unit) (Payload := ConcretePayload)
  concreteProg concreteProg_wellTyped)

end ConcretePayloadWitness
