/-
  MSCAgents/ExampleModel.lean
  ===========================
  A concrete model witnessing that the abstract interfaces used by the
  correctness development are *inhabited*, and that the main results are
  *non-vacuous*.

  The correctness theorem (`thm:correctness`) and the deadlock-freedom
  corollary (`cor:deadlock-free`) are stated for an abstract payload type
  `Payload` equipped with `[ControlPayloadSpec Payload]`. This module exhibits
  a concrete payload type satisfying that interface, together with a concrete
  well-typed program, and instantiates the main theorems at it. If the
  `ControlPayloadSpec` laws were contradictory, or the theorems vacuous, this
  file would fail to compile.

  Paper: "Provable Coordination for LLM Agents via Message Sequence Charts"
-/

import MSCAgents.DeadlockFreeness
import MSCAgents.Correctness

namespace MSCAgents.ExampleModel

/-- A concrete two-element finite lifeline set. -/
inductive LL | p | q
  deriving DecidableEq

instance : Fintype LL where
  elems := [LL.p, LL.q]
  nodup := by decide
  complete := by intro x; cases x <;> decide

/-- A concrete payload type with a genuine control/user split:
    `user` payloads model source-level data; `ctrl` payloads model the
    projection-generated control tags. -/
inductive Pay | user (n : Nat) | ctrl (b : Bool)
  deriving DecidableEq

/-- Payload compatibility: control payloads agree on their decision bit,
    user payloads agree on their value, and the two sorts never mix. -/
def Pay.compat : Pay → Pay → Prop
  | .ctrl b1, .ctrl b2 => b1 = b2
  | .user m, .user n => m = n
  | _, _ => False

/-- Recognizer for control payloads (the dedicated control-tag sort). -/
def Pay.isCtrl : Pay → Bool
  | .ctrl _ => true
  | .user _ => false

instance : PayloadCompatiblePred Pay where
  compat := Pay.compat

instance : ControlPayload Pay where
  ctrlPattern := .ctrl false
  setDecision b _ := .ctrl b

/-- The `ControlPayloadSpec` laws are satisfiable: this instance discharges all
    of them for `Pay`, so the abstract interface is not contradictory. -/
instance : ControlPayloadSpec Pay where
  isControl := Pay.isCtrl
  isControl_true := rfl
  isControl_false := rfl
  compat_ctrl_true := rfl
  compat_ctrl_false := rfl
  compat_preserves_isControl := by
    intro xs ys h
    cases xs <;> cases ys <;>
      simp_all [PayloadCompatible, PayloadCompatiblePred.compat, Pay.compat, Pay.isCtrl]
  compat_decision_eq := by
    intro b1 b2 h
    simpa [PayloadCompatible, PayloadCompatiblePred.compat, Pay.compat,
      ControlPayload.setDecision, ControlPayload.ctrlPattern] using h
  setDecision_injective := by
    intro b1 b2 p h
    simpa [ControlPayload.setDecision] using h

/-- A concrete well-typed, control-distinguishable program:
    `p` sends a user payload to `q`. -/
def P0 : Prog LL Bool String Pay :=
  Prog.msg LL.p (Pay.user 5) LL.q (Pay.user 5) (by decide)

theorem P0_wellTyped : WellTypedProgram P0 := by
  simp [WellTypedProgram, P0, PayloadCompatible, PayloadCompatiblePred.compat, Pay.compat]

theorem P0_ctrlDistinguishable : ControlDistinguishableProgram P0 := by
  simp [ControlDistinguishableProgram, P0, isControlPayload,
    ControlPayloadSpec.isControl, Pay.isCtrl]

/-- The MSC semantics of `P0` is inhabited (so the existential in the
    completeness direction below is over a non-empty domain). -/
theorem P0_semantics_nonempty : ∃ M, ⟦P0⟧ M :=
  mscSemantics_nonempty P0 P0_wellTyped

/-- Non-vacuity of `thm:correctness` (item 1, completeness of realization),
    instantiated at the concrete model. -/
theorem correctness_complete_concrete :
    ∀ M, ⟦P0⟧ M →
      ∃ Mhat, distSemantics (projectDist P0) Mhat ∧ eraseTuple Mhat = M :=
  realization_complete P0 P0_wellTyped P0_ctrlDistinguishable

/-- Non-vacuity of `thm:correctness` (item 2, soundness of realization). -/
theorem correctness_sound_concrete :
    ∀ Mhat, distSemantics (projectDist P0) Mhat → ⟦P0⟧ (eraseTuple Mhat) :=
  realization_sound P0 P0_wellTyped P0_ctrlDistinguishable

/-- Non-vacuity of `cor:deadlock-free` at the concrete model. -/
theorem deadlockFree_concrete : DeadlockFree (projectDist P0) :=
  projectDist_deadlockFree P0 P0_wellTyped

end MSCAgents.ExampleModel
