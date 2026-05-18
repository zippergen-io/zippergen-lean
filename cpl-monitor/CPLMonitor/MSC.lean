/-!
MSC executions for Causal Past Logic.

This file gives the semantic interface used by the first monitor proof.
The representation is intentionally abstract: the type `Event` is the
type of events of the MSC, so quantification over `Event` is
quantification over events in the execution.  An MSC supplies lifelines,
causal order, event valuations, and the two navigation operations used by
CPL, namely latest visible event and previous local event, together with
their specifications.
-/

namespace CPLMonitor

/-- An MSC with event valuations.

`latestVisible e A` is the latest event of lifeline `A` in the non-strict
causal past of `e`, if it exists.

`prevLocal e` is the strict previous event on the lifeline of `e`, if it
exists.  Local indices are injective on each lifeline; this represents
the paper's assumption that events on one lifeline are linearly ordered.
-/
structure MSC (L Event Var Val : Type) where
  lifeline : Event → L
  localIndex : Event → Nat
  localIndex_pos : ∀ e, 0 < localIndex e
  localIndex_inj :
    ∀ {e f}, lifeline e = lifeline f → localIndex e = localIndex f → e = f
  val : Event → Var → Val
  causal : Event → Event → Prop

  causal_refl : ∀ e, causal e e
  causal_trans : ∀ {e f g}, causal e f → causal f g → causal e g
  local_causal :
    ∀ {e f}, lifeline f = lifeline e → localIndex f ≤ localIndex e →
      causal f e

  latestVisible : Event → L → Option Event
  latestVisible_some :
    ∀ {e A f}, latestVisible e A = some f →
      lifeline f = A ∧
      causal f e ∧
      ∀ g, lifeline g = A → causal g e → localIndex g ≤ localIndex f
  latestVisible_none :
    ∀ {e A}, latestVisible e A = none →
      ∀ g, lifeline g = A → ¬ causal g e
  latestVisible_self :
    ∀ e, latestVisible e (lifeline e) = some e

  prevLocal : Event → Option Event
  prevLocal_some :
    ∀ {e f}, prevLocal e = some f →
      lifeline f = lifeline e ∧
      localIndex f < localIndex e ∧
      ∀ g, lifeline g = lifeline e → localIndex g < localIndex e →
        localIndex g ≤ localIndex f
  prevLocal_none :
    ∀ {e}, prevLocal e = none →
      ∀ g, lifeline g = lifeline e → ¬ localIndex g < localIndex e

namespace MSC

variable {L Event Var Val : Type} (M : MSC L Event Var Val)

/-- Events `f` and `e` lie on the same lifeline and `f` is not after `e`
in local index. -/
def LocalLe (f e : Event) : Prop :=
  M.lifeline f = M.lifeline e ∧ M.localIndex f ≤ M.localIndex e

/-- Strict local order, represented through local indices. -/
def LocalLt (f e : Event) : Prop :=
  M.lifeline f = M.lifeline e ∧ M.localIndex f < M.localIndex e

/-- The current event is the latest visible event of its own lifeline.
This is the non-strict convention used by `@A`. -/
theorem latestVisible_self_some (e : Event) :
    M.latestVisible e (M.lifeline e) = some e :=
  M.latestVisible_self e

/-- Latest visible events are unique. -/
theorem latestVisible_unique {e : Event} {A : L} {f g : Event}
    (hf : M.latestVisible e A = some f)
    (hg : M.latestVisible e A = some g) :
    f = g := by
  rcases M.latestVisible_some hf with ⟨hfLife, hfCausal, hfMax⟩
  rcases M.latestVisible_some hg with ⟨hgLife, hgCausal, hgMax⟩
  have hfg : M.localIndex f ≤ M.localIndex g :=
    hgMax f hfLife hfCausal
  have hgf : M.localIndex g ≤ M.localIndex f :=
    hfMax g hgLife hgCausal
  have hIdx : M.localIndex f = M.localIndex g :=
    Nat.le_antisymm hfg hgf
  have hLife : M.lifeline f = M.lifeline g := by
    rw [hfLife, hgLife]
  exact M.localIndex_inj hLife hIdx

/-- Characterization principle for latest-visible events. -/
theorem latestVisible_eq_some {e : Event} {A : L} {f : Event}
    (hLife : M.lifeline f = A)
    (hCausal : M.causal f e)
    (hMax :
      ∀ g, M.lifeline g = A → M.causal g e →
        M.localIndex g ≤ M.localIndex f) :
    M.latestVisible e A = some f := by
  cases hVis : M.latestVisible e A with
  | none =>
      have hNone := M.latestVisible_none hVis f hLife
      exact False.elim (hNone hCausal)
  | some g =>
      rcases M.latestVisible_some hVis with ⟨hLifeG, hCausalG, hMaxG⟩
      have hgf : M.localIndex g ≤ M.localIndex f :=
        hMax g hLifeG hCausalG
      have hfg : M.localIndex f ≤ M.localIndex g :=
        hMaxG f hLife hCausal
      have hIdx : M.localIndex g = M.localIndex f :=
        Nat.le_antisymm hgf hfg
      have hSameLife : M.lifeline g = M.lifeline f := by
        rw [hLifeG, hLife]
      have hEq : g = f := M.localIndex_inj hSameLife hIdx
      exact congrArg some hEq

/-- Characterization principle for absence of visible events. -/
theorem latestVisible_eq_none {e : Event} {A : L}
    (hNone : ∀ g, M.lifeline g = A → ¬ M.causal g e) :
    M.latestVisible e A = none := by
  cases hVis : M.latestVisible e A with
  | none => rfl
  | some g =>
      rcases M.latestVisible_some hVis with ⟨hLife, hCausal, _⟩
      exact False.elim ((hNone g hLife) hCausal)

/-- Previous local events are unique. -/
theorem prevLocal_unique {e f g : Event}
    (hf : M.prevLocal e = some f)
    (hg : M.prevLocal e = some g) :
    f = g := by
  rcases M.prevLocal_some hf with ⟨hfLife, hfIdx, hfMax⟩
  rcases M.prevLocal_some hg with ⟨hgLife, hgIdx, hgMax⟩
  have hfg : M.localIndex f ≤ M.localIndex g :=
    hgMax f hfLife hfIdx
  have hgf : M.localIndex g ≤ M.localIndex f :=
    hfMax g hgLife hgIdx
  have hIdx : M.localIndex f = M.localIndex g :=
    Nat.le_antisymm hfg hgf
  have hLife : M.lifeline f = M.lifeline g := by
    rw [hfLife, hgLife]
  exact M.localIndex_inj hLife hIdx

end MSC

end CPLMonitor
