import CPLMonitor.MSC
import CPLMonitor.CPLSyntax

/-!
Denotational semantics of Causal Past Logic over MSCs.
-/

namespace CPLMonitor

open Formula

variable {L Event Var Val : Type}

/-- Value of a term at formula position `e`.  Latest-visible field terms
are undefined when the referenced lifeline has no visible event. -/
def Term.value (M : MSC L Event Var Val) (e : Event) :
    Term L Var → Option Val
  | Term.var x => some (M.val e x)
  | Term.atField A x =>
      match M.latestVisible e A with
      | none => none
      | some f => some (M.val f x)

/-- Evaluate a list of terms.  If any latest-visible field is undefined,
the whole argument list is undefined. -/
def Term.values (M : MSC L Event Var Val) (e : Event) :
    List (Term L Var) → Option (List Val)
  | [] => some []
  | t :: ts =>
      match Term.value M e t, Term.values M e ts with
      | some v, some vs => some (v :: vs)
      | _, _ => none

/-- Atomic semantics.  Undefined latest-visible terms make the whole atom
false, independently of the comparison operator. -/
def Atom.Sat {Pred : Type} (interp : Pred → List Val → Prop)
    (M : MSC L Event Var Val) (e : Event)
    (α : Atom L Var Pred) : Prop :=
  ∃ vs,
    Term.values M e α.args = some vs ∧
    interp α.pred vs

/-- Denotational CPL semantics. -/
def Sat {Pred : Type} (interp : Pred → List Val → Prop)
    (M : MSC L Event Var Val) :
    Formula L Var Pred → Event → Prop
  | Formula.truth, _ => True
  | Formula.falsity, _ => False
  | Formula.atom α, e => Atom.Sat interp M e α
  | Formula.not φ, e => ¬ Sat interp M φ e
  | Formula.and φ ψ, e => Sat interp M φ e ∧ Sat interp M ψ e
  | Formula.or φ ψ, e => Sat interp M φ e ∨ Sat interp M ψ e
  | Formula.prev φ, e =>
      match M.prevLocal e with
      | none => False
      | some f => Sat interp M φ f
  | Formula.since φ ψ, e =>
      ∃ f,
        M.LocalLe f e ∧
        Sat interp M ψ f ∧
        ∀ g,
          M.LocalLt f g →
          M.LocalLe g e →
          Sat interp M φ g
  | Formula.atL A φ, e =>
      match M.latestVisible e A with
      | none => False
      | some f => Sat interp M φ f

namespace Sat

/-- The `@A` operator is non-strict on the current lifeline. -/
theorem at_self_iff {Pred : Type} (interp : Pred → List Val → Prop)
    (M : MSC L Event Var Val)
    (φ : Formula L Var Pred) (e : Event) :
    Sat interp M (Formula.atL (M.lifeline e) φ) e ↔ Sat interp M φ e := by
  simp [Sat, M.latestVisible_self e]

/-- Local previous is false at events without a previous local event. -/
theorem prev_none_false {Pred : Type} (interp : Pred → List Val → Prop)
    (M : MSC L Event Var Val)
    (φ : Formula L Var Pred) {e : Event}
    (h : M.prevLocal e = none) :
    ¬ Sat interp M (Formula.prev φ) e := by
  simp [Sat, h]

/-- Standard recurrence for local past-time since. -/
theorem sat_since_rec {Pred : Type} (interp : Pred → List Val → Prop)
    (M : MSC L Event Var Val)
    (φ ψ : Formula L Var Pred) (e : Event) :
    Sat interp M (Formula.since φ ψ) e ↔
      Sat interp M ψ e ∨
        (Sat interp M φ e ∧
          match M.prevLocal e with
          | none => False
          | some f => Sat interp M (Formula.since φ ψ) f) := by
  constructor
  · intro h
    rcases h with ⟨f, hfe, hψf, hbetween⟩
    rcases hfe with ⟨hLifeFe, hIdxFe⟩
    by_cases hIdxEq : M.localIndex f = M.localIndex e
    · have hEq : f = e := M.localIndex_inj hLifeFe hIdxEq
      subst hEq
      exact Or.inl hψf
    · have hIdxLt : M.localIndex f < M.localIndex e :=
        Nat.lt_of_le_of_ne hIdxFe hIdxEq
      have hφe : Sat interp M φ e :=
        hbetween e ⟨hLifeFe, hIdxLt⟩ ⟨rfl, Nat.le_refl _⟩
      refine Or.inr ⟨hφe, ?_⟩
      cases hPrev : M.prevLocal e with
      | none =>
          exact False.elim ((M.prevLocal_none hPrev) f hLifeFe hIdxLt)
      | some p =>
          rcases M.prevLocal_some hPrev with ⟨hLifePe, hIdxPe, hMaxP⟩
          refine ⟨f, ?_, hψf, ?_⟩
          · refine ⟨?_, ?_⟩
            · rw [hLifeFe, hLifePe]
            · exact hMaxP f hLifeFe hIdxLt
          · intro g hfg hgp
            rcases hgp with ⟨hLifeGp, hIdxGp⟩
            have hLifeGe : M.lifeline g = M.lifeline e := by
              rw [hLifeGp, hLifePe]
            have hIdxGe : M.localIndex g ≤ M.localIndex e :=
              Nat.le_trans hIdxGp (Nat.le_of_lt hIdxPe)
            exact hbetween g hfg ⟨hLifeGe, hIdxGe⟩
  · intro h
    rcases h with hψe | ⟨hφe, hPrevPart⟩
    · refine ⟨e, ⟨rfl, Nat.le_refl _⟩, hψe, ?_⟩
      intro g heg hge
      rcases heg with ⟨_, hIdxEg⟩
      rcases hge with ⟨_, hIdxGe⟩
      exact False.elim ((Nat.not_lt_of_ge hIdxGe) hIdxEg)
    · cases hPrev : M.prevLocal e with
      | none =>
          simp [hPrev] at hPrevPart
      | some p =>
          simp [hPrev] at hPrevPart
          rcases M.prevLocal_some hPrev with ⟨hLifePe, hIdxPe, hMaxP⟩
          rcases hPrevPart with ⟨f, hfp, hψf, hbetweenP⟩
          rcases hfp with ⟨hLifeFp, hIdxFp⟩
          refine ⟨f, ?_, hψf, ?_⟩
          · refine ⟨?_, ?_⟩
            · rw [hLifeFp, hLifePe]
            · exact Nat.le_trans hIdxFp (Nat.le_of_lt hIdxPe)
          · intro g hfg hge
            rcases hge with ⟨hLifeGe, hIdxGe⟩
            by_cases hIdxEq : M.localIndex g = M.localIndex e
            · have hEq : g = e := M.localIndex_inj hLifeGe hIdxEq
              subst hEq
              exact hφe
            · have hIdxLt : M.localIndex g < M.localIndex e :=
                Nat.lt_of_le_of_ne hIdxGe hIdxEq
              have hIdxGp : M.localIndex g ≤ M.localIndex p :=
                hMaxP g hLifeGe hIdxLt
              have hLifeGp : M.lifeline g = M.lifeline p := by
                rw [hLifeGe, hLifePe]
              exact hbetweenP g hfg ⟨hLifeGp, hIdxGp⟩

end Sat

end CPLMonitor
