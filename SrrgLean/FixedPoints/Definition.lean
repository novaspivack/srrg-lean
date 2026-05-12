import SrrgLean.Core.ViabilityFunctional

/-!
# Fixed points — viability maximizer formulation (book §7.1)

This uses the “simplified” global-maximum definition. It is **not** the same
as a **flow** fixed point `F s ≃ s`; see `Existence.lean` for MFP-1 flow existence.
-/

namespace SrrgLean.FixedPoints

open SrrgLean.Core

variable {α : Type*} (P : RepCapacityProfile α) (C : ConstraintProfile α)

/-- Global maximizer of net viability F = R − C. -/
def IsSrrgFixedPoint (s : α) : Prop :=
  ∀ t : α, Viability P C t ≤ Viability P C s

/-- Lyapunov-style stability carrier (skeleton). -/
structure LyapunovCandidate (α : Type*) where
  L : α → ℝ
  L_nonneg : ∀ s, 0 ≤ L s
  vanishes_at : α → Prop

def IsStableFixedPoint (_V : α → ℝ) (s : α) : Prop :=
  (∃ L : LyapunovCandidate α, L.vanishes_at s ∧ (∀ t, s ≠ t → 0 < L.L t))

end SrrgLean.FixedPoints
