import SrrgLean.FixedPoints.Definition

/-!
# Fixed points — uniqueness (book §7.2)

Strict concavity / Hessian hypotheses on `F[S]` are EPIC_047 §9.3.
-/

namespace SrrgLean.FixedPoints

open SrrgLean.Core

variable {α : Type*} (P : RepCapacityProfile α) (C : ConstraintProfile α)

/--
Uniqueness under a strict-concavity witness — EPIC_047 §9.3.

**TODO(EPIC_047 §9.3):** replace `sorry` with a Hessian / strong-convexity hypothesis.
-/
theorem uniqueness_of_strict_concavity
    {s₁ s₂ : α}
    (h₁ : IsSrrgFixedPoint P C s₁)
    (h₂ : IsSrrgFixedPoint P C s₂) :
    s₁ = s₂ := by
  sorry

end SrrgLean.FixedPoints
