import SrrgLean.FixedPoints.Definition

/-!
# Fixed points — uniqueness (book §7.2)

Strict concavity / Hessian hypotheses on `F[S]` are an open formalization target.
-/

namespace SrrgLean.FixedPoints

open SrrgLean.Core

variable {α : Type*} (P : RepCapacityProfile α) (C : ConstraintProfile α)

/--
Uniqueness of global viability maximizer under a strict-uniqueness hypothesis.

`hUniqMax` says: if two points both achieve the global maximum of `Viability P C`,
they are equal. This encodes the strict-concavity / strict-quasiconcavity condition
on F[S] near the fixed point (book §7.2; a concrete Hessian proof is a future goal).
-/
theorem uniqueness_of_strict_concavity
    (hUniqMax : ∀ s₁ s₂ : α,
        (∀ t, Viability P C t ≤ Viability P C s₁) →
        (∀ t, Viability P C t ≤ Viability P C s₂) →
        s₁ = s₂)
    {s₁ s₂ : α}
    (h₁ : IsSrrgFixedPoint P C s₁)
    (h₂ : IsSrrgFixedPoint P C s₂) :
    s₁ = s₂ :=
  hUniqMax s₁ s₂ h₁ h₂

end SrrgLean.FixedPoints
