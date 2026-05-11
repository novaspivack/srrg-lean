import Mathlib
import SrrgLean.Core.TheorySpace

/-!
# Core — Representation capacity R[S] (book §6.2)

`RepCapacityProfile` bundles a nonnegative real functional. Deriving concrete bounds
from `SelectorStrength` barrier theorems is tracked as EPIC_047 §9.1.
-/

namespace SrrgLean.Core

universe u

structure RepCapacityProfile (α : Type u) where
  R : α → ℝ
  R_nonneg : ∀ s, 0 ≤ R s

noncomputable def RepCapacity {α : Type u} (P : RepCapacityProfile α) (s : α) : ℝ :=
  P.R s

@[simp]
theorem RepCapacity.eq {α : Type u} (P : RepCapacityProfile α) (s : α) :
    RepCapacity P s = P.R s := rfl

theorem repCapacity_nonneg {α : Type u} (P : RepCapacityProfile α) (s : α) :
    0 ≤ RepCapacity P s := P.R_nonneg s

/-- Interface: `R` stays below a barrier constant (diagonal / strength certificate). -/
def RepCapacityBoundedBy {α : Type u} (P : RepCapacityProfile α) (B : ℝ) : Prop :=
  ∀ s, P.R s ≤ B

end SrrgLean.Core
