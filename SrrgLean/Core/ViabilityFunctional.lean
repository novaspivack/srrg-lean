import Mathlib
import SrrgLean.Core.RepresentationCapacity
import SrrgLean.Core.ConstraintFunctional

/-!
# Core — Net viability F[S] = R[S] − C_Λ[S] (book §6.4)
-/

namespace SrrgLean.Core

variable {α : Type*}

noncomputable def Viability (P : RepCapacityProfile α) (C : ConstraintProfile α) (s : α) : ℝ :=
  RepCapacity P s - C.functional s

theorem viability_le_of_rep_bound (P : RepCapacityProfile α) (C : ConstraintProfile α) (BR : ℝ)
    (hR : ∀ s, P.R s ≤ BR) (s : α) :
    Viability P C s ≤ BR := by
  unfold Viability RepCapacity
  have hC : 0 ≤ C.functional s := ConstraintFunctional_nonneg C s
  linarith [hR s, hC]

theorem viability_pos_iff (P : RepCapacityProfile α) (C : ConstraintProfile α) (s : α) :
    0 < Viability P C s ↔ C.functional s < P.R s := by
  simp [Viability, RepCapacity, sub_pos]

end SrrgLean.Core
