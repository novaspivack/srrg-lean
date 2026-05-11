import Mathlib
import SrrgLean.Core.RepresentationCapacity
import SrrgLean.Core.ConstraintFunctional

/-!
# Core — Net viability F[S] = R[S] − C_Λ[S] (book §6.4)

## Correspondence with viable-continuation-lean (SPEC_052_PRI §B1)

`Viability P C s > 0` corresponds to `HasViability.Viable s` in viable-continuation-lean:
- In viable-continuation-lean, `HasViability.Viable s` asserts that system state `s`
  satisfies a viability predicate (the system can continue to exist under its constraints).
- In srrg-lean, `Viability P C s > 0` means net representational capacity exceeds
  constraint cost, i.e. `R[s] > C_Λ[s]` — the system has positive information-profit margin.
- Both capture the same structural idea: a viable system is one whose resources exceed its
  self-maintenance obligations. The SRRG formulation is quantitative (real-valued surplus);
  viable-continuation-lean gives the propositional cut.
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
