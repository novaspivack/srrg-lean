import SrrgLean.Core.ViabilityFunctional

/-!
# Core — SRRG flow (book §6.5, §7.1)

Discrete surrogate for the β-flow. A full variational gradient formulation (`δF/δS`)
is EPIC_047 §9.2.
-/

namespace SrrgLean.Core

variable {α : Type*}

/-- One step of discrete SRRG dynamics. -/
abbrev SrrgFlowStep (α : Type*) := α → α

/-- Weak formal ascent: each step does not decrease viability. -/
def IsMonotoneFlow (P : RepCapacityProfile α) (C : ConstraintProfile α) (F : SrrgFlowStep α) : Prop :=
  ∀ s, Viability P C s ≤ Viability P C (F s)

end SrrgLean.Core
