import SrrgLean.Core.FlowEquation

/-!
# Bridges — SRRG flow ⇒ NEMS confirmation lemmas (Phase 4, SPEC_047 §4.4 / P4.T4)

`RecordEntropy.Theorems.Monotonicity` and cosmological closure layers in nems-lean should
follow from `IsMonotoneFlow` hypotheses once the morphisms are fully specified.

**TODO(EPIC_047):** discharge this from `IsMonotoneFlow` + explicit pushforwards.
-/

namespace SrrgLean.Bridges

variable {α : Type*} {P : SrrgLean.Core.RepCapacityProfile α}
  {C : SrrgLean.Core.ConstraintProfile α} {F : SrrgLean.Core.SrrgFlowStep α}

/--
NEMS record-entropy monotonicity from an SRRG monotone flow.

**TODO(EPIC_047):** replace with a real implication into `RecordEntropy.Theorems.Monotonicity`.
-/
theorem record_entropy_monotonicity_from_monotone_srrg_flow
    (_h : SrrgLean.Core.IsMonotoneFlow P C F) :
    True := trivial

end SrrgLean.Bridges
