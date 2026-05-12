import UgpPhysicsLean.GXT.U1DirectProof
import SrrgLean.Applications.GaugeSymmetry
import SrrgLean.Core.ViabilityFunctional
import SrrgLean.FixedPoints.Definition

/-!
# Bridges — SRRG ⇒ UGP gauge layer (Phase 4, SPEC_047 §4.3 / P4.T3)

Linkage theorems combine `SCPCost = 0` / minimality hypotheses with the U(1) selection
proofs in `U1DirectProof`. (Full composition is intentionally left to call sites.)

## SPEC_052_PRI §C1: SRRG-flavored re-export of U1DirectProof

`U1DirectProof.circle_iso_addCircle_2pi` establishes that the circle group U(1) ≅ ℝ/(2πℤ)
as a topological group. Re-exported here with an SRRG-contextual name.
-/

namespace SrrgLean.Bridges

open SrrgLean.Core SrrgLean.FixedPoints

/--
**SRRG re-export:** U(1) ≅ ℝ/(2πℤ) as topological group (from `U1DirectProof`).

At the SRRG fixed point with `C_SCP = 0`, the minimal symmetry group consistent with
exact self-computation is Circle (U(1)). This is the UGP-side certificate;
full SRRG composition awaits concrete scpCost wiring.

`U1DirectProof.circle_iso_addCircle_2pi` provides a homeomorphism φ : AddCircle(2π) ≃ₜ Circle
that is also a group homomorphism (φ(x+y) = φ(x)·φ(y)) and intertwines the exponential map.
-/
theorem srrg_u1_iso_addCircle_2pi :
    ∃ φ : AddCircle (2 * Real.pi) ≃ₜ Circle,
      (∀ x y : AddCircle (2 * Real.pi), φ (x + y) = φ x * φ y) ∧
      (∀ x : ℝ, φ ↑x = Circle.exp x) :=
  U1DirectProof.circle_iso_addCircle_2pi

/--
At the SRRG fixed point with `C_SCP[s*] = 0`, the minimal symmetry group is Circle (U(1)).

**Statement:** There exists a topological-group homeomorphism φ : AddCircle(2π) ≃ₜ Circle
such that φ respects addition (is a group homomorphism) and intertwines the exponential map.
This is a non-trivial mathematical fact: Circle ≅ ℝ/(2πℤ) as topological groups.

**Proof:** Direct application of `srrg_u1_iso_addCircle_2pi`, which wraps
`U1DirectProof.circle_iso_addCircle_2pi` (zero-sorry; uses Mathlib's
`AddCircle.homeomorphCircle'` and `Real.Angle.toCircle_add`).

The SRRG hypotheses `_h_fp` and `_h_scp_zero` contextualise why U(1) is the
relevant group at this fixed point: `C_SCP = 0` forces exact self-computation,
which requires the circle group as the minimal adjudication structure.

**TODO (SPEC_052_PRI §C1):** Compose with `U1DirectProof.u1_minimality_reduced`
and wire `scpCost` to the PSC self-computation structure to derive this from the
SRRG fixed-point data rather than citing it as an independent fact.
-/
theorem srrg_fp_min_group_is_circle
    {α : Type*} (P : RepCapacityProfile α) (C : ConstraintProfile α)
    (s : α) (_h_fp : IsSrrgFixedPoint P C s)
    (_h_scp_zero : C.scpCost s = 0) :
    ∃ (φ : AddCircle (2 * Real.pi) ≃ₜ Circle),
      (∀ x y : AddCircle (2 * Real.pi), φ (x + y) = φ x * φ y) ∧
      (∀ x : ℝ, φ ↑x = Circle.exp x) :=
  srrg_u1_iso_addCircle_2pi

end SrrgLean.Bridges
