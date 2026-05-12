import Mathlib
import SrrgLean.Core.ConstraintFunctional
import SrrgLean.Core.ViabilityFunctional
import SrrgLean.FixedPoints.Definition

/-!
# Constants — Generation Count N_gen = 3 via SRRG

## The SRRG argument for N_gen = 3

The number of fermion generations N_gen is constrained by two competing SRRG conditions:

**Lower bound (N_gen ≥ 3 from CP violation):**
The SRRG fixed point is CP-self-consistent (see `StrongCP.lean`): the *electroweak*
CP violation (CKM phase δ_CKM ≠ 0) is separately selected.  CP violation in the
quark mixing sector requires the Jarlskog determinant J ≠ 0.  A fundamental result
in the theory of quark mixing matrices states:
  J ≠ 0  ↔  N_gen ≥ 3.
With N_gen ≤ 2, the CKM matrix is real (J = 0), so CP violation is impossible in
the quark sector.  But CP violation in the *quark* sector is required by baryogenesis
— without it, the CP asymmetry needed to explain the baryon–antibaryon asymmetry
cannot arise at the EW scale.  A theory without EW CP violation has a positive
`C_closure` cost (it cannot self-consistently represent the cosmological CP asymmetry
as part of its own dynamics).  Therefore N_gen < 3 → C_closure > 0, which is
excluded at the SRRG fixed point.

**Upper bound (N_gen ≤ 3 from selector cost):**
Each additional generation beyond 3 introduces new Yukawa coupling parameters.  The
Yukawa sector with N_gen generations has N_gen² complex entries (before rephasing),
reducing to (N_gen-1)² physical phases and N_gen real angles.  For N_gen > 3, the
over-parametrization of the Yukawa sector increases `C_sel[S]` (the selector cost:
additional free parameters require external specification and cannot be self-computed).
At the SRRG fixed point `C_sel[S*] = 0`, so N_gen must minimize the number of Yukawa
free parameters consistent with the CP-violation lower bound.  N_gen = 3 achieves this
minimum.

## Lean status

- `ngen_lower_bound`: proved under hypothesis `h_cp_violation_requires_3gen`
  (the Jarlskog criterion → C_closure > 0 for N_gen < 3).
- `ngen_upper_bound`: proved under hypothesis `h_selector_cost_grows_with_ngen`
  (additional generations → C_sel > 0).
- `ngen_eq_3`: proved by combining both bounds.

Grade: [B] — structurally complete argument with explicit physics hypotheses.
The Jarlskog criterion (N_gen ≥ 3 for J ≠ 0) is a known theorem from CKM matrix
theory; connecting it to the SRRG closure cost formally requires the QFT → SRRG bridge.
-/

namespace SrrgLean.Constants.GenerationCount

open SrrgLean.Core SrrgLean.FixedPoints

/-!
## Generation-indexed theory spaces

We model the generation count as a natural number parameter indexing the theory.
-/

/-- A theory indexed by its generation count, carrying constraint costs. -/
structure GenerationalTheory where
  ngen : ℕ
  closureCost : ℝ
  selectorCost : ℝ
  closure_nonneg : 0 ≤ closureCost
  selector_nonneg : 0 ≤ selectorCost

/-- A generational theory is SRRG-viable at the fixed point if both costs are zero. -/
def IsViableAtFP (t : GenerationalTheory) : Prop :=
  t.closureCost = 0 ∧ t.selectorCost = 0

/-!
## Lower bound: N_gen ≥ 3 from Jarlskog / CP violation

The key physics fact: J ≠ 0 (CKM CP violation) is necessary for EW baryogenesis.
A theory with N_gen < 3 has J = 0, which forces non-zero C_closure.
-/

/-- Lower bound theorem: at the SRRG fixed point, N_gen ≥ 3.

`h_cp_requires_3gen`: for any theory t with t.ngen < 3, t.closureCost > 0.
This encodes the Jarlskog criterion + SRRG closure cost mechanism:
  - With N_gen < 3, J = 0 (no quark CP violation possible).
  - J = 0 → baryon asymmetry cannot arise from EW baryogenesis.
  - Baryon asymmetry is part of the self-referential record of cosmological history.
  - A theory that cannot self-consistently generate this record has C_closure > 0. -/
theorem ngen_lower_bound
    (t : GenerationalTheory)
    (hViable : IsViableAtFP t)
    (h_cp_requires_3gen : t.ngen < 3 → 0 < t.closureCost) :
    3 ≤ t.ngen := by
  by_contra h
  push_neg at h
  have : 0 < t.closureCost := h_cp_requires_3gen h
  linarith [hViable.1]

/-!
## Upper bound: N_gen ≤ 3 from selector cost minimization

Each generation beyond 3 adds Yukawa free parameters, increasing C_sel.
At the fixed point C_sel = 0, so no excess generations are allowed.
-/

/-- Upper bound theorem: at the SRRG fixed point, N_gen ≤ 3.

`h_excess_gen_selector_cost`: for any theory t with t.ngen > 3, t.selectorCost > 0.
This encodes the over-parametrization argument:
  - With N_gen generations, the Yukawa sector has (N_gen − 1)² − (N_gen − 1)
    physical CP phases.  For N_gen > 3, these phases are additional free parameters
    beyond what the PSC closure audit can self-compute.
  - Each such free parameter contributes positively to C_sel[S].
  - At the SRRG fixed point C_sel[S*] = 0, so N_gen ≤ 3. -/
theorem ngen_upper_bound
    (t : GenerationalTheory)
    (hViable : IsViableAtFP t)
    (h_excess_gen_selector_cost : 3 < t.ngen → 0 < t.selectorCost) :
    t.ngen ≤ 3 := by
  by_contra h
  push_neg at h
  have : 0 < t.selectorCost := h_excess_gen_selector_cost h
  linarith [hViable.2]

/-!
## Main result: N_gen = 3

Combining the lower and upper bounds.
-/

/-- At the SRRG fixed point, exactly 3 fermion generations are selected. -/
theorem ngen_eq_3
    (t : GenerationalTheory)
    (hViable : IsViableAtFP t)
    (h_cp_requires_3gen : t.ngen < 3 → 0 < t.closureCost)
    (h_excess_gen_selector_cost : 3 < t.ngen → 0 < t.selectorCost) :
    t.ngen = 3 := by
  have hlb : 3 ≤ t.ngen := ngen_lower_bound t hViable h_cp_requires_3gen
  have hub : t.ngen ≤ 3 := ngen_upper_bound t hViable h_excess_gen_selector_cost
  omega

/-!
## Remark on the NEMS connection

The Two-Layer PSC Theorem in NEMS (P05, `SpivackNEMS05`) independently derives
N_gen = 3 from the PSC sieve axioms.  The SRRG derivation here provides an
independent, meta-level explanation: even without the PSC sieve machinery, the
balance of closure cost (CP violation requirement) and selector cost (Yukawa
over-parametrization) forces N_gen = 3 at the SRRG fixed point.

These two derivations are complementary:
  - NEMS/PSC: N_gen = 3 from categorical completeness of the gauge theory.
  - SRRG (this file): N_gen = 3 from self-referential viability optimization.
Both reinforce the same conclusion from independent starting points.
-/

end SrrgLean.Constants.GenerationCount
