import UgpPhysicsLean.IPT.InformationProfitThreshold
import SrrgLean.FixedPoints.Stability

/-!
# Physical constants at SRRG fixed points (book §7.3)

This module gathers **entry points** into the already-certified constants. Detailed
statements stay in `ugp-physics-lean` / `ugp-lean` to avoid duplicating large proof
terms.

- **IPT** → `UgpLean.IPT.IPT_threshold`, `UgpLean.IPT.IPT_theorem`
- **1/φ contraction** → `SrrgLean.FixedPoints.linearized_flow_contraction_rate`
  (= `UgpLean.GTE.abs_psi_eq_inv_phi`)
- **U(1) / gauge minimality** → import `UgpPhysicsLean.GXT.U1DirectProof` at proof sites
-/

namespace SrrgLean.FixedPoints

noncomputable def certified_information_profit_ratio : ℝ :=
  UgpLean.IPT.IPT_threshold

/-- Same identity as `linearized_flow_contraction_rate` (re-stated for readers of this module). -/
theorem certified_linear_contraction_rate :
    |(1 - Real.sqrt 5) / 2| = 1 / Real.goldenRatio :=
  linearized_flow_contraction_rate

end SrrgLean.FixedPoints
