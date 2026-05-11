import UgpLean.GTE.LinearResponse

/-!
# Fixed points — linearized stability anchor (book §6.6)

The certified PSC Fibonacci eigenvalue `|ψ| = 1/φ` is the ugp-lean / IPT certificate
used as the contraction scale for transverse perturbations.
-/

namespace SrrgLean.FixedPoints

/-- Same contraction identity used throughout `UgpLean.IPT`. -/
theorem linearized_flow_contraction_rate :
    |(1 - Real.sqrt 5) / 2| = 1 / Real.goldenRatio :=
  UgpLean.GTE.abs_psi_eq_inv_phi

end SrrgLean.FixedPoints
