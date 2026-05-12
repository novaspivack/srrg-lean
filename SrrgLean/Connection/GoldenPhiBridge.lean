import UgpLean.GTE.LinearResponse

/-!
# Golden ratio / A1 bridge

GXT A1 is already proved in `ugp-lean` as `abs_psi_eq_inv_phi`.
This module re-exports it at the `srrg-lean` boundary for P27 narrative cohesion.
-/

namespace SrrgLean.Connection

/-- PSC update contraction (Fibonacci subdominant eigenvalue): **|ψ| = 1/φ**. -/
theorem a1_contraction_eigenvalue_abs :
    |(1 - Real.sqrt 5) / 2| = 1 / Real.goldenRatio :=
  UgpLean.GTE.abs_psi_eq_inv_phi

end SrrgLean.Connection
