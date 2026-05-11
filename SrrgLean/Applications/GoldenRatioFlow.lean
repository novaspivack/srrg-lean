import UgpLean.GTE.LinearResponse

/-!
# Applications — golden-ratio contraction in linear response (Phase 3, SPEC_047 §5 P3.T3)

Certified as `UgpLean.GTE.abs_psi_eq_inv_phi` (lemma also cited in the IPT derivation).
-/

namespace SrrgLean.Applications

theorem linearized_flow_eigenvalue_abs_psi :
    |(1 - Real.sqrt 5) / 2| = 1 / Real.goldenRatio :=
  UgpLean.GTE.abs_psi_eq_inv_phi

end SrrgLean.Applications
