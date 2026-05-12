import UgpPhysicsLean.IPT.InformationProfitThreshold

/-!
# Applications — IPT as an information-efficiency fixed point

Certified content lives in `UgpPhysicsLean.IPT`; this module is the SRRG-facing entry point.
-/

namespace SrrgLean.Applications

noncomputable abbrev information_profit_threshold : ℝ := UgpLean.IPT.IPT_threshold

theorem ipt_is_derived_closed_form :
    UgpLean.IPT.IPT_threshold =
      1 + Real.log Real.goldenRatio / (2 * Real.log (2 * Real.pi)) :=
  UgpLean.IPT.IPT_theorem

end SrrgLean.Applications
