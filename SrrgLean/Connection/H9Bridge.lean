import UgpPhysicsLean.GXT.H9SelfConsistency
import UgpPhysicsLean.IPT.InformationProfitThreshold

/-!
# H9 self-consistency bridge (SPEC_046_Y8L **[H3]**)

Links `UgpPhysicsLean.GXT.H9SelfConsistency` to `UgpLean.IPT.IPT_threshold`.

(Definitions live at the module root of `H9SelfConsistency.lean`; short names resolve
after `import`.)
-/

namespace SrrgLean.Connection

open Real

/-- Match H9 `phi` to Mathlib `goldenRatio`. -/
theorem h9_phi_eq_goldenRatio : phi = goldenRatio := by
  unfold phi goldenRatio
  ring_nf

/-- The H9 closed form matches `UgpLean.IPT.IPT_threshold`. -/
theorem h9_ipt_val_eq_certified : IPT_val = UgpLean.IPT.IPT_threshold := by
  unfold IPT_val UgpLean.IPT.IPT_threshold UgpLean.IPT.IPT_Lambda
  rw [← h9_phi_eq_goldenRatio]
  ring

/-- Algebraic fixed point of the Landauer map equals certified IPT. -/
theorem ipt_landauer_map_fixed_point :
    1 / (1 - log 2 / N_universal) = UgpLean.IPT.IPT_threshold := by
  rw [ipt_self_consistent, h9_ipt_val_eq_certified]

end SrrgLean.Connection
