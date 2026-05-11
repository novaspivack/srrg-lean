import UgpPhysicsLean.GXT.LieExpSurjective

/-!
# U(1) / circle exponential bridge (A2 limb)

`circle_exp_surjective_MAIN` is the zero-sorry entry point used in GXT for the
compact connected 1D Lie group picture (Phase / adjudication circle).
-/

namespace SrrgLean.Connection

/-- `Circle.exp : ℝ → Circle` is surjective (UGP / GXT main lemma). -/
theorem circle_exp_surjective : Function.Surjective Circle.exp :=
  LieExpSurjective.circle_exp_surjective_MAIN

end SrrgLean.Connection
