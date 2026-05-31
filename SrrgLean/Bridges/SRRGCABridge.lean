import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Real.GoldenRatio
import SrrgLean.Core.CMCALanguage

/-!
# SRRG–CA scalar bridge (CatAL)

Coupling-axis MDL functional `K_CMCA(g) = -log₂(g² + g)` and SRRG β-function
`β_SRRG(g) = g(1 - g - g²)`. Certified zero-sorry results matching
`UgpLean.Algebra.SRRGCABridge` (ugp-lean-exp).

At `g* = 1/φ = srrgFixedPoint`: `K_CMCA(g*) = 0` and `β_SRRG(g*) = 0`.
For `g > 0`, both vanish iff `g = g*` (unique positive root of `g² + g = 1`).
-/

namespace SrrgLean.Bridges.SRRGCABridge

open SrrgLean.Core.CMCALanguage
open Real

/-- SRRG / CA fixed-point coupling `g* = 1/φ = (√5 - 1)/2`. -/
noncomputable def srrgFixedPoint : ℝ := -Real.goldenConj

/-- Alias: scalar CMCA Kolmogorov on the coupling axis. -/
noncomputable abbrev kCMCA (g : ℝ) : ℝ := kCMCA_scalar g

/-- SRRG β-function: `β_SRRG(g) = g(1 - g - g²)`. -/
noncomputable def srrgBetaFn (g : ℝ) : ℝ := g * (1 - g - g ^ 2)

theorem ca_fixed_point_is_golden_ratio_recip :
    let x := (Real.sqrt 5 - 1) / 2
    x ^ 2 + x - 1 = 0 := by
  simp only
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  ring_nf
  nlinarith [h5, Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]

theorem srrg_fixed_point_in_unit_interval :
    0 < srrgFixedPoint ∧ srrgFixedPoint < 1 := by
  unfold srrgFixedPoint
  have hpos : 0 < -Real.goldenConj := by linarith [Real.goldenConj_neg]
  have hlt : -Real.goldenConj < 1 := by linarith [Real.neg_one_lt_goldenConj]
  exact ⟨hpos, hlt⟩

theorem srrg_fixed_point_eq_inv_phi : srrgFixedPoint = Real.goldenRatio⁻¹ := by
  unfold srrgFixedPoint
  exact Real.inv_goldenRatio.symm

theorem fca_attractor_diagonal_fp_equals_srrg_fp :
    srrgFixedPoint ^ 2 + srrgFixedPoint = 1 := by
  have hs : srrgFixedPoint = (Real.sqrt 5 - 1) / 2 := by
    unfold srrgFixedPoint Real.goldenConj; ring
  rw [hs]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-- **kCMCA_at_srrg_fp** (CatAL): `K_CMCA(g*) = 0`. -/
theorem kCMCA_at_srrg_fp : kCMCA srrgFixedPoint = 0 := by
  unfold kCMCA kCMCA_scalar
  have heq : srrgFixedPoint ^ 2 + srrgFixedPoint = 1 :=
    fca_attractor_diagonal_fp_equals_srrg_fp
  simp [heq, Real.logb_one]

theorem kCMCA_pos_of_lt_srrg_fp (g : ℝ) (hg : 0 < g) (hlt : g < srrgFixedPoint) :
    0 < kCMCA g := by
  unfold kCMCA kCMCA_scalar
  rw [neg_pos]
  have hgt0 : (0 : ℝ) < g ^ 2 + g := by positivity
  have hlt1 : g ^ 2 + g < 1 := by
    have hfp := fca_attractor_diagonal_fp_equals_srrg_fp
    nlinarith [sq_nonneg (srrgFixedPoint - g), srrg_fixed_point_in_unit_interval.1]
  rw [Real.logb]
  apply div_neg_of_neg_of_pos
  · exact Real.log_neg hgt0 hlt1
  · exact Real.log_pos (by norm_num)

theorem kCMCA_nonneg (g : ℝ) (hg : 0 < g) (hle : g ≤ srrgFixedPoint) :
    0 ≤ kCMCA g := by
  rcases eq_or_lt_of_le hle with rfl | hlt
  · simp [kCMCA_at_srrg_fp]
  · exact le_of_lt (kCMCA_pos_of_lt_srrg_fp g hg hlt)

/-- **srrg_beta_zero_iff_kCMCA_minimum** (CatAL): for `g > 0`, `β_SRRG(g) = 0 ↔ K_CMCA(g) = 0`. -/
theorem srrg_beta_zero_iff_kCMCA_minimum (g : ℝ) (hg : 0 < g) :
    srrgBetaFn g = 0 ↔ kCMCA g = 0 := by
  simp only [srrgBetaFn, kCMCA, kCMCA_scalar]
  have hpos : (0 : ℝ) < g ^ 2 + g := by positivity
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h1
    · linarith
    · have heq : g ^ 2 + g = 1 := by linarith
      simp [heq, Real.logb_one]
  · intro h
    rw [neg_eq_zero, Real.logb, div_eq_zero_iff] at h
    rcases h with hlog | hlog2
    · rw [Real.log_eq_zero] at hlog
      rcases hlog with h1 | h2 | h3
      · exact absurd h1 hpos.ne'
      · exact mul_eq_zero.mpr (Or.inr (by linarith))
      · exact absurd (show g ^ 2 + g > 0 from hpos) (by linarith [h3])
    · exact absurd hlog2 (Real.log_pos (by norm_num)).ne'

/-- **srrg_mdl_common_zero_is_g_star** (CatAL): for `g > 0`, `β_SRRG(g) = 0 ↔ g = g*`. -/
theorem srrg_mdl_common_zero_is_g_star (g : ℝ) (hg : 0 < g) :
    srrgBetaFn g = 0 ↔ g = srrgFixedPoint := by
  simp only [srrgBetaFn]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h1
    · linarith
    · have heq : g ^ 2 + g = 1 := by linarith
      have hdiff : (g - srrgFixedPoint) * (g + srrgFixedPoint + 1) = 0 := by
        nlinarith [fca_attractor_diagonal_fp_equals_srrg_fp, heq]
      rcases mul_eq_zero.mp hdiff with hg' | hsum
      · exact eq_of_sub_eq_zero hg'
      · have hsum_pos : 0 < g + srrgFixedPoint + 1 := by
          nlinarith [srrg_fixed_point_in_unit_interval.1, hg]
        linarith
  · intro h
    rw [h]
    have hfp := fca_attractor_diagonal_fp_equals_srrg_fp
    exact mul_eq_zero.mpr (Or.inr (by linarith))

/-- **kCMCA_zero_iff_eq_srrg_fp** (CatAL): on `(0, ∞)`, the MDL zero locus is `{g*}`. -/
theorem kCMCA_zero_iff_eq_srrg_fp (g : ℝ) (hg : 0 < g) :
    kCMCA g = 0 ↔ g = srrgFixedPoint := by
  constructor
  · intro h
    have hβ : srrgBetaFn g = 0 := (srrg_beta_zero_iff_kCMCA_minimum g hg).mpr h
    exact (srrg_mdl_common_zero_is_g_star g hg).mp hβ
  · intro h
    rw [h]
    exact kCMCA_at_srrg_fp

/-- **kCMCA_pos_of_ne_srrg_fp** (CatAL): strict positivity on `(0, g*)`. -/
theorem kCMCA_pos_of_ne_srrg_fp (g : ℝ) (hg : 0 < g) (hlt : g < srrgFixedPoint) :
    0 < kCMCA g :=
  kCMCA_pos_of_lt_srrg_fp g hg hlt

end SrrgLean.Bridges.SRRGCABridge
