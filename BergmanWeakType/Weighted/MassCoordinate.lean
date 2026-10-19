/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.PolarIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # The uniform mass coordinate for weighted disk area -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real

namespace BergmanWeakType

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem image_rpow_unit_interval {q : ℝ} (hq : 0 < q) :
    (fun x : ℝ ↦ x ^ q) '' Ioo 0 1 = Ioo 0 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rpow_pos_of_pos hx.1 _, rpow_lt_one hx.1.le hx.2 hq⟩
  · intro hy
    exact ⟨y ^ q⁻¹, ⟨rpow_pos_of_pos hy.1 _,
      rpow_lt_one hy.1.le hy.2 (inv_pos.mpr hq)⟩, rpow_inv_rpow hy.1.le hq.ne'⟩

theorem integral_unit_interval_rpow [CompleteSpace E] {q : ℝ} (hq : 0 < q)
    (F : ℝ → E) :
    (∫ y in Ioo (0 : ℝ) 1, F y) =
      ∫ x in Ioo (0 : ℝ) 1, (q * x ^ (q - 1)) • F (x ^ q) := by
  have hi : InjOn (fun x : ℝ ↦ x ^ q) (Ioo 0 1) := by
    intro x hx y hy hxy
    exact (rpow_left_inj hx.1.le hy.1.le hq.ne').mp hxy
  nth_rw 1 [← image_rpow_unit_interval hq]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun x hx ↦ (hasDerivAt_rpow_const (p := q) (Or.inl hx.1.ne')).hasDerivWithinAt) hi]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  dsimp only
  rw [abs_of_pos (mul_pos hq (rpow_pos_of_pos hx.1 _))]

/-- A radius whose exterior weighted disk has measure `y`. -/
def massRadius (α y : ℝ) : ℝ := sqrt (1 - y ^ (α + 1)⁻¹)

theorem massRadius_mem_unit {α y : ℝ} (hα : -1 < α) (hy : y ∈ Ioo (0 : ℝ) 1) :
    massRadius α y ∈ Ioo (0 : ℝ) 1 := by
  have hp : 0 < α + 1 := by linarith
  have hpow := rpow_lt_one hy.1.le hy.2 (inv_pos.mpr hp)
  constructor
  · exact sqrt_pos.mpr (sub_pos.mpr hpow)
  · exact (sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr
      (by simpa using sub_lt_self (1 : ℝ) (rpow_pos_of_pos hy.1 (α + 1)⁻¹))

theorem massRadius_antitone {α : ℝ} (hα : -1 < α) :
    AntitoneOn (massRadius α) (Icc 0 1) := by
  intro y hy u _ hyu
  apply sqrt_le_sqrt
  exact sub_le_sub_left (rpow_le_rpow hy.1 hyu (inv_nonneg.mpr (by linarith))) 1

theorem integral_weightedArea_eq_circleAverage_mass [CompleteSpace E] {α : ℝ}
    (hα : -1 < α) {f : ℂ → E} (hf : Integrable f (weightedArea α)) :
    ∫ z, f z ∂weightedArea α =
      ∫ y in (0 : ℝ)..1, circleAverage f 0 (massRadius α y) := by
  have hp : 0 < α + 1 := by linarith
  rw [integral_weightedArea_eq_diskArea hα,
    integral_diskArea_eq_circleAverage_sqrt_one_sub (integrable_weightedDensity_smul hα hf)]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
    integral_unit_interval_rpow hp (fun y ↦ circleAverage f 0 (massRadius α y))]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro y hy
  have hs : 0 ≤ 1 - y := sub_nonneg.mpr hy.2.le
  have hrad : massRadius α (y ^ (α + 1)) = sqrt (1 - y) := by
    simp only [massRadius, rpow_rpow_inv hy.1.le hp.ne']
  dsimp only
  rw [hrad, add_sub_cancel_right, ← circleAverage_fun_smul]
  apply circleAverage_congr_sphere
  intro z hz
  have hn : ‖z‖ = sqrt (1 - y) := by
    simpa only [Metric.mem_sphere, dist_zero_right, abs_of_nonneg (sqrt_nonneg _)] using hz
  dsimp only
  rw [hn, sq_sqrt hs, sub_sub_cancel]

end BergmanWeakType
