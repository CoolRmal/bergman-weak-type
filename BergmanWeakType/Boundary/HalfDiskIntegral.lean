/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.Normalizer
public import BergmanWeakType.Rigidity.PolarIntegral

/-! # The half-disk power integral in the boundary concentration limit -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real
open scoped Topology ENNReal

namespace BergmanWeakType

/-- The limiting density after blowing up a boundary cap at the point one. -/
def halfDiskPower (α : ℝ) (z : ℂ) : ℝ :=
  if 0 < z.re then (2 * z.re) ^ α else 0

theorem measurable_halfDiskPower (α : ℝ) : Measurable (halfDiskPower α) := by
  unfold halfDiskPower
  have hm : Measurable (fun z : ℂ ↦ (2 * z.re) ^ α) := by fun_prop
  exact hm.ite (measurableSet_lt measurable_const Complex.measurable_re) measurable_const

theorem halfDiskPower_nonneg (α : ℝ) (z : ℂ) : 0 ≤ halfDiskPower α z := by
  unfold halfDiskPower
  split_ifs with h
  · exact Real.rpow_nonneg (by positivity) _
  · exact le_rfl

theorem halfDiskPower_le {α : ℝ} (hα : 0 ≤ α) {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) :
    halfDiskPower α z ≤ (2 * R) ^ α := by
  unfold halfDiskPower
  split_ifs with h
  · apply Real.rpow_le_rpow (by positivity) _ hα
    exact mul_le_mul_of_nonneg_left ((Complex.re_le_norm z).trans hz) (by norm_num)
  · exact Real.rpow_nonneg (by linarith [norm_nonneg z]) _

theorem integrable_halfDiskPower {α : ℝ} (hα : 0 ≤ α) :
    Integrable (halfDiskPower α) diskArea := by
  apply (integrable_const ((2 : ℝ) ^ α)).mono' (measurable_halfDiskPower α).aestronglyMeasurable
  filter_upwards [ae_mem_disk] with z hz
  rw [Real.norm_of_nonneg (halfDiskPower_nonneg α z)]
  simpa only [mul_one] using halfDiskPower_le hα ((mem_disk_iff z).mp hz).le

theorem intervalIntegrable_halfDiskPower_circle {α : ℝ} (hα : 0 ≤ α) (r η a b : ℝ)
    (hab : a ≤ b) :
    IntervalIntegrable (fun θ ↦ halfDiskPower α (circleMap 0 r (θ + η))) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  apply Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
    ((measurable_halfDiskPower α).comp
      ((continuous_circleMap 0 r).comp (continuous_id.add_const η)).measurable).aestronglyMeasurable
      (M := (2 * |r|) ^ α)
  apply Filter.Eventually.of_forall
  intro θ
  dsimp only [Function.comp_def, id_eq]
  rw [Real.norm_of_nonneg (halfDiskPower_nonneg α _)]
  exact halfDiskPower_le hα (by simp)

theorem circleAverage_halfDiskPower {α : ℝ} (hα : 0 ≤ α) {r : ℝ} (hr : 0 < r) :
    circleAverage (halfDiskPower α) 0 r = r ^ α * gammaConstant α / 2 := by
  let H := fun θ ↦ halfDiskPower α (circleMap 0 r (θ + -(π / 2)))
  have hpoint (θ : ℝ) : H θ = if 0 < sin θ then (2 * r) ^ α * sin θ ^ α else 0 := by
    dsimp only [H, halfDiskPower]
    rw [circleMap_zero_re, ← sub_eq_add_neg, cos_sub_pi_div_two]
    simp only [mul_pos_iff_of_pos_left hr]
    split_ifs with hs
    · rw [show 2 * (r * sin θ) = (2 * r) * sin θ by ring]
      exact Real.mul_rpow (by positivity) hs.le
    · rfl
  have hleft : (∫ θ in (0 : ℝ)..π, H θ) =
      (2 * r) ^ α * ∫ θ in (0 : ℝ)..π, sin θ ^ α := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le pi_pos.le
    intro θ hθ
    rw [hpoint, ite_eq_left (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)]
  have hright : (∫ θ in π..2 * π, H θ) = 0 := by
    rw [← intervalIntegral.integral_zero (a := π) (b := 2 * π)]
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith [pi_pos])
    intro θ hθ
    have hs : sin θ ≤ 0 := by
      have hn := sin_nonpos_of_nonpos_of_neg_pi_le
        (show θ - 2 * π ≤ 0 by linarith [hθ.2])
        (show -π ≤ θ - 2 * π by linarith [hθ.1])
      simpa using hn
    rw [hpoint, ite_eq_right (not_lt.mpr hs)]
  rw [circleAverage_eq_integral_add (-(π / 2)), smul_eq_mul]
  change (2 * π)⁻¹ * (∫ θ in (0 : ℝ)..2 * π, H θ) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_halfDiskPower_circle hα r (-(π / 2)) 0 π pi_pos.le)
    (intervalIntegrable_halfDiskPower_circle hα r (-(π / 2)) π (2 * π) (by linarith [pi_pos])),
    hleft, hright, add_zero, integral_sin_rpow (by linarith : -1 < α),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le,
    gammaConstant_eq_boundaryGamma (by linarith : -1 < α)]
  have hs : sqrt π ^ 2 = π := sq_sqrt pi_pos.le
  have hsp : sqrt π ≠ 0 := (sqrt_pos.mpr pi_pos).ne'
  have hg : Real.Gamma (1 + α / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  field_simp
  nlinarith

theorem integral_halfDiskPower {α : ℝ} (hα : 0 ≤ α) :
    (∫ z, halfDiskPower α z ∂diskArea) = gammaConstant α / (α + 2) := by
  rw [integral_diskArea_eq_circleAverage (integrable_halfDiskPower hα)]
  have heq : (∫ r in Ioo (0 : ℝ) 1, (2 * r) • circleAverage (halfDiskPower α) 0 r) =
      gammaConstant α * ∫ r in Ioo (0 : ℝ) 1, r ^ (α + 1) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    dsimp only
    rw [circleAverage_halfDiskPower hα hr.1, smul_eq_mul, Real.rpow_add hr.1,
      Real.rpow_one]
    ring
  rw [heq, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_rpow (Or.inl (by linarith : -1 < α + 1))]
  rw [one_rpow, zero_rpow (by linarith : α + 1 + 1 ≠ 0), sub_zero]
  ring

end BergmanWeakType
