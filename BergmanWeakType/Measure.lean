/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Definitions
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Normalization and support of Bergman area measures -/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

theorem area_ball (c : ℂ) (r : ℝ) : area (Metric.ball c r) = ENNReal.ofReal r ^ 2 := by
  rw [area, Measure.smul_apply, smul_eq_mul, Complex.volume_ball]
  rw [ENNReal.ofReal_inv_of_pos Real.pi_pos, ← NNReal.coe_real_pi,
    ENNReal.ofReal_coe_nnreal]
  rw [mul_left_comm,
    ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr NNReal.pi_ne_zero) ENNReal.coe_ne_top,
    mul_one]

theorem area_closedBall (c : ℂ) (r : ℝ) :
    area (Metric.closedBall c r) = ENNReal.ofReal r ^ 2 := by
  rw [area, Measure.smul_apply, smul_eq_mul, Complex.volume_closedBall]
  rw [ENNReal.ofReal_inv_of_pos Real.pi_pos, ← NNReal.coe_real_pi,
    ENNReal.ofReal_coe_nnreal]
  rw [mul_left_comm,
    ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr NNReal.pi_ne_zero) ENNReal.coe_ne_top,
    mul_one]

theorem area_disk : area disk = 1 := by
  simpa [disk] using area_ball 0 1

instance diskArea_isProbabilityMeasure : IsProbabilityMeasure diskArea where
  measure_univ := by simpa [diskArea] using area_disk

theorem diskArea_disk : diskArea disk = 1 := by
  simpa [diskArea] using area_disk

theorem ae_mem_disk : ∀ᵐ z ∂diskArea, z ∈ disk :=
  ae_restrict_mem Metric.isOpen_ball.measurableSet

theorem ae_mem_disk_weightedArea (α : ℝ) : ∀ᵐ z ∂weightedArea α, z ∈ disk := by
  exact (withDensity_absolutelyContinuous diskArea _).ae_le ae_mem_disk

/-- Under normalized disk area, the squared radius is uniform on the unit interval. -/
theorem map_norm_sq_diskArea :
    diskArea.map (fun z : ℂ ↦ ‖z‖ ^ 2) = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  apply Measure.ext_of_Iic
  intro t
  rw [Measure.map_apply (by fun_prop : Measurable (fun z : ℂ ↦ ‖z‖ ^ 2)) measurableSet_Iic]
  by_cases ht : 0 ≤ t
  · have hpre : (fun z : ℂ ↦ ‖z‖ ^ 2) ⁻¹' Set.Iic t =
        Metric.closedBall (0 : ℂ) (Real.sqrt t) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_Iic, Metric.mem_closedBall, dist_zero_right]
      exact (Real.le_sqrt (norm_nonneg z) ht).symm
    rw [hpre]
    by_cases ht1 : t < 1
    · have hsub : Metric.closedBall (0 : ℂ) (Real.sqrt t) ⊆ disk := by
        intro z hz
        exact lt_of_le_of_lt hz ((Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
          (by simpa using ht1))
      rw [diskArea, Measure.restrict_eq_self _ hsub, area_closedBall,
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg t), Real.sq_sqrt ht,
        Measure.restrict_apply measurableSet_Iic]
      have hset : Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 t := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        constructor
        · rintro ⟨hxt, hx0, _⟩
          exact ⟨hx0, hxt⟩
        · rintro ⟨hx0, hxt⟩
          exact ⟨hxt, hx0, hxt.trans ht1.le⟩
      simp [hset]
    · have hsub : disk ⊆ Metric.closedBall (0 : ℂ) (Real.sqrt t) := by
        intro z hz
        exact le_trans (le_of_lt hz) ((Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) ht).2
          (by simpa using le_of_not_gt ht1))
      rw [diskArea, Measure.restrict_apply_superset hsub, area_disk,
        Measure.restrict_apply_superset (Set.Icc_subset_Iic_self.trans
          (Set.Iic_subset_Iic.mpr (le_of_not_gt ht1)))]
      simp
  · have hpre : (fun z : ℂ ↦ ‖z‖ ^ 2) ⁻¹' Set.Iic t = ∅ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
      exact not_le.mpr ((lt_of_not_ge ht).trans_le (sq_nonneg ‖z‖))
    rw [hpre, measure_empty, Measure.restrict_apply measurableSet_Iic]
    have hset : Set.Iic t ∩ Set.Icc (0 : ℝ) 1 = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro hxt hx0 _
      exact ht (hx0.trans hxt)
    simp [hset]

/-- The radial weight is normalized for every admissible exponent. -/
theorem weightedArea_univ (α : ℝ) (hα : -1 < α) : weightedArea α Set.univ = 1 := by
  rw [weightedArea, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  have hm : Measurable (fun u : ℝ ↦ ENNReal.ofReal ((α + 1) * (1 - u) ^ α)) := by
    fun_prop
  rw [← lintegral_map hm (by fun_prop : Measurable (fun z : ℂ ↦ ‖z‖ ^ 2)),
    map_norm_sq_diskArea]
  have hf : IntervalIntegrable (fun u : ℝ ↦ (1 - u) ^ α) volume 0 1 := by
    simpa using
      ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hα).comp_sub_left 1).symm
  have hfi : IntegrableOn (fun u : ℝ ↦ (α + 1) * (1 - u) ^ α) (Set.Icc 0 1) := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp (hf.const_mul (α + 1))
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun u : ℝ ↦ (α + 1) * (1 - u) ^ α) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (sub_nonneg.mpr hu.2) _)
  rw [← ofReal_integral_eq_lintegral_ofReal hfi hnonneg, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ α) 1]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl hα)]
  have hpos : 0 < α + 1 := by linarith
  simp [Real.zero_rpow hpos.ne', ne_of_gt hpos]

theorem weightedArea_isProbabilityMeasure (α : ℝ) (hα : -1 < α) :
    IsProbabilityMeasure (weightedArea α) :=
  ⟨weightedArea_univ α hα⟩

theorem diskArea_ball_pos {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    0 < diskArea (Metric.ball (0 : ℂ) r) := by
  rw [diskArea, disk, Measure.restrict_eq_self _ (Metric.ball_subset_ball hr1), area_ball]
  positivity

/-- The admissible radial weights have the same null sets as disk area. -/
theorem diskArea_absolutelyContinuous_weightedArea (α : ℝ) (hα : -1 < α) :
    diskArea ≪ weightedArea α := by
  apply withDensity_absolutelyContinuous'
  · fun_prop
  · filter_upwards [ae_mem_disk] with z hz
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    apply mul_pos (by linarith)
    apply Real.rpow_pos_of_pos
    have hz_norm : ‖z‖ < 1 := by simpa [disk] using hz
    nlinarith [norm_nonneg z]

theorem weightedArea_ball_pos (α : ℝ) (hα : -1 < α) {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) : 0 < weightedArea α (Metric.ball (0 : ℂ) r) := by
  exact pos_iff_ne_zero.mpr fun h ↦
    (diskArea_ball_pos hr hr1).ne' (diskArea_absolutelyContinuous_weightedArea α hα h)

end BergmanWeakType
