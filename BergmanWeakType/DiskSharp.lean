/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.DiskCap
public import BergmanWeakType.Rigidity.PolarIntegral
public import BergmanWeakType.Reproduction

/-! # Sharp weak type constants on the unit disk -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace BergmanWeakType

open Weighted

theorem positiveProjection_level_iff {f : ℂ → ℂ} (hf : Integrable f diskArea)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ disk) :
    ENNReal.ofReal t < positiveProjection f z ↔
      t * (1 - ‖z‖ ^ 2) < diskPotential f z := by
  rw [diskPotential_eq hz, normalizedPotential_eq_mul_positiveProjection_toReal hf hz,
    ENNReal.ofReal_lt_iff_lt_toReal ht (positiveProjection_lt_top hf hz).ne]
  have hm : 0 < 1 - ‖z‖ ^ 2 := by
    have hz' := (mem_disk_iff z).mp hz
    nlinarith [norm_nonneg z]
  simpa only [mul_comm t] using (mul_lt_mul_iff_right₀ hm).symm

/-- The angular distribution in complementary squared radius is exactly disk area. -/
theorem integral_levelFraction_eq_measure {f : ℂ → ℂ} (hf : Integrable f diskArea)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ y in (0 : ℝ)..1, levelFraction f t y) =
      diskArea.real {z | ENNReal.ofReal t < positiveProjection f z} := by
  let S := disk ∩ {z : ℂ | t * (1 - ‖z‖ ^ 2) < diskPotential f z}
  have hS : MeasurableSet S := measurableSet_disk.inter
    (measurableSet_lt (by fun_prop) (measurable_diskPotential hf))
  have hSi : Integrable (S.indicator (fun _ ↦ (1 : ℝ))) diskArea :=
    (integrable_const 1).indicator hS
  have hm : diskArea S = diskArea {z | ENNReal.ofReal t < positiveProjection f z} := by
    apply measure_congr
    filter_upwards [ae_mem_disk] with z hz
    simp only [S, mem_inter_iff, mem_ofPred_eq, hz, true_and]
    exact propext (positiveProjection_level_iff hf ht hz).symm
  calc
    _ = ∫ y in (0 : ℝ)..1,
        circleAverage (S.indicator (fun _ ↦ (1 : ℝ))) 0 (sqrt (1 - y)) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro y hy
      apply circleAverage_congr_sphere
      intro z hz
      have hzNorm : ‖z‖ = sqrt (1 - y) := by
        simpa only [Metric.mem_sphere, dist_zero_right, abs_of_nonneg (sqrt_nonneg _)] using hz
      have hzSq : ‖z‖ ^ 2 = 1 - y := by
        rw [hzNorm, sq_sqrt (sub_nonneg.mpr hy.2)]
      have hzdisk : z ∈ disk := by
        apply (mem_disk_iff z).mpr
        nlinarith [norm_nonneg z, hy.1]
      have hpred : z ∈ S ↔ t * y < diskPotential f z := by
        simp only [S, mem_inter_iff, mem_ofPred_eq, hzdisk, true_and, hzSq, sub_sub_cancel]
      by_cases hzS : z ∈ S
      · simp only [indicator_of_mem hzS, ite_eq_left (hpred.mp hzS)]
      · simp only [indicator_of_notMem hzS, ite_eq_right (not_congr hpred |>.mp hzS)]
    _ = ∫ z, S.indicator (fun _ ↦ (1 : ℝ)) z ∂diskArea :=
      (integral_diskArea_eq_circleAverage_sqrt_one_sub hSi).symm
    _ = diskArea.real S := by
      simpa using integral_indicator_const (μ := diskArea) (1 : ℝ) hS
    _ = _ := congrArg ENNReal.toReal hm

/-- The positive Bergman projection has weak type bound one on the unit disk. -/
theorem isWeakTypeBound_positiveProjection_one :
    IsWeakTypeBound diskArea positiveProjection 1 := by
  intro f hf t ht
  rw [one_mul]
  have hi := integral_mul_levelFraction_le hf ht.le
  rw [intervalIntegral.integral_const_mul, integral_levelFraction_eq_measure hf ht.le] at hi
  have he := ENNReal.ofReal_le_ofReal hi
  rw [ENNReal.ofReal_mul ht.le, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _), ofReal_integral_norm_eq_lintegral_enorm hf] at he
  exact he

/-- The sharp weak type constant of the positive disk Bergman projection is one. -/
theorem positiveProjection_constant_eq_one : weakTypeConstant diskArea positiveProjection = 1 :=
  le_antisymm (weakTypeConstant_le_of_bound isWeakTypeBound_positiveProjection_one)
    one_le_positiveProjection_constant

/-- The sharp weak type constant of the complex disk Bergman projection is one. -/
theorem projection_constant_eq_one :
    weakTypeConstant diskArea (fun f z ↦ ‖projection f z‖ₑ) = 1 := by
  apply le_antisymm _ one_le_projection_constant
  exact projection_constant_le_positiveProjection_constant.trans_eq
    positiveProjection_constant_eq_one

end BergmanWeakType
