/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.WeightedPotential
public import BergmanWeakType.Weighted.RadialLevel
public import BergmanWeakType.Weighted.MassCoordinate
public import BergmanWeakType.Weighted.AnnularSharpness
public import BergmanWeakType.Comparison

/-! # Sharp positive weighted constants and the complex weighted upper bound -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace BergmanWeakType

open Weighted

theorem integral_weightedLevelFraction_le {α : ℝ} (hα : -1 < α) {f : ℂ → ℂ}
    (hf : Integrable f (weightedArea α)) {t : ℝ} (ht : 0 ≤ t) :
    (∫ y in (0 : ℝ)..1,
      t * radialLevelFraction (weightedDiskPotential α f) (massRadius α) t y) ≤
      ∫ w, ‖f w‖ ∂weightedArea α := by
  apply integral_mul_radialLevelFraction_le (measurable_weightedDiskPotential hα hf)
    (weightedDiskPotential_nonneg α f) (by unfold massRadius; fun_prop) _ _ ht
  · intro c y hy u hu hyu
    exact antitoneOn_circleAverage_min_weightedDiskPotential hα hf c
      ⟨(massRadius_mem_unit hα hu).1.le, (massRadius_mem_unit hα hu).2⟩
      ⟨(massRadius_mem_unit hα hy).1.le, (massRadius_mem_unit hα hy).2⟩
      (massRadius_antitone hα ⟨hy.1.le, hy.2.le⟩ ⟨hu.1.le, hu.2.le⟩ hyu)
  · intro y hy c
    exact circleAverage_min_weightedDiskPotential_le_mass hα hf
      ⟨(massRadius_mem_unit hα hy).1.le, (massRadius_mem_unit hα hy).2⟩ c

theorem integral_radialLevelFraction_eq_weightedMeasure {α : ℝ} (hα : -1 < α)
    {U : ℂ → ℝ} (hU : Measurable U) (t : ℝ) :
    (∫ y in (0 : ℝ)..1, radialLevelFraction U (massRadius α) t y) =
      (weightedArea α).real (disk ∩ {z | t * (1 - ‖z‖ ^ 2) ^ (α + 1) < U z}) := by
  let := weightedArea_isProbabilityMeasure α hα
  let S := disk ∩ {z : ℂ | t * (1 - ‖z‖ ^ 2) ^ (α + 1) < U z}
  have hS : MeasurableSet S := measurableSet_disk.inter
    (measurableSet_lt (by fun_prop) hU)
  have hSi : Integrable (S.indicator (fun _ ↦ (1 : ℝ))) (weightedArea α) :=
    (integrable_const 1).indicator hS
  have heq : (∫ y in (0 : ℝ)..1, radialLevelFraction U (massRadius α) t y) =
      ∫ y in (0 : ℝ)..1, circleAverage (S.indicator (fun _ ↦ (1 : ℝ))) 0 (massRadius α y) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro y hy
    apply circleAverage_congr_sphere
    intro z hz
    have hr := massRadius_mem_unit hα hy
    have hn : ‖z‖ = massRadius α y := by
      simpa only [Metric.mem_sphere, dist_zero_right, abs_of_pos hr.1] using hz
    have hzD : z ∈ disk := (mem_disk_iff z).mpr (hn.trans_lt hr.2)
    have hp : 0 < α + 1 := by linarith
    have hbase : 0 ≤ 1 - y ^ (α + 1)⁻¹ :=
      sub_nonneg.mpr (rpow_lt_one hy.1.le hy.2 (inv_pos.mpr hp)).le
    have hpow : (1 - ‖z‖ ^ 2) ^ (α + 1) = y := by
      rw [hn, massRadius, sq_sqrt hbase, sub_sub_cancel,
        rpow_inv_rpow hy.1.le hp.ne']
    have hpred : z ∈ S ↔ t * y < U z := by
      simp only [S, mem_inter_iff, mem_ofPred_eq, hzD, true_and, hpow]
    by_cases hzS : z ∈ S
    · simp only [indicator_of_mem hzS, ite_eq_left (hpred.mp hzS)]
    · simp only [indicator_of_notMem hzS, ite_eq_right (not_congr hpred |>.mp hzS)]
  rw [heq, ← integral_weightedArea_eq_circleAverage_mass hα hSi]
  simpa using integral_indicator_const (μ := weightedArea α) (1 : ℝ) hS

theorem weightedPositiveProjection_level_subset {α : ℝ} (hα : -1 < α) {f : ℂ → ℂ}
    (hf : Integrable f (weightedArea α)) {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ disk)
    (hlevel : ENNReal.ofReal t < weightedPositiveProjection α f z) :
    (t / gammaConstant α) * (1 - ‖z‖ ^ 2) ^ (α + 1) < weightedDiskPotential α f z := by
  have hz1 := (mem_disk_iff z).mp hz
  have hJ : 0 < normalizer α ‖z‖ := normalizer_pos hα (by simpa using hz1)
  have hD := gammaConstant_pos hα
  have hm : 0 < (1 - ‖z‖ ^ 2) ^ (α + 1) :=
    rpow_pos_of_pos (by nlinarith [norm_nonneg z]) _
  have hbound := radialMass_mul_normalizer_le hα (norm_nonneg z) hz1
  have hF : t < weightedPotential α f z := by
    rw [weightedPotential_eq_toReal hα hf hz]
    exact (ENNReal.ofReal_lt_iff_lt_toReal ht
      (weightedPositiveProjection_lt_top hα hf hz).ne).mp hlevel
  rw [weightedDiskPotential_eq hz, weightedNormalizedPotential, lt_div_iff₀ hJ]
  have hscale := mul_le_mul_of_nonneg_left hbound (div_nonneg ht hD.le)
  have hcancel : (t / gammaConstant α) * gammaConstant α = t := div_mul_cancel₀ t hD.ne'
  rw [hcancel] at hscale
  calc
    _ = (t / gammaConstant α) * ((1 - ‖z‖ ^ 2) ^ (α + 1) * normalizer α ‖z‖) := by ring
    _ ≤ t := hscale
    _ < _ := hF

/-- The sharp positive weighted weak type bound for every admissible standard weight. -/
theorem isWeakTypeBound_weightedPositiveProjection {α : ℝ} (hα : -1 < α) :
    IsWeakTypeBound (weightedArea α) (weightedPositiveProjection α)
      (ENNReal.ofReal (gammaConstant α)) := by
  let := weightedArea_isProbabilityMeasure α hα
  intro f hf t ht
  let s := t / gammaConstant α
  have hs : 0 < s := div_pos ht (gammaConstant_pos hα)
  have hi := integral_weightedLevelFraction_le hα hf hs.le
  rw [intervalIntegral.integral_const_mul,
    integral_radialLevelFraction_eq_weightedMeasure hα (measurable_weightedDiskPotential hα hf)] at hi
  have hm : weightedArea α {z | ENNReal.ofReal t < weightedPositiveProjection α f z} ≤
      weightedArea α (disk ∩ {z | s * (1 - ‖z‖ ^ 2) ^ (α + 1) < weightedDiskPotential α f z}) := by
    apply measure_mono_ae
    filter_upwards [ae_mem_disk_weightedArea α] with z hz
    exact fun hlev ↦ ⟨hz, weightedPositiveProjection_level_subset hα hf ht.le hz hlev⟩
  have hmreal := ENNReal.toReal_mono (measure_ne_top _ _) hm
  have hreal : t * (weightedArea α).real
      {z | ENNReal.ofReal t < weightedPositiveProjection α f z} ≤
      gammaConstant α * ∫ w, ‖f w‖ ∂weightedArea α := by
    have hsmall := (mul_le_mul_of_nonneg_left hmreal hs.le).trans hi
    have hlarge := mul_le_mul_of_nonneg_left hsmall (gammaConstant_pos hα).le
    have heq : gammaConstant α * s = t := mul_div_cancel₀ t (gammaConstant_pos hα).ne'
    simpa only [← mul_assoc, heq, measureReal_def] using! hlarge
  have he := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_mul ht.le, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_mul (gammaConstant_pos hα).le,
    ofReal_integral_norm_eq_lintegral_enorm hf] at he
  exact he

theorem weightedPositiveProjection_constant_eq (α : ℝ) (hα : -1 < α) :
    weakTypeConstant (weightedArea α) (weightedPositiveProjection α) =
      ENNReal.ofReal (gammaConstant α) :=
  le_antisymm (weakTypeConstant_le_of_bound (isWeakTypeBound_weightedPositiveProjection hα))
    (gammaConstant_le_weightedPositiveProjection_constant α hα)

theorem weightedProjection_constant_le (α : ℝ) (hα : -1 < α) :
    weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) ≤
      ENNReal.ofReal (gammaConstant α) := by
  exact (weightedProjection_constant_le_weightedPositiveProjection_constant α).trans_eq
    (weightedPositiveProjection_constant_eq α hα)

end BergmanWeakType
