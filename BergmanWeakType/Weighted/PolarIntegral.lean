/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.PolarIntegral

/-! # Polar integration for normalized weighted disk area -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weightedDensity_nonneg_ae {α : ℝ} (hα : -1 < α) :
    ∀ᵐ z ∂diskArea, 0 ≤ (α + 1) * (1 - ‖z‖ ^ 2) ^ α := by
  filter_upwards [ae_mem_disk] with z hz
  apply mul_nonneg (by linarith)
  apply Real.rpow_nonneg
  have hz' : ‖z‖ < 1 := by simpa [disk] using hz
  nlinarith [norm_nonneg z]

theorem integrable_weightedDensity_smul {α : ℝ} (hα : -1 < α) {f : ℂ → E}
    (hf : Integrable f (weightedArea α)) :
    Integrable (fun z ↦ ((α + 1) * (1 - ‖z‖ ^ 2) ^ α) • f z) diskArea := by
  have hm : Measurable (fun z : ℂ ↦ ENNReal.ofReal ((α + 1) * (1 - ‖z‖ ^ 2) ^ α)) := by
    fun_prop
  have hi := (integrable_withDensity_iff_integrable_smul' hm
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mp hf
  apply hi.congr
  filter_upwards [weightedDensity_nonneg_ae hα] with z hz
  simp only [ENNReal.toReal_ofReal hz]

theorem integral_weightedArea_eq_diskArea [CompleteSpace E] {α : ℝ} (hα : -1 < α)
    (f : ℂ → E) :
    ∫ z, f z ∂weightedArea α =
      ∫ z, ((α + 1) * (1 - ‖z‖ ^ 2) ^ α) • f z ∂diskArea := by
  rw [weightedArea, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [weightedDensity_nonneg_ae hα] with z hz
  simp only [ENNReal.toReal_ofReal hz]

theorem integral_weightedArea_eq_circleAverage [CompleteSpace E] {α : ℝ} (hα : -1 < α)
    {f : ℂ → E} (hf : Integrable f (weightedArea α)) :
    ∫ z, f z ∂weightedArea α = ∫ r in Set.Ioo (0 : ℝ) 1,
      (2 * r * ((α + 1) * (1 - r ^ 2) ^ α)) • Real.circleAverage f 0 r := by
  rw [integral_weightedArea_eq_diskArea hα,
    integral_diskArea_eq_circleAverage (integrable_weightedDensity_smul hα hf)]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  dsimp only
  rw [mul_smul (2 * r)]
  congr 1
  rw [← Real.circleAverage_fun_smul]
  apply Real.circleAverage_congr_sphere
  intro z hz
  have hz' : ‖z‖ = r := by simpa only [Metric.mem_sphere, dist_zero_right, abs_of_pos hr.1] using hz
  dsimp only
  rw [hz']

end BergmanWeakType
