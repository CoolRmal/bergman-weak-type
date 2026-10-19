/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Kernel
public import BergmanWeakType.Measure
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # Integrability of the Bergman integral formulas

For each interior output point, both kernel columns are bounded on the input disk. Consequently
their products with integrable inputs are integrable. The Bochner integrals defining the complex
projections therefore represent genuine integrable functions, and the positive outputs are finite.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

theorem measurableSet_disk : MeasurableSet disk := Metric.isOpen_ball.measurableSet

theorem ae_mem_disk_weighted (α : ℝ) : ∀ᵐ w ∂weightedArea α, w ∈ disk :=
  (withDensity_absolutelyContinuous diskArea _).ae_le ae_mem_disk

/-- A fixed interior output point keeps the kernel denominator uniformly away from zero. -/
theorem kernel_denominator_norm_lower (z : ℂ) {w : ℂ} (hw : w ∈ disk) :
    1 - ‖z‖ ≤ ‖1 - z * star w‖ := by
  have hmul : ‖z * star w‖ ≤ ‖z‖ := by
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_right (norm_nonneg z) ((mem_disk_iff w).mp hw).le
  calc
    1 - ‖z‖ ≤ 1 - ‖z * star w‖ := sub_le_sub_left hmul 1
    _ ≤ ‖1 - z * star w‖ := by simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) _

theorem norm_kernel_le {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk) :
    ‖kernel z w‖ ≤ (1 - ‖z‖)⁻¹ ^ 2 := by
  rw [norm_kernel]
  exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _))
    (inv_anti₀ (sub_pos.mpr ((mem_disk_iff z).mp hz))
      (kernel_denominator_norm_lower z hw)) 2

theorem norm_weightedKernel_le {α : ℝ} (hα : -1 < α) {z w : ℂ}
    (hz : z ∈ disk) (hw : w ∈ disk) :
    ‖weightedKernel α z w‖ ≤ (1 - ‖z‖) ^ (-(α + 2)) := by
  rw [norm_weightedKernel]
  exact Real.rpow_le_rpow_of_nonpos (sub_pos.mpr ((mem_disk_iff z).mp hz))
    (kernel_denominator_norm_lower z hw) (by linarith)

/-- The principal-power kernel is continuous throughout the input disk. -/
theorem continuousOn_weightedKernel (α : ℝ) {z : ℂ} (hz : z ∈ disk) :
    ContinuousOn (weightedKernel α z) disk := by
  apply ContinuousOn.cpow_const
    (continuous_const.sub (continuous_const.mul continuous_star)).continuousOn
  intro w hw
  exact Complex.mem_slitPlane_iff.mpr (Or.inl (kernel_denominator_re_pos hz hw))

theorem continuousOn_kernel {z : ℂ} (hz : z ∈ disk) : ContinuousOn (kernel z) disk := by
  have h := continuousOn_weightedKernel 0 hz
  change ContinuousOn (fun w ↦ weightedKernel 0 z w) disk at h
  simpa only [weightedKernel_zero] using h

theorem aestronglyMeasurable_kernel {z : ℂ} (hz : z ∈ disk) :
    AEStronglyMeasurable (kernel z) diskArea :=
  (continuousOn_kernel hz).aestronglyMeasurable measurableSet_disk

theorem aestronglyMeasurable_weightedKernel (α : ℝ) {z : ℂ} (hz : z ∈ disk) :
    AEStronglyMeasurable (weightedKernel α z) (weightedArea α) :=
  ((continuousOn_weightedKernel α hz).aestronglyMeasurable
    (μ := area) measurableSet_disk).mono_ac (withDensity_absolutelyContinuous diskArea _)

/-- Every admissible input gives an integrable unweighted kernel integrand at an interior point. -/
theorem integrable_kernel_mul {f : ℂ → ℂ} (hf : Integrable f diskArea) {z : ℂ}
    (hz : z ∈ disk) : Integrable (fun w ↦ kernel z w * f w) diskArea := by
  apply hf.bdd_mul (aestronglyMeasurable_kernel hz)
  exact ae_mem_disk.mono fun w hw ↦ norm_kernel_le hz hw

/-- Every admissible input gives an integrable weighted kernel integrand at an interior point. -/
theorem integrable_weightedKernel_mul {α : ℝ} (hα : -1 < α) {f : ℂ → ℂ}
    (hf : Integrable f (weightedArea α)) {z : ℂ} (hz : z ∈ disk) :
    Integrable (fun w ↦ weightedKernel α z w * f w) (weightedArea α) := by
  apply hf.bdd_mul (aestronglyMeasurable_weightedKernel α hz)
  exact (ae_mem_disk_weighted α).mono fun w hw ↦ norm_weightedKernel_le hα hz hw

theorem positiveProjection_lt_top {f : ℂ → ℂ} (hf : Integrable f diskArea) {z : ℂ}
    (hz : z ∈ disk) : positiveProjection f z < ∞ := by
  simpa only [positiveProjection, enorm_mul, ofReal_norm] using
    (hasFiniteIntegral_iff_enorm.mp (integrable_kernel_mul hf hz).hasFiniteIntegral)

theorem weightedPositiveProjection_lt_top {α : ℝ} (hα : -1 < α) {f : ℂ → ℂ}
    (hf : Integrable f (weightedArea α)) {z : ℂ} (hz : z ∈ disk) :
    weightedPositiveProjection α f z < ∞ := by
  simpa only [weightedPositiveProjection, enorm_mul, ofReal_norm] using
    (hasFiniteIntegral_iff_enorm.mp
      (integrable_weightedKernel_mul hα hf hz).hasFiniteIntegral)

end BergmanWeakType
