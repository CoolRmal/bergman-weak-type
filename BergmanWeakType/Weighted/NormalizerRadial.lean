/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.RadialKernel
public import BergmanWeakType.Weighted.PolarPotential

/-! # The circular normalizer as a polar kernel potential -/

@[expose] public section

noncomputable section

open MeasureTheory Real

namespace BergmanWeakType.Weighted

theorem polarIntegral_boundary_eq_normalizer (α r θ : ℝ) :
    polarIntegral (polarKernel (-(α + 2) / 2)) cos sin
      (volume.restrict (Set.Icc 0 (2 * π))) (fun _ ↦ (2 * π)⁻¹) r θ =
        normalizer α r := by
  have hk (t : ℝ) : polarKernel (-(α + 2) / 2) (cos t) (sin t) r θ =
      ‖weightedKernel α (circleMap 0 r θ) (circleMap 0 1 t)‖ := by
    simpa only [circleMap_zero_re, circleMap_zero_im, one_mul] using
      polarKernel_eq_norm_weightedKernel α r θ (circleMap 0 1 t)
  have hcircle := circleAverage_weightedKernel_norm α (circleMap 0 r θ) (r := 1)
    (by norm_num)
  simp only [one_mul, norm_circleMap_zero] at hcircle
  have habs : normalizer α |r| = normalizer α r := by
    simp only [normalizer_eq_circleAverage_radius, circleAverage_abs_radius]
  rw [habs] at hcircle
  rw [polarIntegral]
  simp_rw [hk]
  rw [integral_mul_const, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  simpa only [Real.circleAverage_def, smul_eq_mul, mul_comm] using hcircle

def normalizerFirst (α r : ℝ) : ℝ :=
  polarIntegral (polarKernelR (-(α + 2) / 2)) cos sin
    (volume.restrict (Set.Icc 0 (2 * π))) (fun _ ↦ (2 * π)⁻¹) r 0

def normalizerSecond (α r : ℝ) : ℝ :=
  polarIntegral (polarKernelRR (-(α + 2) / 2)) cos sin
    (volume.restrict (Set.Icc 0 (2 * π))) (fun _ ↦ (2 * π)⁻¹) r 0

theorem normalizer_hasDerivAt (α : ℝ) {r : ℝ} (hr : r ^ 2 < 1) :
    HasDerivAt (normalizer α) (normalizerFirst α r) r := by
  have hd := polarIntegral_kernel_hasDerivAt_r isCompact_Icc
    (ae_restrict_mem measurableSet_Icc)
    (integrable_const (μ := volume.restrict (Set.Icc (0 : ℝ) (2 * π))) ((2 * π)⁻¹))
    continuous_cos.continuousOn continuous_sin.continuousOn
    (fun t _ ↦ (cos_sq_add_sin_sq t).le) (-(α + 2) / 2) hr 0
  simpa only [polarIntegral_boundary_eq_normalizer, normalizerFirst] using hd

theorem normalizerFirst_hasDerivAt (α : ℝ) {r : ℝ} (hr : r ^ 2 < 1) :
    HasDerivAt (normalizerFirst α) (normalizerSecond α r) r := by
  exact polarIntegral_kernelR_hasDerivAt_r isCompact_Icc
    (ae_restrict_mem measurableSet_Icc)
    (integrable_const (μ := volume.restrict (Set.Icc (0 : ℝ) (2 * π))) ((2 * π)⁻¹))
    continuous_cos.continuousOn continuous_sin.continuousOn
    (fun t _ ↦ (cos_sq_add_sin_sq t).le) (-(α + 2) / 2) hr 0

theorem continuousOn_normalizerFirst (α : ℝ) :
    ContinuousOn (normalizerFirst α) (Set.Ico 0 1) := by
  apply (continuousOn_polarIntegral_unit isCompact_Icc
    (ae_restrict_mem measurableSet_Icc)
    (integrable_const (μ := volume.restrict (Set.Icc (0 : ℝ) (2 * π))) ((2 * π)⁻¹))
    (continuousOn_polarKernelR_source continuous_cos.continuousOn
      continuous_sin.continuousOn (fun t _ ↦ (cos_sq_add_sin_sq t).le)
      (-(α + 2) / 2))).comp (continuous_id.prodMk continuous_const).continuousOn
  exact fun r hr ↦ ⟨hr, Set.mem_univ _⟩

theorem continuousOn_normalizerSecond (α : ℝ) :
    ContinuousOn (normalizerSecond α) (Set.Ico 0 1) := by
  apply (continuousOn_polarIntegral_unit isCompact_Icc
    (ae_restrict_mem measurableSet_Icc)
    (integrable_const (μ := volume.restrict (Set.Icc (0 : ℝ) (2 * π))) ((2 * π)⁻¹))
    (continuousOn_polarKernelRR_source continuous_cos.continuousOn
      continuous_sin.continuousOn (fun t _ ↦ (cos_sq_add_sin_sq t).le)
      (-(α + 2) / 2))).comp (continuous_id.prodMk continuous_const).continuousOn
  exact fun r hr ↦ ⟨hr, Set.mem_univ _⟩

theorem polarIntegral_boundary_angular_eq_zero (α : ℝ) {r : ℝ} (hr : r ^ 2 < 1)
    (θ : ℝ) :
    polarIntegral (polarKernelT (-(α + 2) / 2)) cos sin
      (volume.restrict (Set.Icc 0 (2 * π))) (fun _ ↦ (2 * π)⁻¹) r θ = 0 := by
  have hd := polarIntegral_kernel_hasDerivAt_t isCompact_Icc
    (ae_restrict_mem measurableSet_Icc)
    (integrable_const (μ := volume.restrict (Set.Icc (0 : ℝ) (2 * π))) ((2 * π)⁻¹))
    continuous_cos.continuousOn continuous_sin.continuousOn
    (fun t _ ↦ (cos_sq_add_sin_sq t).le) (-(α + 2) / 2) hr θ
  have heq : polarIntegral (polarKernel (-(α + 2) / 2)) cos sin
      (volume.restrict (Set.Icc 0 (2 * π))) (fun _ ↦ (2 * π)⁻¹) r =
        fun _ ↦ normalizer α r := by
    funext t
    exact polarIntegral_boundary_eq_normalizer α r t
  rw [heq] at hd
  exact hd.unique (hasDerivAt_const θ (normalizer α r))

theorem polarIntegral_boundary_angular_second_eq_zero (α : ℝ) {r : ℝ}
    (hr : r ^ 2 < 1) (θ : ℝ) :
    polarIntegral (polarKernelTT (-(α + 2) / 2)) cos sin
      (volume.restrict (Set.Icc 0 (2 * π))) (fun _ ↦ (2 * π)⁻¹) r θ = 0 := by
  have hd := polarIntegral_kernelT_hasDerivAt_t isCompact_Icc
    (ae_restrict_mem measurableSet_Icc)
    (integrable_const (μ := volume.restrict (Set.Icc (0 : ℝ) (2 * π))) ((2 * π)⁻¹))
    continuous_cos.continuousOn continuous_sin.continuousOn
    (fun t _ ↦ (cos_sq_add_sin_sq t).le) (-(α + 2) / 2) hr θ
  have heq : polarIntegral (polarKernelT (-(α + 2) / 2)) cos sin
      (volume.restrict (Set.Icc 0 (2 * π))) (fun _ ↦ (2 * π)⁻¹) r = fun _ ↦ 0 := by
    funext t
    exact polarIntegral_boundary_angular_eq_zero α hr t
  rw [heq] at hd
  exact hd.unique (hasDerivAt_const θ 0)

/-- The exact radial differential equation for the normalizing circular average. -/
theorem normalizer_ode (α : ℝ) {r : ℝ} (hr : r ^ 2 < 1) (hr0 : r ≠ 0) :
    normalizerSecond α r + normalizerFirst α r / r -
      (2 * (α + 2) * r / (1 - r ^ 2)) * normalizerFirst α r -
      ((α + 2) ^ 2 / (1 - r ^ 2)) * normalizer α r = 0 := by
  have heq := polarIntegral_operator_boundary isCompact_Icc
    (ae_restrict_mem measurableSet_Icc)
    (integrable_const (μ := volume.restrict (Set.Icc (0 : ℝ) (2 * π))) ((2 * π)⁻¹))
    continuous_cos.continuousOn continuous_sin.continuousOn
    (fun t _ ↦ (cos_sq_add_sin_sq t).le) (α + 2) hr hr0 0
    (fun t _ ↦ cos_sq_add_sin_sq t)
  simpa only [polarIntegral_boundary_eq_normalizer,
    polarIntegral_boundary_angular_second_eq_zero α hr, normalizerFirst, normalizerSecond,
    zero_div, add_zero] using heq

end BergmanWeakType.Weighted
