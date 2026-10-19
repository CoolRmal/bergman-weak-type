/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Measure
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Tactic.Module

/-! # Integration on the disk in polar coordinates -/

@[expose] public section

noncomputable section

open Set MeasureTheory Metric
open scoped Real

namespace BergmanWeakType

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integrable functions remain integrable after polar substitution with the Jacobian. -/
theorem integrable_polar {f : ℂ → E} (hf : Integrable f) :
    IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • f (Complex.polarCoord.symm p))
      polarCoord.target := by
  have hreal : Integrable (f ∘ Complex.measurableEquivRealProd.symm) :=
    Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_of_integrable hf
  have hsource := hreal.integrableOn (s := polarCoord.source)
  rw [← polarCoord.symm_image_target_eq_source] at hsource
  have hpolar := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    polarCoord.open_target.measurableSet
    (fun p _ ↦ (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    polarCoord.symm.injOn (f ∘ Complex.measurableEquivRealProd.symm)).mp hsource
  apply hpolar.congr
  filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
  simp only [det_fderivPolarCoordSymm, Function.comp_apply,
    Complex.measurableEquivRealProd_symm_polarCoord_symm_apply,
    abs_of_pos (show 0 < p.1 from hp.1)]

/-- Polar coordinates for an integrable function on the unit disk. -/
theorem integral_disk_eq_polar [CompleteSpace E] {f : ℂ → E} (hf : IntegrableOn f disk) :
    ∫ z in disk, f z = ∫ r in Ioo (0 : ℝ) 1, r •
      ∫ θ in Ioo (-π) π, f (Complex.polarCoord.symm (r, θ)) := by
  have hD : MeasurableSet disk := isOpen_ball.measurableSet
  have hfi : Integrable (disk.indicator f) := (integrable_indicator_iff hD).mpr hf
  have hp := integrable_polar hfi
  rw [← integral_indicator hD, ← Complex.integral_comp_polarCoord_symm]
  change (∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
    p.1 • disk.indicator f (Complex.polarCoord.symm p)) = _
  rw [Measure.volume_eq_prod, setIntegral_prod _ hp]
  have hset : Ioi (0 : ℝ) ∩ Iio 1 = Ioo 0 1 := by ext r; simp
  rw [← hset, ← setIntegral_indicator measurableSet_Iio]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  have hr0 : 0 < r := hr
  by_cases hr1 : r < 1
  · simp only [mem_Iio, hr1, indicator_of_mem]
    rw [← integral_smul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro θ _
    have hmem : Complex.polarCoord.symm (r, θ) ∈ disk := by
      simp only [disk, mem_ball, dist_zero_right, Complex.norm_polarCoord_symm,
        abs_of_pos hr0, hr1]
    simp only [indicator_of_mem hmem]
  · rw [indicator_of_notMem (show r ∉ Iio 1 from hr1)]
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun θ ↦ by
      have hnmem : Complex.polarCoord.symm (r, θ) ∉ disk := by
        simpa only [disk, mem_ball, dist_zero_right, Complex.norm_polarCoord_symm,
          abs_of_pos hr0] using hr1
      change r • disk.indicator f (Complex.polarCoord.symm (r, θ)) = 0
      rw [indicator_of_notMem hnmem, smul_zero]

theorem integral_polar_angle_eq_circleAverage [CompleteSpace E] (f : ℂ → E) (r : ℝ) :
    (∫ θ in Ioo (-π) π, f (Complex.polarCoord.symm (r, θ))) =
      (2 * π) • Real.circleAverage f 0 r := by
  rw [Real.circleAverage_eq_integral_add (-π),
    intervalIntegral.integral_comp_add_right (fun θ ↦ f (circleMap 0 r θ)) (-π), zero_add]
  have harg : 2 * π + -π = π := by ring
  rw [harg, smul_smul, mul_inv_cancel₀ (by positivity : 2 * π ≠ 0), one_smul,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
  congr 1
  funext θ
  congr 1
  simp [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I]

omit [NormedSpace ℝ E] in
theorem integrable_diskArea_iff {f : ℂ → E} :
    Integrable f diskArea ↔ IntegrableOn f disk := by
  simp only [diskArea, area, Measure.restrict_smul]
  exact integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top

/-- Disk integration is twice the radius-weighted integral of circular means. -/
theorem integral_diskArea_eq_circleAverage [CompleteSpace E] {f : ℂ → E}
    (hf : Integrable f diskArea) :
    ∫ z, f z ∂diskArea = ∫ r in Ioo (0 : ℝ) 1, (2 * r) • Real.circleAverage f 0 r := by
  rw [diskArea, area, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ π⁻¹),
    integral_disk_eq_polar (integrable_diskArea_iff.mp hf), ← integral_smul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r _
  dsimp only
  rw [integral_polar_angle_eq_circleAverage]
  simp only [smul_smul]
  congr 1
  field_simp

theorem image_sq_unit_interval : (fun r : ℝ ↦ r ^ 2) '' Ioo 0 1 = Ioo 0 1 := by
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨sq_pos_of_pos hr.1, by nlinarith [hr.1, hr.2]⟩
  · intro hy
    refine ⟨Real.sqrt y, ⟨Real.sqrt_pos.mpr hy.1, ?_⟩, Real.sq_sqrt hy.1.le⟩
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by simpa using hy.2)

theorem integral_unit_interval_sq [CompleteSpace E] (F : ℝ → E) :
    (∫ y in Ioo (0 : ℝ) 1, F y) = ∫ r in Ioo (0 : ℝ) 1, (2 * r) • F (r ^ 2) := by
  have hd (r : ℝ) : HasDerivWithinAt (fun r : ℝ ↦ r ^ 2) (2 * r) (Ioo 0 1) r := by
    simpa using (hasDerivAt_pow 2 r).hasDerivWithinAt
  have hi : InjOn (fun r : ℝ ↦ r ^ 2) (Ioo 0 1) := by
    intro r hr s hs hrs
    nlinarith [hr.1, hs.1]
  nth_rw 1 [← image_sq_unit_interval]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo (fun r _ ↦ hd r) hi]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  simp only [abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hr.1)]

/-- Squared radius is the uniform radial coordinate for normalized disk area. -/
theorem integral_diskArea_eq_circleAverage_sqrt [CompleteSpace E] {f : ℂ → E}
    (hf : Integrable f diskArea) :
    ∫ z, f z ∂diskArea = ∫ y in Ioo (0 : ℝ) 1, Real.circleAverage f 0 (Real.sqrt y) := by
  rw [integral_diskArea_eq_circleAverage hf,
    integral_unit_interval_sq (fun y ↦ Real.circleAverage f 0 (Real.sqrt y))]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  simp only [Real.sqrt_sq hr.1.le]

/-- The complementary squared radius is also uniform. -/
theorem integral_diskArea_eq_circleAverage_sqrt_one_sub [CompleteSpace E] {f : ℂ → E}
    (hf : Integrable f diskArea) :
    ∫ z, f z ∂diskArea =
      ∫ y in (0 : ℝ)..1, Real.circleAverage f 0 (Real.sqrt (1 - y)) := by
  rw [intervalIntegral.integral_comp_sub_left
    (fun y ↦ Real.circleAverage f 0 (Real.sqrt y)) 1]
  simp only [sub_zero, sub_self]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo]
  exact integral_diskArea_eq_circleAverage_sqrt hf

end BergmanWeakType
