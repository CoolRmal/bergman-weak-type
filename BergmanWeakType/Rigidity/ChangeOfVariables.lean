/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Definitions
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity

public section

open Set MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

/-- A complex derivative scales real area by its squared norm. -/
theorem det_complex_derivative (c : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]

/-- Change of variables for nonnegative integrals under a holomorphic injection. -/
theorem lintegral_image_eq_lintegral_norm_deriv_sq {U : Set ℂ} {φ : ℂ → ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U)
    (g : ℂ → ℝ≥0∞) :
    ∫⁻ z in φ '' U, g z = ∫⁻ w in U, ENNReal.ofReal (‖deriv φ w‖ ^ 2) * g (φ w) := by
  simpa only [det_complex_derivative, abs_sq] using
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hU.measurableSet
      (fun w hw ↦ ((hφ.differentiableAt (hU.mem_nhds hw)).hasDerivAt.hasFDerivAt
        |>.restrictScalars ℝ).hasFDerivWithinAt) hinj g

/-- Change of variables for complex integrals under a holomorphic injection. -/
theorem integral_image_eq_integral_norm_deriv_sq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set ℂ} {φ : ℂ → ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) (g : ℂ → E) :
    ∫ z in φ '' U, g z = ∫ w in U, (‖deriv φ w‖ ^ 2 : ℝ) • g (φ w) := by
  simpa only [det_complex_derivative, abs_sq] using
    integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet
      (fun w hw ↦ ((hφ.differentiableAt (hU.mem_nhds hw)).hasDerivAt.hasFDerivAt
        |>.restrictScalars ℝ).hasFDerivWithinAt) hinj g

/-- Integrability is preserved by the full complex area Jacobian. -/
theorem integrableOn_image_iff_norm_deriv_sq {U : Set ℂ} {φ : ℂ → ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) (g : ℂ → ℂ) :
    IntegrableOn g (φ '' U) ↔ IntegrableOn (fun w ↦ (‖deriv φ w‖ ^ 2 : ℝ) • g (φ w)) U := by
  simpa only [IntegrableOn, det_complex_derivative, abs_sq] using
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hU.measurableSet
      (fun w hw ↦ ((hφ.differentiableAt (hU.mem_nhds hw)).hasDerivAt.hasFDerivAt
        |>.restrictScalars ℝ).hasFDerivWithinAt) hinj g

/-- The normalized-area version of holomorphic change of variables for nonnegative integrals. -/
theorem area_lintegral_image_eq {U : Set ℂ} {φ : ℂ → ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U)
    (g : ℂ → ℝ≥0∞) :
    ∫⁻ z in φ '' U, g z ∂area =
      ∫⁻ w in U, ENNReal.ofReal (‖deriv φ w‖ ^ 2) * g (φ w) ∂area := by
  simp only [area, Measure.restrict_smul, lintegral_smul_measure]
  rw [lintegral_image_eq_lintegral_norm_deriv_sq hU hφ hinj]

/-- The normalized-area version of holomorphic change of variables for complex integrals. -/
theorem area_integral_image_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set ℂ} {φ : ℂ → ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) (g : ℂ → E) :
    ∫ z in φ '' U, g z ∂area = ∫ w in U, (‖deriv φ w‖ ^ 2 : ℝ) • g (φ w) ∂area := by
  simp only [area, Measure.restrict_smul, integral_smul_measure]
  rw [integral_image_eq_integral_norm_deriv_sq hU hφ hinj]

/-- Normalizing area preserves the integrability equivalence in holomorphic substitution. -/
theorem area_integrableOn_image_iff_norm_deriv_sq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set ℂ} {φ : ℂ → ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) (g : ℂ → E) :
    IntegrableOn g (φ '' U) area ↔
      IntegrableOn (fun w ↦ (‖deriv φ w‖ ^ 2 : ℝ) • g (φ w)) U area := by
  simp only [IntegrableOn, area, Measure.restrict_smul]
  rw [integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top,
    integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top]
  simpa only [IntegrableOn, det_complex_derivative, abs_sq] using
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hU.measurableSet
      (fun w hw ↦ ((hφ.differentiableAt (hU.mem_nhds hw)).hasDerivAt.hasFDerivAt
        |>.restrictScalars ℝ).hasFDerivWithinAt) hinj g

end BergmanWeakType
