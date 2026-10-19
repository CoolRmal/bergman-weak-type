/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.NormalizerEndpoint

/-! # Angular means of weighted kernel columns -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace BergmanWeakType

theorem circleAverage_mul_eq_norm (f : ℂ → ℝ) (a : ℂ) :
    Real.circleAverage (fun ζ ↦ f (a * ζ)) 0 1 =
      Real.circleAverage (fun ζ ↦ f ((‖a‖ : ℂ) * ζ)) 0 1 := by
  rw [Real.circleAverage_def,
    Real.circleAverage_eq_integral_add (f := fun ζ ↦ f ((‖a‖ : ℂ) * ζ)) (Complex.arg a)]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  congr 1
  nth_rw 1 [← Complex.norm_mul_exp_arg_mul_I a]
  simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.ofReal_add,
    add_mul, Complex.exp_add]
  ring

theorem circleAverage_star_eq (f : ℂ → ℝ) :
    Real.circleAverage (fun ζ ↦ f (star ζ)) 0 1 = Real.circleAverage f 0 1 := by
  rw [← Real.circleAverage_zero_one_congr_inv (f := f)]
  apply Real.circleAverage_congr_sphere
  intro ζ hζ
  have hζ' : ‖ζ‖ = 1 := by simpa using hζ
  dsimp only
  congr 1
  rw [Complex.inv_def, ← Complex.sq_norm, hζ']
  simp

theorem circleAverage_weightedKernel_norm (α : ℝ) (z : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    Real.circleAverage (fun w ↦ ‖weightedKernel α z w‖) 0 r = normalizer α (r * ‖z‖) := by
  rw [Real.circleAverage_eq_circleAverage_zero_one]
  simp only [norm_weightedKernel, add_zero, Complex.star_def, map_mul, Complex.conj_ofReal]
  have heq : (fun ζ : ℂ ↦ ‖1 - z * ((r : ℂ) * star ζ)‖ ^ (-(α + 2))) =
      (fun ζ : ℂ ↦ (fun ξ : ℂ ↦ ‖1 - (z * (r : ℂ)) * ξ‖ ^ (-(α + 2))) (star ζ)) := by
    funext ζ
    dsimp only
    rw [mul_assoc]
  change Real.circleAverage (fun ζ : ℂ ↦ ‖1 - z * ((r : ℂ) * star ζ)‖ ^ (-(α + 2))) 0 1 = _
  rw [heq, circleAverage_star_eq (fun ξ : ℂ ↦ ‖1 - (z * (r : ℂ)) * ξ‖ ^ (-(α + 2))),
    circleAverage_mul_eq_norm (fun u : ℂ ↦ ‖1 - u‖ ^ (-(α + 2)))]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
    mul_comm ‖z‖ r, normalizer]

theorem normalizer_mono (α : ℝ) {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r ≤ R) (hR : R < 1) : normalizer α r ≤ normalizer α R := by
  simp only [normalizer_eq_circleAverage_radius]
  exact circleAverage_boundaryPower_mono (-(α + 2)) hr hrR hR

end BergmanWeakType
