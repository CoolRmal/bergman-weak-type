/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Real beta integrals for the weighted boundary constants -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace BergmanWeakType

theorem integral_real_beta {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in (0 : ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1)) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  calc
    _ = Complex.betaIntegral (a : ℂ) (b : ℂ) := by
      unfold Complex.betaIntegral
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro x hx
      simp only [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
        Complex.ofReal_cpow (sub_nonneg.mpr hx.2.le), Complex.ofReal_sub, Complex.ofReal_one]
    _ = _ := by
      rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using ha) (by simpa using hb)]
      rw [← Complex.ofReal_add]
      simp only [Complex.Gamma_ofReal, Complex.ofReal_div, Complex.ofReal_mul]

theorem beta_sin_substitution_integrand (α : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x ^ 2) ^ ((α - 1) / 2) * (y ^ 2) ^ (-(1 / 2 : ℝ)) * (2 * x * y) = 2 * x ^ α := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le,
    ← Real.rpow_natCast y 2, ← Real.rpow_mul hy.le]
  norm_num only [Nat.cast_ofNat]
  have ha : (2 : ℝ) * ((α - 1) / 2) = α - 1 := by ring
  rw [ha, Real.rpow_neg_one]
  have hc : x ^ (α - 1) * x = x ^ α := by
    calc
      _ = x ^ (α - 1) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((α - 1) + 1) := (Real.rpow_add hx _ _).symm
      _ = x ^ α := by congr 1; ring
  calc
    _ = 2 * (x ^ (α - 1) * x) * (y⁻¹ * y) := by ring
    _ = _ := by rw [hc, inv_mul_cancel₀ hy.ne', mul_one]

theorem integral_sin_rpow_half {α : ℝ} (hα : -1 < α) :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ α) =
      Real.sqrt Real.pi * Real.Gamma ((α + 1) / 2) /
        (2 * Real.Gamma (1 + α / 2)) := by
  have hp : 0 ≤ Real.pi / 2 := by positivity
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := Real.pi / 2)
    (f := fun x ↦ Real.sin x ^ 2) (f' := fun x ↦ 2 * Real.sin x * Real.cos x)
    (g := fun t ↦ t ^ ((α - 1) / 2) * (1 - t) ^ (-(1 / 2 : ℝ)))
    (by fun_prop)
    (fun x _ ↦ by simpa [Pi.pow_apply] using! (Real.hasDerivAt_sin x).pow 2)
    (fun x hx ↦ by
      rw [min_eq_left hp, max_eq_right hp] at hx
      exact mul_nonneg (mul_nonneg (by norm_num)
        (Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le (by linarith [hx.2])))
        (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hx.1], hx.2.le⟩))
  simp only [Real.sin_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Real.sin_pi_div_two, one_pow] at hsub
  have heq : (∫ x in (0 : ℝ)..Real.pi / 2,
      ((Real.sin x ^ 2) ^ ((α - 1) / 2) *
        (1 - Real.sin x ^ 2) ^ (-(1 / 2 : ℝ))) *
          (2 * Real.sin x * Real.cos x)) =
        2 * (∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ α) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le hp
    intro x hx
    have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [hx.2])
    have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1], hx.2⟩
    dsimp only
    rw [show 1 - Real.sin x ^ 2 = Real.cos x ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq x]]
    exact beta_sin_substitution_integrand α hs hc
  dsimp only [Function.comp_def] at hsub
  rw [heq] at hsub
  have hbeta := integral_real_beta
    (a := (α + 1) / 2) (b := (1 / 2 : ℝ)) (by linarith) (by norm_num)
  have harg : (α + 1) / 2 - 1 = (α - 1) / 2 := by ring
  have hsum : (α + 1) / 2 + 1 / 2 = 1 + α / 2 := by ring
  rw [harg, hsum, Real.Gamma_one_half_eq] at hbeta
  norm_num only [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num] at hbeta
  rw [hbeta] at hsub
  calc
    _ = (Real.Gamma ((α + 1) / 2) * Real.sqrt Real.pi /
        Real.Gamma (1 + α / 2)) / 2 := by linarith
    _ = _ := by ring

theorem intervalIntegrable_sin_rpow_half {α : ℝ} (hα : -1 < α) :
    IntervalIntegrable (fun x ↦ Real.sin x ^ α) volume 0 (Real.pi / 2) := by
  apply intervalIntegral.intervalIntegrable_of_integral_ne_zero
  rw [integral_sin_rpow_half hα]
  apply ne_of_gt
  apply div_pos
  · exact mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (Real.Gamma_pos_of_pos (by linarith))
  · exact mul_pos (by norm_num) (Real.Gamma_pos_of_pos (by linarith))

theorem intervalIntegrable_sin_rpow {α : ℝ} (hα : -1 < α) :
    IntervalIntegrable (fun x ↦ Real.sin x ^ α) volume 0 Real.pi := by
  have hh := intervalIntegrable_sin_rpow_half hα
  apply hh.trans
  have hr := hh.comp_sub_left Real.pi
  simpa only [Real.sin_pi_sub, sub_zero, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring]
    using hr.symm

theorem integral_sin_rpow {α : ℝ} (hα : -1 < α) :
    (∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ α) =
      Real.sqrt Real.pi * Real.Gamma ((α + 1) / 2) / Real.Gamma (1 + α / 2) := by
  have hh := intervalIntegrable_sin_rpow_half hα
  have hr : IntervalIntegrable (fun x ↦ Real.sin x ^ α) volume (Real.pi / 2) Real.pi := by
    simpa only [Real.sin_pi_sub, sub_zero, show Real.pi - Real.pi / 2 = Real.pi / 2 by ring]
      using (hh.comp_sub_left Real.pi).symm
  have heq : (∫ x in Real.pi / 2..Real.pi, Real.sin x ^ α) =
      ∫ x in (0 : ℝ)..Real.pi / 2, Real.sin x ^ α := by
    conv_lhs => arg 1; intro x; rw [← Real.sin_pi_sub x]
    rw [intervalIntegral.integral_comp_sub_left (fun x ↦ Real.sin x ^ α), sub_self,
      show Real.pi - Real.pi / 2 = Real.pi / 2 by ring]
  rw [← intervalIntegral.integral_add_adjacent_intervals hh hr, heq,
    integral_sin_rpow_half hα]
  ring

end BergmanWeakType
