/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.BetaIntegral

/-! # The real change of variables underlying boundary-circle Möbius invariance -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace BergmanWeakType

def circleDenominator (r x : ℝ) : ℝ := 1 + r ^ 2 - 2 * r * x

def circleMobius (r x : ℝ) : ℝ :=
  (2 * r - (1 + r ^ 2) * x) / circleDenominator r x

theorem circleDenominator_pos {r x : ℝ} (hr : |r| < 1) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    0 < circleDenominator r x := by
  have hr₁ : -1 < r := (abs_lt.mp hr).1
  have hr₂ : r < 1 := (abs_lt.mp hr).2
  unfold circleDenominator
  by_cases h : 0 ≤ r
  · nlinarith [mul_nonneg h (sub_nonneg.mpr hx.2), sq_pos_of_pos (sub_pos.mpr hr₂)]
  · have hn : r < 0 := lt_of_not_ge h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hn.le (by linarith [hx.1] : 0 ≤ x + 1),
      sq_pos_of_pos (by linarith : 0 < 1 + r)]

theorem circleMobius_one {r : ℝ} (hr : |r| < 1) : circleMobius r 1 = -1 := by
  unfold circleMobius
  apply (div_eq_iff (circleDenominator_pos hr ⟨by norm_num, le_rfl⟩).ne').mpr
  unfold circleDenominator
  ring

theorem circleMobius_neg_one {r : ℝ} (hr : |r| < 1) : circleMobius r (-1) = 1 := by
  unfold circleMobius
  apply (div_eq_iff (circleDenominator_pos hr ⟨le_rfl, by norm_num⟩).ne').mpr
  unfold circleDenominator
  ring

theorem circleMobius_mem_Ioo {r x : ℝ} (hr : |r| < 1) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    circleMobius r x ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hd := circleDenominator_pos hr ⟨hx.1.le, hx.2.le⟩
  have hr₁ : -1 < r := (abs_lt.mp hr).1
  have hr₂ : r < 1 := (abs_lt.mp hr).2
  unfold circleMobius
  constructor
  · rw [lt_div_iff₀ hd]
    have h := mul_pos (sq_pos_of_pos (by linarith : 0 < 1 + r))
      (sub_pos.mpr hx.2)
    unfold circleDenominator
    nlinarith
  · rw [div_lt_iff₀ hd]
    have h := mul_pos (sq_pos_of_pos (sub_pos.mpr hr₂)) (by linarith [hx.1] : 0 < 1 + x)
    unfold circleDenominator
    nlinarith

theorem continuousOn_circleMobius {r : ℝ} (hr : |r| < 1) :
    ContinuousOn (circleMobius r) (Set.Icc (-1 : ℝ) 1) := by
  unfold circleMobius
  apply ContinuousOn.div (by fun_prop) (by unfold circleDenominator; fun_prop)
  exact fun x hx ↦ (circleDenominator_pos hr hx).ne'

theorem hasDerivAt_circleMobius {r x : ℝ} (hr : |r| < 1)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    HasDerivAt (circleMobius r) (-(1 - r ^ 2) ^ 2 / circleDenominator r x ^ 2) x := by
  have hn := ((hasDerivAt_id x).const_mul (1 + r ^ 2)).const_sub (2 * r)
  have hd := ((hasDerivAt_id x).const_mul (2 * r)).const_sub (1 + r ^ 2)
  convert! hn.div hd (circleDenominator_pos hr hx).ne' using 1
  unfold circleDenominator
  simp only [id_eq]
  ring

theorem one_sub_circleMobius_sq {r x : ℝ} (hr : |r| < 1)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    1 - circleMobius r x ^ 2 =
      (1 - r ^ 2) ^ 2 * (1 - x ^ 2) / circleDenominator r x ^ 2 := by
  have hd := (circleDenominator_pos hr hx).ne'
  unfold circleMobius
  field_simp
  unfold circleDenominator
  ring

theorem sqrt_one_sub_circleMobius_sq {r x : ℝ} (hr : |r| < 1)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Real.sqrt (1 - circleMobius r x ^ 2) =
      (1 - r ^ 2) * Real.sqrt (1 - x ^ 2) / circleDenominator r x := by
  have hr₂ : 0 < 1 - r ^ 2 := by
    nlinarith [mul_pos (by linarith [(abs_lt.mp hr).1] : 0 < 1 + r)
      (sub_pos.mpr (abs_lt.mp hr).2)]
  have hx₂ : 0 ≤ 1 - x ^ 2 := by
    nlinarith [mul_nonneg (by linarith [hx.1] : 0 ≤ 1 + x) (sub_nonneg.mpr hx.2)]
  have hd := circleDenominator_pos hr hx
  rw [one_sub_circleMobius_sq hr hx, Real.sqrt_div (by positivity),
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    abs_of_pos hr₂, abs_of_pos hd]

theorem integral_circleMobius_weight (F : ℝ → ℝ) {r : ℝ} (hr : |r| < 1) :
    (∫ x in (-1 : ℝ)..1,
      F (circleMobius r x) * (1 - r ^ 2) /
        (circleDenominator r x * Real.sqrt (1 - x ^ 2))) =
      ∫ x in (-1 : ℝ)..1, F x / Real.sqrt (1 - x ^ 2) := by
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := (-1 : ℝ)) (b := 1) (f := circleMobius r)
    (f' := fun x ↦ -(1 - r ^ 2) ^ 2 / circleDenominator r x ^ 2)
    (g := fun x ↦ F x / Real.sqrt (1 - x ^ 2))
    (by simpa only [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using
      continuousOn_circleMobius hr)
    (fun x hx ↦ hasDerivAt_circleMobius hr (by
      norm_num at hx
      exact ⟨hx.1.le, hx.2.le⟩))
    (fun x _ ↦ div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (sq_nonneg _))
  rw [circleMobius_neg_one hr, circleMobius_one hr,
    intervalIntegral.integral_symm (f := fun x ↦ F x / Real.sqrt (1 - x ^ 2))] at hsub
  have heq : (∫ x in (-1 : ℝ)..1,
      ((fun x ↦ F x / Real.sqrt (1 - x ^ 2)) ∘ circleMobius r) x *
        (-(1 - r ^ 2) ^ 2 / circleDenominator r x ^ 2)) =
      -(∫ x in (-1 : ℝ)..1, F (circleMobius r x) * (1 - r ^ 2) /
        (circleDenominator r x * Real.sqrt (1 - x ^ 2))) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    dsimp only [Function.comp_def]
    have hd := (circleDenominator_pos hr ⟨hx.1.le, hx.2.le⟩).ne'
    have hr₂ : 1 - r ^ 2 ≠ 0 := by
      apply ne_of_gt
      nlinarith [mul_pos (by linarith [(abs_lt.mp hr).1] : 0 < 1 + r)
        (sub_pos.mpr (abs_lt.mp hr).2)]
    have hs : Real.sqrt (1 - x ^ 2) ≠ 0 := by
      apply (Real.sqrt_pos.mpr _).ne'
      nlinarith [mul_pos (by linarith [hx.1] : 0 < 1 + x) (sub_pos.mpr hx.2)]
    rw [sqrt_one_sub_circleMobius_sq hr ⟨hx.1.le, hx.2.le⟩]
    field_simp
  rw [heq] at hsub
  exact neg_injective hsub

theorem circleDenominator_circleMobius {r x : ℝ} (hr : |r| < 1)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    circleDenominator r (circleMobius r x) =
      (1 - r ^ 2) ^ 2 / circleDenominator r x := by
  have hd := (circleDenominator_pos hr hx).ne'
  change 1 + r ^ 2 - 2 * r *
    ((2 * r - (1 + r ^ 2) * x) / circleDenominator r x) = _
  apply (eq_div_iff hd).mpr
  rw [sub_mul, mul_assoc (2 * r), div_mul_cancel₀ _ hd]
  unfold circleDenominator
  ring

theorem mobius_rpow_factor (α : ℝ) {δ D : ℝ} (hδ : 0 < δ) (hD : 0 < D) :
    δ ^ (α + 1) * ((δ ^ 2 / D) ^ (-(α + 2) / 2) * δ / D) = D ^ (α / 2) := by
  have hδexp : δ ^ (α + 1) * δ = δ ^ (α + 2) := by
    calc
      _ = δ ^ (α + 1) * δ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = δ ^ ((α + 1) + 1) := (Real.rpow_add hδ _ _).symm
      _ = _ := by congr 1; ring
  have hDexp : D ^ ((α + 2) / 2) = D ^ (α / 2) * D := by
    rw [show (α + 2) / 2 = α / 2 + 1 by ring, Real.rpow_add hD, Real.rpow_one]
  have hpow : (δ ^ 2 / D) ^ (-(α + 2) / 2) =
      (δ ^ (α + 2))⁻¹ * D ^ ((α + 2) / 2) := by
    rw [Real.div_rpow (sq_nonneg δ) hD.le, ← Real.rpow_natCast δ 2,
      ← Real.rpow_mul hδ.le]
    norm_num only [Nat.cast_ofNat]
    rw [show 2 * (-(α + 2) / 2) = -(α + 2) by ring,
      show -(α + 2) / 2 = -((α + 2) / 2) by ring,
      Real.rpow_neg hδ.le, Real.rpow_neg hD.le, div_inv_eq_mul]
  rw [hpow, hDexp]
  calc
    _ = (δ ^ (α + 1) * δ) * (δ ^ (α + 2))⁻¹ * D ^ (α / 2) * (D / D) := by ring
    _ = _ := by rw [hδexp, mul_inv_cancel₀ (Real.rpow_pos_of_pos hδ _).ne',
      div_self hD.ne', one_mul, mul_one]

theorem integral_circleDenominator_transform (α : ℝ) {r : ℝ} (hr : |r| < 1) :
    (1 - r ^ 2) ^ (α + 1) *
      (∫ x in (-1 : ℝ)..1,
        circleDenominator r x ^ (-(α + 2) / 2) / Real.sqrt (1 - x ^ 2)) =
      ∫ x in (-1 : ℝ)..1,
        circleDenominator r x ^ (α / 2) / Real.sqrt (1 - x ^ 2) := by
  rw [← integral_circleMobius_weight
    (fun x ↦ circleDenominator r x ^ (-(α + 2) / 2)) hr,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro x hx
  dsimp only
  have hδ : 0 < 1 - r ^ 2 := by
    nlinarith [mul_pos (by linarith [(abs_lt.mp hr).1] : 0 < 1 + r)
      (sub_pos.mpr (abs_lt.mp hr).2)]
  rw [circleDenominator_circleMobius hr ⟨hx.1.le, hx.2.le⟩]
  have heq := mobius_rpow_factor α hδ (circleDenominator_pos hr ⟨hx.1.le, hx.2.le⟩)
  calc
    _ = ((1 - r ^ 2) ^ (α + 1) *
        (((1 - r ^ 2) ^ 2 / circleDenominator r x) ^ (-(α + 2) / 2) *
          (1 - r ^ 2) / circleDenominator r x)) / Real.sqrt (1 - x ^ 2) := by ring
    _ = _ := by rw [heq]

theorem integral_cos_arcsine (F : ℝ → ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi, F (Real.cos θ)) =
      ∫ x in (-1 : ℝ)..1, F x / Real.sqrt (1 - x ^ 2) := by
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := (0 : ℝ)) (b := Real.pi) (f := Real.cos) (f' := fun θ ↦ -Real.sin θ)
    (g := fun x ↦ F x / Real.sqrt (1 - x ^ 2)) Real.continuous_cos.continuousOn
    (fun θ _ ↦ Real.hasDerivAt_cos θ)
    (fun θ hθ ↦ by
      rw [min_eq_left Real.pi_pos.le, max_eq_right Real.pi_pos.le] at hθ
      exact neg_nonpos.mpr (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2.le))
  rw [Real.cos_zero, Real.cos_pi,
    intervalIntegral.integral_symm (f := fun x ↦ F x / Real.sqrt (1 - x ^ 2))] at hsub
  have heq : (∫ θ in (0 : ℝ)..Real.pi,
      ((fun x ↦ F x / Real.sqrt (1 - x ^ 2)) ∘ Real.cos) θ * -Real.sin θ) =
      -(∫ θ in (0 : ℝ)..Real.pi, F (Real.cos θ)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le
    intro θ hθ
    dsimp only [Function.comp_def]
    have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    rw [show 1 - Real.cos θ ^ 2 = Real.sin θ ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq θ], Real.sqrt_sq_eq_abs, abs_of_pos hs]
    field_simp
  rw [heq] at hsub
  exact neg_injective hsub

end BergmanWeakType
