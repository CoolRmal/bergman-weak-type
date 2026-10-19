/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.PolarCap
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Normalizing a polar supersolution by a positive radial solution -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real
open scoped Topology

namespace BergmanWeakType.Weighted

def quotientRadialFirst (F Fr : ℝ → ℝ → ℝ) (J Jr : ℝ → ℝ) (r θ : ℝ) : ℝ :=
  (Fr r θ * J r - F r θ * Jr r) / J r ^ 2

def quotientRadialSecond (F Fr Frr : ℝ → ℝ → ℝ) (J Jr Jrr : ℝ → ℝ)
    (r θ : ℝ) : ℝ :=
  Frr r θ / J r - F r θ * Jrr r / J r ^ 2 - 2 * Fr r θ * Jr r / J r ^ 2 +
    2 * F r θ * Jr r ^ 2 / J r ^ 3

theorem quotientRadialFirst_hasDerivAt {F Fr Frr : ℝ → ℝ → ℝ} {J Jr Jrr : ℝ → ℝ}
    {r θ : ℝ} (hF : HasDerivAt (fun u ↦ F u θ) (Fr r θ) r)
    (hFr : HasDerivAt (fun u ↦ Fr u θ) (Frr r θ) r)
    (hJ : HasDerivAt J (Jr r) r) (hJr : HasDerivAt Jr (Jrr r) r) (hJ0 : J r ≠ 0) :
    HasDerivAt (fun u ↦ quotientRadialFirst F Fr J Jr u θ)
      (quotientRadialSecond F Fr Frr J Jr Jrr r θ) r := by
  convert ((hFr.mul hJ).sub (hF.mul hJr)).div (hJ.pow 2) (pow_ne_zero 2 hJ0) using 1
  · rfl
  · unfold quotientRadialSecond
    dsimp only [Pi.pow_apply, Pi.sub_apply, Pi.mul_apply]
    field_simp [hJ0]
    ring

def quotientWeight (k : ℝ) (J : ℝ → ℝ) (r : ℝ) : ℝ :=
  (1 - r ^ 2) ^ k * J r ^ 2

def quotientWeightDeriv (k : ℝ) (J Jr : ℝ → ℝ) (r : ℝ) : ℝ :=
  quotientWeight k J r * (-(2 * k * r / (1 - r ^ 2)) + 2 * Jr r / J r)

theorem quotientWeight_hasDerivAt {k r : ℝ} {J Jr : ℝ → ℝ}
    (hr : r ^ 2 < 1) (hJ0 : J r ≠ 0) (hJ : HasDerivAt J (Jr r) r) :
    HasDerivAt (quotientWeight k J) (quotientWeightDeriv k J Jr r) r := by
  have ht : 0 < 1 - r ^ 2 := sub_pos.mpr hr
  have hd := (((hasDerivAt_id r).pow 2).const_sub 1).rpow_const (p := k) (Or.inl ht.ne')
  convert hd.mul (hJ.pow 2) using 1
  · rfl
  · unfold quotientWeightDeriv quotientWeight
    dsimp only [Pi.pow_apply, id_eq]
    rw [Real.rpow_sub_one ht.ne']
    field_simp [hJ0, ht.ne']
    ring

theorem antitoneOn_angularMean_min_quotient {F Fr Frr Ft Ftt : ℝ → ℝ → ℝ}
    {J Jr Jrr : ℝ → ℝ} (k c : ℝ)
    (hF : ContinuousOn (fun p : ℝ × ℝ ↦ F p.1 p.2) (Ico 0 1 ×ˢ univ))
    (hFr : ContinuousOn (fun p : ℝ × ℝ ↦ Fr p.1 p.2) (Ico 0 1 ×ˢ univ))
    (hFrr : ContinuousOn (fun p : ℝ × ℝ ↦ Frr p.1 p.2) (Ico 0 1 ×ˢ univ))
    (hFt : ContinuousOn (fun p : ℝ × ℝ ↦ Ft p.1 p.2) (Ico 0 1 ×ˢ univ))
    (hFtt : ContinuousOn (fun p : ℝ × ℝ ↦ Ftt p.1 p.2) (Ico 0 1 ×ˢ univ))
    (hFd : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ θ, HasDerivAt (fun u ↦ F u θ) (Fr r θ) r)
    (hFrd : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ θ, HasDerivAt (fun u ↦ Fr u θ) (Frr r θ) r)
    (hFdt : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ θ, HasDerivAt (F r) (Ft r θ) θ)
    (hFtd : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ θ, HasDerivAt (Ft r) (Ftt r θ) θ)
    (hperiodF : ∀ r ∈ Ioo (0 : ℝ) 1, F r (2 * π) = F r 0)
    (hperiodFt : ∀ r ∈ Ioo (0 : ℝ) 1, Ft r (2 * π) = Ft r 0)
    (hJ : ContinuousOn J (Ico 0 1)) (hJr : ContinuousOn Jr (Ico 0 1))
    (hJrr : ContinuousOn Jrr (Ico 0 1))
    (hJd : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt J (Jr r) r)
    (hJrd : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt Jr (Jrr r) r)
    (hJpos : ∀ r ∈ Ico (0 : ℝ) 1, 0 < J r)
    (hJode : ∀ r ∈ Ioo (0 : ℝ) 1,
      Jrr r + (1 / r - 2 * k * r / (1 - r ^ 2)) * Jr r -
        (k ^ 2 / (1 - r ^ 2)) * J r = 0)
    (hFode : ∀ r ∈ Ioo (0 : ℝ) 1, ∀ θ,
      Frr r θ + (1 / r - 2 * k * r / (1 - r ^ 2)) * Fr r θ + Ftt r θ / r ^ 2 -
        (k ^ 2 / (1 - r ^ 2)) * F r θ ≤ 0) :
    AntitoneOn (angularMean (fun r θ ↦ min (F r θ / J r) c)) (Ico 0 1) := by
  have hJ' : ContinuousOn (fun p : ℝ × ℝ ↦ J p.1) (Ico 0 1 ×ˢ univ) :=
    hJ.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  have hJr' : ContinuousOn (fun p : ℝ × ℝ ↦ Jr p.1) (Ico 0 1 ×ˢ univ) :=
    hJr.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  have hJrr' : ContinuousOn (fun p : ℝ × ℝ ↦ Jrr p.1) (Ico 0 1 ×ˢ univ) :=
    hJrr.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
  have hn : ∀ p ∈ Ico (0 : ℝ) 1 ×ˢ (univ : Set ℝ), J p.1 ≠ 0 :=
    fun p hp ↦ (hJpos p.1 hp.1).ne'
  have hpow (n : ℕ) : ∀ p ∈ Ico (0 : ℝ) 1 ×ˢ (univ : Set ℝ), J p.1 ^ n ≠ 0 :=
    fun p hp ↦ pow_ne_zero n (hn p hp)
  have hbase : ContinuousOn (fun r : ℝ ↦ (1 - r ^ 2) ^ k) (Ico 0 1) := by
    apply (continuousOn_const.sub (continuousOn_id.pow 2)).rpow_const
    intro r hr
    left
    apply (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one r).mpr _)).ne'
    exact abs_lt.mpr ⟨by linarith [hr.1], hr.2⟩
  apply antitoneOn_angularMean_min_of_polar_flux c
    (Fr := quotientRadialFirst F Fr J Jr) (Frr := quotientRadialSecond F Fr Frr J Jr Jrr)
    (Ft := fun r θ ↦ Ft r θ / J r) (Ftt := fun r θ ↦ Ftt r θ / J r)
    (w := quotientWeight k J) (w' := quotientWeightDeriv k J Jr)
  · exact hF.div hJ' hn
  · exact ((hFr.mul hJ').sub (hF.mul hJr')).div (hJ'.pow 2) (hpow 2)
  · exact (((hFrr.div hJ' hn).sub ((hF.mul hJrr').div (hJ'.pow 2) (hpow 2))).sub
      (((hFr.const_mul 2).mul hJr').div (hJ'.pow 2) (hpow 2))).add
      (((hF.const_mul 2).mul (hJr'.pow 2)).div (hJ'.pow 3) (hpow 3))
  · exact hFt.div hJ' hn
  · exact hFtt.div hJ' hn
  · intro r hr θ
    exact (hFd r hr θ).div (hJd r hr) (hJpos r ⟨hr.1.le, hr.2⟩).ne'
  · intro r hr θ
    exact quotientRadialFirst_hasDerivAt (hFd r hr θ) (hFrd r hr θ) (hJd r hr)
      (hJrd r hr) (hJpos r ⟨hr.1.le, hr.2⟩).ne'
  · intro r hr θ
    exact (hFdt r hr θ).div_const (J r)
  · intro r hr θ
    exact (hFtd r hr θ).div_const (J r)
  · intro r hr
    rw [hperiodF r hr]
  · intro r hr
    rw [hperiodFt r hr]
  · exact hbase.mul (hJ.pow 2)
  · intro r hr
    exact quotientWeight_hasDerivAt
      ((sq_lt_one_iff_abs_lt_one r).mpr (abs_lt.mpr ⟨by linarith [hr.1], hr.2⟩))
      (hJpos r ⟨hr.1.le, hr.2⟩).ne' (hJd r hr)
  · intro r hr
    apply mul_pos (Real.rpow_pos_of_pos _ _) (sq_pos_of_pos (hJpos r ⟨hr.1.le, hr.2⟩))
    exact sub_pos.mpr ((sq_lt_one_iff_abs_lt_one r).mpr
      (abs_lt.mpr ⟨by linarith [hr.1], hr.2⟩))
  · intro r hr θ
    have hj := hJpos r ⟨hr.1.le, hr.2⟩
    have ht : 0 < 1 - r ^ 2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one r).mpr
      (abs_lt.mpr ⟨by linarith [hr.1], hr.2⟩))
    have h := quotient_polar_operator_nonpos hj hr.1.ne'
      (a := 1 / r - 2 * k * r / (1 - r ^ 2)) (b := -(k ^ 2 / (1 - r ^ 2)))
      (by simpa only [neg_mul, ← sub_eq_add_neg] using hJode r hr)
      (by simpa only [neg_mul, ← sub_eq_add_neg] using hFode r hr θ)
    have hm := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hr.1.le (mul_nonneg (Real.rpow_nonneg ht.le k) (sq_nonneg (J r)))) h
    convert hm using 1
    unfold quotientWeightDeriv quotientWeight quotientRadialFirst quotientRadialSecond
    field_simp [hj.ne', hr.1.ne', ht.ne']
    ring

end BergmanWeakType.Weighted
