/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.KernelPotential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-! # Pure radial and angular derivatives of the weighted kernel -/

@[expose] public section

noncomputable section

open Real
open scoped Topology

namespace BergmanWeakType.Weighted

def radialComponent (a b θ : ℝ) : ℝ := a * cos θ + b * sin θ
def angularComponent (a b θ : ℝ) : ℝ := b * cos θ - a * sin θ

theorem component_norm_sq (a b θ : ℝ) :
    radialComponent a b θ ^ 2 + angularComponent a b θ ^ 2 = a ^ 2 + b ^ 2 := by
  calc
    _ = (a ^ 2 + b ^ 2) * (sin θ ^ 2 + cos θ ^ 2) := by
      unfold radialComponent angularComponent
      ring
    _ = _ := by rw [sin_sq_add_cos_sq, mul_one]

theorem radialComponent_hasDerivAt (a b θ : ℝ) :
    HasDerivAt (radialComponent a b) (angularComponent a b θ) θ := by
  convert ((hasDerivAt_cos θ).const_mul a).add ((hasDerivAt_sin θ).const_mul b) using 1
  · rfl
  · unfold angularComponent
    ring

theorem angularComponent_hasDerivAt (a b θ : ℝ) :
    HasDerivAt (angularComponent a b) (-radialComponent a b θ) θ := by
  convert ((hasDerivAt_cos θ).const_mul b).sub ((hasDerivAt_sin θ).const_mul a) using 1
  · rfl
  · unfold radialComponent
    ring

def polarDenominator (a b r θ : ℝ) : ℝ :=
  (a ^ 2 + b ^ 2) * r ^ 2 - 2 * r * radialComponent a b θ + 1

def polarKernel (q a b r θ : ℝ) : ℝ := polarDenominator a b r θ ^ q

theorem polarDenominator_eq_denominator (a b r θ : ℝ) :
    polarDenominator a b r θ =
      denominator (radialComponent a b θ) (angularComponent a b θ) r 0 := by
  rw [denominator, component_norm_sq]
  unfold polarDenominator
  ring

theorem polarKernel_eq_powerKernel (q a b r θ : ℝ) :
    polarKernel q a b r θ =
      powerKernel q (radialComponent a b θ) (angularComponent a b θ) r 0 := by
  rw [polarKernel, powerKernel, polarDenominator_eq_denominator]

def polarKernelR (q a b r θ : ℝ) : ℝ :=
  2 * q * ((a ^ 2 + b ^ 2) * r - radialComponent a b θ) * polarKernel (q - 1) a b r θ

def polarKernelRR (q a b r θ : ℝ) : ℝ :=
  2 * q * (a ^ 2 + b ^ 2) * polarKernel (q - 1) a b r θ +
    4 * q * (q - 1) * ((a ^ 2 + b ^ 2) * r - radialComponent a b θ) ^ 2 *
      polarKernel (q - 2) a b r θ

def polarKernelT (q a b r θ : ℝ) : ℝ :=
  -2 * q * r * angularComponent a b θ * polarKernel (q - 1) a b r θ

def polarKernelTT (q a b r θ : ℝ) : ℝ :=
  2 * q * r * radialComponent a b θ * polarKernel (q - 1) a b r θ +
    4 * q * (q - 1) * r ^ 2 * angularComponent a b θ ^ 2 * polarKernel (q - 2) a b r θ

theorem polarDenominator_pos {a b r : ℝ} (hr : r ^ 2 < 1)
    (hw : a ^ 2 + b ^ 2 ≤ 1) (θ : ℝ) : 0 < polarDenominator a b r θ := by
  rw [polarDenominator_eq_denominator]
  exact denominator_pos_coordinates (by simpa using hr) (by simpa [component_norm_sq] using hw)

theorem polarKernel_hasDerivAt_r (q a b r θ : ℝ) (hd : 0 < polarDenominator a b r θ) :
    HasDerivAt (fun u ↦ polarKernel q a b u θ) (polarKernelR q a b r θ) r := by
  have hd' : 0 < denominator (radialComponent a b θ) (angularComponent a b θ) r 0 := by
    simpa only [polarDenominator_eq_denominator] using hd
  simpa only [← polarKernel_eq_powerKernel, component_norm_sq, polarKernelR, powerKernel,
    ← polarDenominator_eq_denominator, polarKernel] using
      powerKernel_hasDerivAt_x q (radialComponent a b θ) (angularComponent a b θ) r 0 hd'

theorem polarKernelR_hasDerivAt_r (q a b r θ : ℝ) (hd : 0 < polarDenominator a b r θ) :
    HasDerivAt (fun u ↦ polarKernelR q a b u θ) (polarKernelRR q a b r θ) r := by
  have hd' : 0 < denominator (radialComponent a b θ) (angularComponent a b θ) r 0 := by
    simpa only [polarDenominator_eq_denominator] using hd
  simpa only [powerKernelX, powerKernelXX, component_norm_sq, ← polarKernel_eq_powerKernel,
    polarKernelR, polarKernelRR] using
      powerKernelX_hasDerivAt q (radialComponent a b θ) (angularComponent a b θ) r 0 hd'

theorem polarDenominator_hasDerivAt_t (a b r θ : ℝ) :
    HasDerivAt (polarDenominator a b r) (-2 * r * angularComponent a b θ) θ := by
  convert ((radialComponent_hasDerivAt a b θ).const_mul (-2 * r)).const_add
    ((a ^ 2 + b ^ 2) * r ^ 2 + 1) using 1
  · funext u
    unfold polarDenominator
    ring

theorem polarKernel_hasDerivAt_t (q a b r θ : ℝ) (hd : 0 < polarDenominator a b r θ) :
    HasDerivAt (polarKernel q a b r) (polarKernelT q a b r θ) θ := by
  convert (polarDenominator_hasDerivAt_t a b r θ).rpow_const (p := q) (Or.inl hd.ne') using 1
  · rfl
  · unfold polarKernelT polarKernel
    ring

theorem polarKernelT_hasDerivAt_t (q a b r θ : ℝ) (hd : 0 < polarDenominator a b r θ) :
    HasDerivAt (polarKernelT q a b r) (polarKernelTT q a b r θ) θ := by
  convert ((angularComponent_hasDerivAt a b θ).mul
    (polarKernel_hasDerivAt_t (q - 1) a b r θ hd)).const_mul (-2 * q * r) using 1
  · funext u
    unfold polarKernelT
    simp only [Pi.mul_apply]
    ring
  · unfold polarKernelT polarKernelTT
    rw [show q - 1 - 1 = q - 2 by ring]
    ring

theorem polarKernel_laplacian (q a b r θ : ℝ)
    (hd : 0 < polarDenominator a b r θ) (hr : r ≠ 0) :
    polarKernelRR q a b r θ + polarKernelR q a b r θ / r +
      polarKernelTT q a b r θ / r ^ 2 =
        4 * q ^ 2 * (a ^ 2 + b ^ 2) * polarKernel (q - 1) a b r θ := by
  have hp : polarKernel (q - 1) a b r θ =
      polarDenominator a b r θ * polarKernel (q - 2) a b r θ := by
    unfold polarKernel
    have he : polarDenominator a b r θ ^ (q - 2) =
        polarDenominator a b r θ ^ (q - 1) / polarDenominator a b r θ := by
      rw [show q - 2 = (q - 1) - 1 by ring]
      exact Real.rpow_sub_one hd.ne' _
    rw [he, mul_div_cancel₀ _ hd.ne']
  have hB : angularComponent a b θ ^ 2 = a ^ 2 + b ^ 2 - radialComponent a b θ ^ 2 := by
    linarith [component_norm_sq a b θ]
  unfold polarKernelRR polarKernelR polarKernelTT
  rw [hp, hB]
  unfold polarDenominator
  field_simp [hr]
  ring

/-- The weighted elliptic equation in polar coordinates, with no mixed derivatives. -/
theorem polarKernel_equation (k a b r θ : ℝ)
    (hd : 0 < polarDenominator a b r θ) (hr : r ≠ 0) (ht : 1 - r ^ 2 ≠ 0) :
    polarKernelRR (-k / 2) a b r θ + polarKernelR (-k / 2) a b r θ / r +
      polarKernelTT (-k / 2) a b r θ / r ^ 2 -
      (2 * k * r / (1 - r ^ 2)) * polarKernelR (-k / 2) a b r θ -
      (k ^ 2 / (1 - r ^ 2)) * polarKernel (-k / 2) a b r θ =
        -(k ^ 2 * (1 - (a ^ 2 + b ^ 2))) /
          ((1 - r ^ 2) * polarDenominator a b r θ) * polarKernel (-k / 2) a b r θ := by
  rw [polarKernel_laplacian (-k / 2) a b r θ hd hr]
  unfold polarKernelR polarKernel
  rw [Real.rpow_sub_one hd.ne']
  field_simp [hr, ht, hd.ne']
  unfold polarDenominator
  ring

theorem polarKernel_equation_nonpos (k a b r θ : ℝ)
    (hd : 0 < polarDenominator a b r θ) (hr : r ≠ 0) (ht : 0 < 1 - r ^ 2)
    (hw : a ^ 2 + b ^ 2 ≤ 1) :
    polarKernelRR (-k / 2) a b r θ + polarKernelR (-k / 2) a b r θ / r +
      polarKernelTT (-k / 2) a b r θ / r ^ 2 -
      (2 * k * r / (1 - r ^ 2)) * polarKernelR (-k / 2) a b r θ -
      (k ^ 2 / (1 - r ^ 2)) * polarKernel (-k / 2) a b r θ ≤ 0 := by
  rw [polarKernel_equation k a b r θ hd hr ht.ne']
  exact mul_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr
      (mul_nonneg (sq_nonneg k) (sub_nonneg.mpr hw))) (mul_nonneg ht.le hd.le))
    (Real.rpow_nonneg hd.le _)

theorem polarDenominator_eq_norm_sq (r θ : ℝ) (w : ℂ) :
    polarDenominator w.re w.im r θ = ‖1 - circleMap 0 r θ * star w‖ ^ 2 := by
  rw [← denominator_eq_norm_sq, circleMap_zero_re, circleMap_zero_im]
  have hs : (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 := by
    nlinarith [cos_sq_add_sin_sq θ, sq_nonneg r]
  unfold denominator polarDenominator radialComponent
  rw [hs]
  ring

theorem polarKernel_eq_norm_weightedKernel (α r θ : ℝ) (w : ℂ) :
    polarKernel (-(α + 2) / 2) w.re w.im r θ = ‖weightedKernel α (circleMap 0 r θ) w‖ := by
  rw [polarKernel, polarDenominator_eq_norm_sq, norm_weightedKernel,
    ← Real.rpow_natCast_mul (norm_nonneg _) 2]
  congr 1
  ring

end BergmanWeakType.Weighted
