/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.KernelIntegrability
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp

/-! # The real differential equation for the positive weighted kernel

The calculations use Cartesian coordinates and ordinary one-variable derivatives in each
coordinate. The resulting second-order operator is the Laplacian with radial drift from the
source proof.
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace BergmanWeakType.Weighted

/-- The squared denominator in Cartesian coordinates. -/
def denominator (a b x y : ℝ) : ℝ :=
  (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) - 2 * (a * x + b * y) + 1

/-- A real power of the squared denominator. -/
def powerKernel (q a b x y : ℝ) : ℝ := denominator a b x y ^ q

theorem denominator_swap (a b x y : ℝ) : denominator a b x y = denominator b a y x := by
  unfold denominator
  ring

theorem powerKernel_swap (q a b x y : ℝ) :
    powerKernel q a b x y = powerKernel q b a y x := by
  rw [powerKernel, powerKernel, denominator_swap]

theorem denominator_hasDerivAt_x (a b x y : ℝ) :
    HasDerivAt (fun u ↦ denominator a b u y)
      (2 * ((a ^ 2 + b ^ 2) * x - a)) x := by
  convert (((((hasDerivAt_id x).pow 2).add_const (y ^ 2)).const_mul (a ^ 2 + b ^ 2)).sub
    ((((hasDerivAt_id x).const_mul a).add_const (b * y)).const_mul 2)).add_const 1 using 1
  · rfl
  · norm_num
    ring

theorem powerKernel_hasDerivAt_x (q a b x y : ℝ) (hd : 0 < denominator a b x y) :
    HasDerivAt (fun u ↦ powerKernel q a b u y)
      (2 * q * ((a ^ 2 + b ^ 2) * x - a) * denominator a b x y ^ (q - 1)) x := by
  convert (denominator_hasDerivAt_x a b x y).rpow_const (p := q) (Or.inl hd.ne') using 1
  · rfl
  · ring

theorem powerKernel_deriv_x (q a b x y : ℝ) (hd : 0 < denominator a b x y) :
    deriv (fun u ↦ powerKernel q a b u y) x =
      2 * q * ((a ^ 2 + b ^ 2) * x - a) * denominator a b x y ^ (q - 1) :=
  (powerKernel_hasDerivAt_x q a b x y hd).deriv

theorem powerKernel_hasDerivAt_y (q a b x y : ℝ) (hd : 0 < denominator a b x y) :
    HasDerivAt (fun u ↦ powerKernel q a b x u)
      (2 * q * ((a ^ 2 + b ^ 2) * y - b) * denominator a b x y ^ (q - 1)) y := by
  have h := powerKernel_hasDerivAt_x q b a y x (by simpa [denominator_swap] using hd)
  have hfun : (fun u ↦ powerKernel q a b x u) = (fun u ↦ powerKernel q b a u x) :=
    funext fun u ↦ powerKernel_swap q a b x u
  rw [hfun]
  simpa only [add_comm (a ^ 2), denominator_swap a b x y] using h

theorem powerKernel_deriv_y (q a b x y : ℝ) (hd : 0 < denominator a b x y) :
    deriv (fun u ↦ powerKernel q a b x u) y =
      2 * q * ((a ^ 2 + b ^ 2) * y - b) * denominator a b x y ^ (q - 1) :=
  (powerKernel_hasDerivAt_y q a b x y hd).deriv

theorem powerKernel_hasDerivAt_deriv_x (q a b x y : ℝ)
    (hd : 0 < denominator a b x y) :
    HasDerivAt (fun u ↦ deriv (fun v ↦ powerKernel q a b v y) u)
      (2 * q * (a ^ 2 + b ^ 2) * denominator a b x y ^ (q - 1) +
        4 * q * (q - 1) * ((a ^ 2 + b ^ 2) * x - a) ^ 2 *
          denominator a b x y ^ (q - 2)) x := by
  have hpow := (denominator_hasDerivAt_x a b x y).rpow_const (p := q - 1) (Or.inl hd.ne')
  have hlin := ((hasDerivAt_id x).const_mul (a ^ 2 + b ^ 2)).sub_const a
  have hformula : HasDerivAt
      (fun u ↦ 2 * q * ((a ^ 2 + b ^ 2) * u - a) * denominator a b u y ^ (q - 1))
      (2 * q * (a ^ 2 + b ^ 2) * denominator a b x y ^ (q - 1) +
        4 * q * (q - 1) * ((a ^ 2 + b ^ 2) * x - a) ^ 2 *
          denominator a b x y ^ (q - 2)) x := by
    convert (hlin.mul hpow).const_mul (2 * q) using 1
    · funext u
      dsimp
      ring
    · simp only [show q - 1 - 1 = q - 2 by ring, id_eq]
      ring
  apply hformula.congr_of_eventuallyEq
  have hpos : ∀ᶠ u in nhds x, 0 < denominator a b u y :=
    (denominator_hasDerivAt_x a b x y).continuousAt.eventually (lt_mem_nhds hd)
  exact hpos.mono fun u hu ↦ powerKernel_deriv_x q a b u y hu

theorem powerKernel_deriv2_x (q a b x y : ℝ) (hd : 0 < denominator a b x y) :
    deriv (fun u ↦ deriv (fun v ↦ powerKernel q a b v y) u) x =
      2 * q * (a ^ 2 + b ^ 2) * denominator a b x y ^ (q - 1) +
        4 * q * (q - 1) * ((a ^ 2 + b ^ 2) * x - a) ^ 2 *
          denominator a b x y ^ (q - 2) :=
  (powerKernel_hasDerivAt_deriv_x q a b x y hd).deriv

theorem powerKernel_deriv2_y (q a b x y : ℝ) (hd : 0 < denominator a b x y) :
    deriv (fun u ↦ deriv (fun v ↦ powerKernel q a b x v) u) y =
      2 * q * (a ^ 2 + b ^ 2) * denominator a b x y ^ (q - 1) +
        4 * q * (q - 1) * ((a ^ 2 + b ^ 2) * y - b) ^ 2 *
          denominator a b x y ^ (q - 2) := by
  have h := powerKernel_deriv2_x q b a y x (by simpa [denominator_swap] using hd)
  have hfun : (fun u ↦ powerKernel q a b x u) = (fun u ↦ powerKernel q b a u x) :=
    funext fun u ↦ powerKernel_swap q a b x u
  simp only [hfun, add_comm (a ^ 2), denominator_swap a b x y]
  exact h

/-- Summing the two Cartesian second derivatives cancels the angular terms. -/
theorem powerKernel_laplacian (q a b x y : ℝ) (hd : 0 < denominator a b x y) :
    deriv (fun u ↦ deriv (fun v ↦ powerKernel q a b v y) u) x +
        deriv (fun u ↦ deriv (fun v ↦ powerKernel q a b x v) u) y =
      4 * q ^ 2 * (a ^ 2 + b ^ 2) * denominator a b x y ^ (q - 1) := by
  rw [powerKernel_deriv2_x q a b x y hd, powerKernel_deriv2_y q a b x y hd]
  have hp : denominator a b x y ^ (q - 1) =
      denominator a b x y * denominator a b x y ^ (q - 2) := by
    have he : denominator a b x y ^ (q - 2) =
        denominator a b x y ^ (q - 1) / denominator a b x y := by
      rw [show q - 2 = (q - 1) - 1 by ring]
      exact Real.rpow_sub_one hd.ne' _
    rw [he, mul_div_cancel₀ _ hd.ne']
  rw [hp]
  unfold denominator
  ring

/-- The second-order operator used by the weighted weak-type proof. -/
def ellipticOperator (k : ℝ) (F : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun u ↦ deriv (fun v ↦ F v y) u) x +
    deriv (fun u ↦ deriv (fun v ↦ F x v) u) y -
    (2 * k / (1 - (x ^ 2 + y ^ 2))) *
      (x * deriv (fun u ↦ F u y) x + y * deriv (fun u ↦ F x u) y) -
    (k ^ 2 / (1 - (x ^ 2 + y ^ 2))) * F x y

/-- The exact kernel equation, including its nonpositive interior-source defect. -/
theorem ellipticOperator_powerKernel (k a b x y : ℝ)
    (hd : 0 < denominator a b x y) (ht : 1 - (x ^ 2 + y ^ 2) ≠ 0) :
    ellipticOperator k (powerKernel (-k / 2) a b) x y =
      -(k ^ 2 * (1 - (a ^ 2 + b ^ 2))) /
        ((1 - (x ^ 2 + y ^ 2)) * denominator a b x y) *
          powerKernel (-k / 2) a b x y := by
  rw [ellipticOperator, powerKernel_laplacian (-k / 2) a b x y hd,
    powerKernel_deriv_x (-k / 2) a b x y hd,
    powerKernel_deriv_y (-k / 2) a b x y hd, Real.rpow_sub_one hd.ne']
  unfold powerKernel
  field_simp [ht, hd.ne']
  unfold denominator
  ring

theorem ellipticOperator_powerKernel_nonpos (k a b x y : ℝ)
    (hd : 0 < denominator a b x y) (ht : 0 < 1 - (x ^ 2 + y ^ 2))
    (hw : a ^ 2 + b ^ 2 ≤ 1) :
    ellipticOperator k (powerKernel (-k / 2) a b) x y ≤ 0 := by
  rw [ellipticOperator_powerKernel k a b x y hd ht.ne']
  exact mul_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg (sq_nonneg k)
      (sub_nonneg.mpr hw))) (mul_nonneg ht.le hd.le))
    (Real.rpow_nonneg hd.le _)

theorem ellipticOperator_powerKernel_boundary (k a b x y : ℝ)
    (hd : 0 < denominator a b x y) (ht : 1 - (x ^ 2 + y ^ 2) ≠ 0)
    (hw : a ^ 2 + b ^ 2 = 1) :
    ellipticOperator k (powerKernel (-k / 2) a b) x y = 0 := by
  rw [ellipticOperator_powerKernel k a b x y hd ht, hw]
  simp

/-- The Cartesian denominator is exactly the squared modulus of the Bergman denominator. -/
theorem denominator_eq_norm_sq (z w : ℂ) :
    denominator w.re w.im z.re z.im = ‖1 - z * star w‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.mul_re,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.sub_im, Complex.one_im,
    Complex.mul_im]
  unfold denominator
  ring

/-- The real-power kernel used in the differential calculation is the positive Bergman kernel. -/
theorem powerKernel_eq_norm_weightedKernel (α : ℝ) (z w : ℂ) :
    powerKernel (-(α + 2) / 2) w.re w.im z.re z.im = ‖weightedKernel α z w‖ := by
  rw [powerKernel, denominator_eq_norm_sq, norm_weightedKernel,
    ← Real.rpow_natCast_mul (norm_nonneg _) 2]
  congr 1
  ring

theorem denominator_pos {z w : ℂ} (hz : z ∈ disk) (hw : ‖w‖ ≤ 1) :
    0 < denominator w.re w.im z.re z.im := by
  have hz' : ‖z‖ < 1 := (mem_disk_iff z).mp hz
  have hmul : ‖z * star w‖ ≤ ‖z‖ := by
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_right (norm_nonneg z) hw
  have hsub := norm_sub_norm_le (1 : ℂ) (z * star w)
  simp only [norm_one] at hsub
  rw [denominator_eq_norm_sq]
  exact sq_pos_of_pos (by linarith)

end BergmanWeakType.Weighted
