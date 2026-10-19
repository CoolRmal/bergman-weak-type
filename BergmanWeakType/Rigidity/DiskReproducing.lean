/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.KernelIntegrability
public import BergmanWeakType.Domain
public import BergmanWeakType.Rigidity.PolarIntegral
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

open Set Filter Metric MeasureTheory Complex Real
open scoped Topology Real ComplexConjugate

namespace BergmanWeakType

/-- Cauchy's derivative formula at any point inside the contour. -/
theorem circleIntegral_sub_inv_sq_mul {f : ℂ → ℂ} {c a : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : DiffContOnCl ℂ f (ball c r)) (ha : a ∈ ball c r) :
    (∮ w in C(c, r), (w - a) ^ (-2 : ℤ) * f w) = (2 * π * I) * deriv f a := by
  have hc : CircleIntegrable f c r :=
    (hf.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable hr.le
  have has := Complex.hasDerivAt_circleIntegral_sub_inv_smul (w := a) hc (by
    rw [abs_of_pos hr]
    exact fun hs ↦ (ne_of_lt ha) (mem_sphere.mp hs))
  have heq : (fun a ↦ ∮ w in C(c, r), (w - a)⁻¹ • f w) =ᶠ[𝓝 a]
      (fun a ↦ (2 * π * I) * f a) := by
    filter_upwards [isOpen_ball.eventually_mem ha] with b hb
    simpa only [smul_eq_mul] using hf.circleIntegral_sub_inv_smul hb
  have hd := (hf.differentiableAt isOpen_ball ha).hasDerivAt.const_mul (2 * π * I)
  simpa only [smul_eq_mul] using (has.congr_of_eventuallyEq heq.symm).unique hd

/-- The angular Bergman average is the radial derivative of the holomorphic primitive. -/
theorem circleAverage_kernel_mul {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disk)
    {z : ℂ} (hz : z ∈ disk) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    circleAverage (fun w ↦ kernel z w * f w) 0 r =
      f ((r : ℂ) ^ 2 * z) + (r : ℂ) ^ 2 * z * deriv f ((r : ℂ) ^ 2 * z) := by
  let a : ℂ := (r : ℂ) ^ 2 * z
  have hz1 : ‖z‖ < 1 := (mem_disk_iff z).mp hz
  have ha : a ∈ ball 0 r := by
    simp only [a, mem_ball, dist_zero_right, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
    nlinarith [sq_pos_of_pos hr, norm_nonneg z]
  have hsub : closedBall (0 : ℂ) r ⊆ disk := by
    intro w hw
    exact lt_of_le_of_lt hw hr1
  have hfr : DiffContOnCl ℂ f (ball 0 r) :=
    (hf.mono (closure_ball_subset_closedBall.trans hsub)).diffContOnCl
  have hne : ∀ w ∈ sphere (0 : ℂ) r, w - a ≠ 0 := by
    intro w hw hwa
    have : w = a := sub_eq_zero.mp hwa
    exact (ne_of_lt ha) (mem_sphere.mp (this ▸ hw))
  have hci₁ : CircleIntegrable (fun w ↦ (w - a)⁻¹ * f w) 0 r := by
    apply ContinuousOn.circleIntegrable hr.le
    exact ((continuousOn_id.sub continuousOn_const).inv₀ hne).mul
      (hfr.continuousOn_ball.mono sphere_subset_closedBall)
  have hci₂ : CircleIntegrable (fun w ↦ (w - a) ^ (-2 : ℤ) * f w) 0 r := by
    apply ContinuousOn.circleIntegrable hr.le
    exact ((continuousOn_id.sub continuousOn_const).zpow₀ (-2) (by
      intro w hw
      exact Or.inl (hne w hw))).mul (hfr.continuousOn_ball.mono sphere_subset_closedBall)
  have hcauchy : (∮ w in C(0, r), (w - a)⁻¹ * f w) = (2 * π * I) * f a := by
    simpa only [smul_eq_mul] using hfr.circleIntegral_sub_inv_smul ha
  rw [circleAverage_eq_circleIntegral hr.ne']
  have hintegrand : ∀ w ∈ sphere (0 : ℂ) r,
      (w - 0)⁻¹ • (kernel z w * f w) =
        (w - a)⁻¹ * f w + a * ((w - a) ^ (-2 : ℤ) * f w) := by
    intro w hw
    have hwNorm : ‖w‖ = r := by simpa only [mem_sphere, dist_zero_right] using hw
    have hw0 : w ≠ 0 := by intro h; simp [h] at hwNorm; linarith
    have hwstar : w * conj w = (r : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hwNorm]
      norm_cast
    have heq : w * (1 - z * conj w) = w - a := by
      dsimp [a]
      linear_combination -z * hwstar
    have hdenEq : 1 - z * conj w = (w - a) / w := by
      apply (eq_div_iff hw0).mpr
      linear_combination heq
    simp only [sub_zero, smul_eq_mul, kernel, zpow_neg, zpow_ofNat, ← starRingEnd_apply]
    rw [hdenEq]
    field_simp [hw0, hne w hw]
    ring
  have hci₂a : CircleIntegrable (fun w ↦ a * ((w - a) ^ (-2 : ℤ) * f w)) 0 r := by
    apply ContinuousOn.circleIntegrable hr.le
    exact continuousOn_const.mul
      (((continuousOn_id.sub continuousOn_const).zpow₀ (-2) (fun w hw ↦ Or.inl (hne w hw))).mul
        (hfr.continuousOn_ball.mono sphere_subset_closedBall))
  rw [circleIntegral.integral_congr hr.le hintegrand,
    circleIntegral.integral_add hci₁ hci₂a, circleIntegral.integral_const_mul,
    hcauchy, circleIntegral_sub_inv_sq_mul hr hfr ha]
  simp only [smul_eq_mul]
  field_simp
  rfl

/-- The explicit disk kernel reproduces every integrable holomorphic function. -/
theorem integral_kernel_mul_eq {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disk)
    (hfi : Integrable f diskArea) {z : ℂ} (hz : z ∈ disk) :
    (∫ w, kernel z w * f w ∂diskArea) = f z := by
  have hz1 : ‖z‖ < 1 := (mem_disk_iff z).mp hz
  have hmap : MapsTo (fun r : ℝ ↦ (r : ℂ) ^ 2 * z) (Icc 0 1) disk := by
    intro r hr
    apply (mem_disk_iff _).mpr
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1]
    have hr2 : r ^ 2 ≤ 1 := by nlinarith [hr.1, hr.2]
    exact (mul_le_of_le_one_left (norm_nonneg z) hr2).trans_lt hz1
  have hderiv : ∀ r ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ ↦ (s : ℂ) ^ 2 * f ((s : ℂ) ^ 2 * z))
        ((2 * r) • (f ((r : ℂ) ^ 2 * z) +
          (r : ℂ) ^ 2 * z * deriv f ((r : ℂ) ^ 2 * z))) r := by
    intro r hr
    have hpow := (hasDerivAt_id (r : ℂ)).pow 2
    have hcomp := (hf.differentiableAt (isOpen_ball.mem_nhds (hmap hr))).hasDerivAt.comp
      (r : ℂ) (hpow.mul_const z)
    convert (hpow.mul hcomp).comp_ofReal using 1
    · rfl
    · simp only [Pi.pow_apply, Function.comp_apply, id_eq, Nat.reduceSub, pow_one,
        Nat.cast_ofNat, mul_one, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
      ring
  have hcont : ContinuousOn (fun r : ℝ ↦ (2 * r) •
      (f ((r : ℂ) ^ 2 * z) + (r : ℂ) ^ 2 * z * deriv f ((r : ℂ) ^ 2 * z))) (Icc 0 1) := by
    have hs : ContinuousOn (fun r : ℝ ↦ 2 * r) (Icc 0 1) := by fun_prop
    have ha : ContinuousOn (fun r : ℝ ↦ (r : ℂ) ^ 2 * z) (Icc 0 1) := by fun_prop
    have hfc := hf.continuousOn.comp ha hmap
    have hdc := (hf.analyticOnNhd isOpen_ball).deriv.continuousOn.comp ha hmap
    apply (hs.smul (hfc.add (ha.mul hdc))).congr
    intro r _
    rfl
  rw [integral_diskArea_eq_circleAverage (integrable_kernel_mul hfi hz)]
  calc
    _ = ∫ r in Ioo (0 : ℝ) 1, (2 * r) • (f ((r : ℂ) ^ 2 * z) +
        (r : ℂ) ^ 2 * z * deriv f ((r : ℂ) ^ 2 * z)) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      dsimp only
      rw [circleAverage_kernel_mul hf hz hr.1 hr.2]
    _ = ∫ r in (0 : ℝ)..1, (2 * r) • (f ((r : ℂ) ^ 2 * z) +
        (r : ℂ) ^ 2 * z * deriv f ((r : ℂ) ^ 2 * z)) := by
      rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
    _ = f z := by
      have hi := hcont.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun r hr ↦ hderiv r (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hr)) hi
      simpa only [Complex.ofReal_one, Complex.ofReal_zero, one_pow, zero_pow (by omega : 2 ≠ 0),
        one_mul, zero_mul, sub_zero] using ht

/-- The explicit unit-disk kernel satisfies the standard Bergman-kernel characterization. -/
theorem isBergmanKernel_disk : IsBergmanKernel disk kernel where
  holomorphic w hw := by
    unfold kernel
    exact (((differentiableOn_const 1).sub
      (differentiableOn_id.mul_const (star w))).inv
      (fun z hz ↦ kernel_denominator_ne_zero hz hw)).pow 2
  hermitian z _ w _ := by simp [kernel, star_mul]
  squareIntegrable z hz := by
    change MemLp (kernel z) 2 diskArea
    exact MemLp.of_bound (aestronglyMeasurable_kernel hz) ((1 - ‖z‖)⁻¹ ^ 2)
      (ae_mem_disk.mono fun w hw ↦ norm_kernel_le hz hw)
  reproduces f hf hfi z hz := by
    have hfi' : MemLp f 2 diskArea := hfi
    exact integral_kernel_mul_eq hf (hfi'.integrable (by norm_num)) hz

end BergmanWeakType
