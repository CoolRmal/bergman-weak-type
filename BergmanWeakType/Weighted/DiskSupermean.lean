/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.KernelIntegrability
public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-! # Poisson supermean property of the normalized unweighted kernel -/

@[expose] public section

noncomputable section

open MeasureTheory Complex InnerProductSpace
open scoped Topology

namespace BergmanWeakType.Weighted

def normalizedKernel (z w : ℂ) : ℝ := (1 - ‖z‖ ^ 2) * ‖kernel z w‖

def kernelResolvent (w z : ℂ) : ℂ := z / (1 - z * star w)

def kernelHerglotz (w z : ℂ) : ℂ := (1 + z * star w) / (1 - z * star w)

theorem re_cayley (u : ℂ) :
    ((1 + u) / (1 - u)).re = (1 - ‖u‖ ^ 2) / ‖1 - u‖ ^ 2 := by
  simp only [Complex.div_re, Complex.sq_norm,
    Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im,
    Complex.one_im, Complex.sub_im, Complex.normSq_apply]
  ring

/-- A harmonic part minus a nonnegative multiple of a holomorphic square. -/
theorem normalizedKernel_decomposition (z w : ℂ) :
    normalizedKernel z w = (kernelHerglotz w z).re -
      (1 - ‖w‖ ^ 2) * ‖kernelResolvent w z‖ ^ 2 := by
  rw [normalizedKernel, kernelHerglotz, re_cayley, kernelResolvent, norm_kernel]
  simp only [norm_mul, norm_star, norm_div, div_pow, mul_pow, inv_pow]
  ring

theorem kernel_denominator_ne_zero_closed {R : ℝ} (hR : R < 1) {z w : ℂ}
    (hz : z ∈ Metric.closedBall 0 R) (hw : w ∈ disk) : 1 - z * star w ≠ 0 := by
  apply kernel_denominator_ne_zero _ hw
  exact (mem_disk_iff z).mpr ((by simpa using hz : ‖z‖ ≤ R).trans_lt hR)

theorem differentiableOn_kernelResolvent {R : ℝ} (hR : R < 1) {w : ℂ} (hw : w ∈ disk) :
    DifferentiableOn ℂ (kernelResolvent w) (Metric.closedBall 0 R) := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  exact differentiableAt_id.div
    (differentiableAt_const 1 |>.sub (differentiableAt_id.mul_const (star w)))
    (kernel_denominator_ne_zero_closed hR hz hw)

theorem differentiableOn_kernelHerglotz {R : ℝ} (hR : R < 1) {w : ℂ} (hw : w ∈ disk) :
    DifferentiableOn ℂ (kernelHerglotz w) (Metric.closedBall 0 R) := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  exact ((differentiableAt_id.mul_const (star w)).const_add 1).div
    (differentiableAt_const 1 |>.sub (differentiableAt_id.mul_const (star w)))
    (kernel_denominator_ne_zero_closed hR hz hw)

theorem continuousOn_poisson_circle {R : ℝ} {z : ℂ} (hz : z ∈ Metric.ball 0 R) :
    ContinuousOn (poissonKernel 0 z) (Metric.sphere 0 |R|) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  apply Complex.continuous_re.comp_continuousOn
  apply continuousOn_herglotzRieszKernel_sphere
  intro heq
  have hz' : ‖z‖ < R := by simpa using hz
  have heq' : ‖z‖ = |R| := by simpa using heq
  linarith [le_abs_self R]

theorem poisson_nonneg_on_circle {R : ℝ} {z ζ : ℂ} (hz : z ∈ Metric.ball 0 R)
    (hζ : ζ ∈ Metric.sphere 0 |R|) : 0 ≤ poissonKernel 0 z ζ := by
  have hz' : ‖z‖ < R := by simpa using hz
  have hR : 0 < R := (norm_nonneg z).trans_lt hz'
  have hζ' : ‖ζ‖ = R := by simpa [abs_of_pos hR] using hζ
  simp only [poissonKernel_def, sub_zero, hζ']
  exact div_nonneg (by nlinarith [norm_nonneg z]) (sq_nonneg _)

theorem circleAverage_poisson_re {R : ℝ} {z : ℂ} {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (Metric.ball 0 R)) (hz : z ∈ Metric.ball 0 R) :
    Real.circleAverage (fun ζ ↦ poissonKernel 0 z ζ * (g ζ).re) 0 R = (g z).re := by
  have hR : 0 < R := Metric.pos_of_mem_ball hz
  have hgs : ContinuousOn g (Metric.sphere 0 |R|) := by
    apply hg.continuousOn.mono
    rw [closure_ball 0 hR.ne']
    simpa only [abs_of_pos hR] using Metric.sphere_subset_closedBall
  have hi : CircleIntegrable (poissonKernel 0 z • g) 0 R :=
    ((continuousOn_poisson_circle hz).smul hgs).circleIntegrable'
  have h := Complex.reCLM.circleAverage_comp_comm hi
  rw [hg.circleAverage_poissonKernel_smul hz] at h
  simpa only [Function.comp_def, Complex.reCLM_apply, Pi.smul_apply', Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using h

/-- The elementary Poisson Jensen inequality for the squared norm of a holomorphic function. -/
theorem norm_sq_le_circleAverage_poisson {R : ℝ} {z : ℂ} {g : ℂ → ℂ}
    (hg : DiffContOnCl ℂ g (Metric.ball 0 R)) (hz : z ∈ Metric.ball 0 R) :
    ‖g z‖ ^ 2 ≤ Real.circleAverage (fun ζ ↦ poissonKernel 0 z ζ * ‖g ζ‖ ^ 2) 0 R := by
  let H : ℂ → ℂ := fun ζ ↦ (2 * star (g z)) * g ζ - ((‖g z‖ ^ 2 : ℝ) : ℂ)
  have hH : DiffContOnCl ℂ H (Metric.ball 0 R) :=
    (hg.const_smul (2 * star (g z))).sub_const _
  have htangent (ζ : ℂ) : (H ζ).re ≤ ‖g ζ‖ ^ 2 := by
    have hsq := sq_nonneg ((g ζ).re - (g z).re)
    have hsq' := sq_nonneg ((g ζ).im - (g z).im)
    simp only [H, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.mul_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.sq_norm, Complex.normSq_apply] at *
    norm_num at *
    nlinarith
  have hHz : (H z).re = ‖g z‖ ^ 2 := by
    simp only [H, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.mul_im,
      Complex.star_def, Complex.conj_re, Complex.conj_im,
      Complex.sq_norm, Complex.normSq_apply]
    norm_num
    ring
  have hR : 0 < R := Metric.pos_of_mem_ball hz
  have hgs : ContinuousOn g (Metric.sphere 0 |R|) := by
    apply hg.continuousOn.mono
    rw [closure_ball 0 hR.ne']
    simpa only [abs_of_pos hR] using Metric.sphere_subset_closedBall
  have hHs : ContinuousOn H (Metric.sphere 0 |R|) := by
    apply hH.continuousOn.mono
    rw [closure_ball 0 hR.ne']
    simpa only [abs_of_pos hR] using Metric.sphere_subset_closedBall
  rw [← hHz, ← circleAverage_poisson_re hH hz]
  apply Real.circleAverage_mono
    ((continuousOn_poisson_circle hz).mul (Complex.continuous_re.comp_continuousOn hHs)).circleIntegrable'
    ((continuousOn_poisson_circle hz).mul (hgs.norm.pow 2)).circleIntegrable'
  intro ζ hζ
  exact mul_le_mul_of_nonneg_left (htangent ζ) (poisson_nonneg_on_circle hz hζ)

/-- Every normalized kernel column is a Poisson supersolution on concentric interior disks. -/
theorem normalizedKernel_poisson_supermean {R : ℝ} (hR : R < 1) {z w : ℂ}
    (hz : z ∈ Metric.ball 0 R) (hw : w ∈ disk) :
    Real.circleAverage (fun ζ ↦ poissonKernel 0 z ζ * normalizedKernel ζ w) 0 R ≤
      normalizedKernel z w := by
  have hR0 : 0 < R := Metric.pos_of_mem_ball hz
  have hH := (differentiableOn_kernelHerglotz hR hw).diffContOnCl_ball (Set.Subset.refl _)
  have hG := (differentiableOn_kernelResolvent hR hw).diffContOnCl_ball (Set.Subset.refl _)
  have hs : Metric.sphere (0 : ℂ) |R| ⊆ Metric.closedBall 0 R := by
    simpa only [abs_of_pos hR0] using Metric.sphere_subset_closedBall
  have hHs := (differentiableOn_kernelHerglotz hR hw).continuousOn.mono hs
  have hGs := (differentiableOn_kernelResolvent hR hw).continuousOn.mono hs
  have hiH : CircleIntegrable
      (fun ζ ↦ poissonKernel 0 z ζ * (kernelHerglotz w ζ).re) 0 R :=
    ((continuousOn_poisson_circle hz).mul
      (Complex.continuous_re.comp_continuousOn hHs)).circleIntegrable'
  have hiG : CircleIntegrable
      (fun ζ ↦ poissonKernel 0 z ζ * ‖kernelResolvent w ζ‖ ^ 2) 0 R :=
    ((continuousOn_poisson_circle hz).mul (hGs.norm.pow 2)).circleIntegrable'
  have hiGc : CircleIntegrable
      (fun ζ ↦ (1 - ‖w‖ ^ 2) • (poissonKernel 0 z ζ * ‖kernelResolvent w ζ‖ ^ 2)) 0 R :=
    hiG.const_smul
  have heq : (fun ζ ↦ poissonKernel 0 z ζ * normalizedKernel ζ w) =
      (fun ζ ↦ poissonKernel 0 z ζ * (kernelHerglotz w ζ).re -
        (1 - ‖w‖ ^ 2) • (poissonKernel 0 z ζ * ‖kernelResolvent w ζ‖ ^ 2)) := by
    funext ζ
    rw [normalizedKernel_decomposition]
    simp only [smul_eq_mul]
    ring
  rw [heq, Real.circleAverage_fun_sub hiH hiGc,
    Real.circleAverage_fun_smul, circleAverage_poisson_re hH hz,
    normalizedKernel_decomposition, smul_eq_mul]
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left (norm_sq_le_circleAverage_poisson hG hz)
    (by nlinarith [(mem_disk_iff w).mp hw, norm_nonneg w])) _

end BergmanWeakType.Weighted
