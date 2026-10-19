/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.IntegralPhase
public import BergmanWeakType.KernelIntegrability
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

noncomputable section

open Set MeasureTheory Metric Filter
open scoped Topology ComplexConjugate

namespace BergmanWeakType

theorem kernel_denominator_ne_zero_closed_left {ζ w : ℂ} (hζ : ‖ζ‖ ≤ 1) (hw : w ∈ disk) :
    1 - ζ * star w ≠ 0 := by
  have hnorm : ‖ζ * star w‖ < 1 := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg w) hζ).trans_lt ((mem_disk_iff w).mp hw)
  intro h
  have hmul : ζ * star w = 1 := (sub_eq_zero.mp h).symm
  rw [hmul, norm_one] at hnorm
  exact (lt_irrefl 1) hnorm

/-- The compact-core integrand stays continuous even for boundary output parameters. -/
theorem continuousOn_coreIntegrand {q : ℂ → ℂ} (hq : ContinuousOn q disk)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) {r : ℝ} (hr : r < 1) :
    ContinuousOn (fun w ↦ q w * kernel ζ w) (closedBall 0 r) := by
  have hsub : closedBall (0 : ℂ) r ⊆ disk := fun _ hw ↦ lt_of_le_of_lt hw hr
  refine (hq.mono hsub).mul ?_
  unfold kernel
  exact ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id.star)).inv₀
    (fun w hw ↦ kernel_denominator_ne_zero_closed_left hζ (hsub hw))).pow 2

/-- Equality in the compact-core triangle inequality forces the Möbius derivative form. -/
theorem derivative_form_of_core_triangle_eq {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q disk) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hI : (∫ w in ball 0 r, q w * kernel ζ w ∂area) ≠ 0)
    (heq : ‖∫ w in ball 0 r, q w * kernel ζ w ∂area‖ =
      ∫ w in ball 0 r, ‖q w * kernel ζ w‖ ∂area) :
    ∀ w ∈ disk, q w * (1 - star ζ * w) ^ 2 = q 0 := by
  let c := ∫ w in ball 0 r, q w * kernel ζ w ∂area
  let G : ℂ → ℂ := fun w ↦ q w * (1 - star ζ * w) ^ 2 / c
  have hc : c ≠ 0 := hI
  have hBcont := continuousOn_coreIntegrand hq.continuousOn hζ hr1
  have hBi : IntegrableOn (fun w ↦ q w * kernel ζ w) (ball 0 r) area :=
    (hBcont.integrableOn_compact (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  have hphase := im_div_integral_eq_zero_on isOpen_ball
    (hBcont.mono ball_subset_closedBall) hBi hI heq
  have hlin : DifferentiableOn ℂ (fun w : ℂ ↦ 1 - star ζ * w) disk :=
    (differentiableOn_const 1).sub ((differentiableOn_const (star ζ)).mul differentiableOn_id)
  have hGd : DifferentiableOn ℂ G disk := (hq.mul (hlin.pow 2)).div_const c
  have hinner : ∀ w ∈ ball (0 : ℂ) r, (G w).im = 0 := by
    intro w hw
    have hwd : w ∈ disk := lt_trans hw hr1
    have hd : 1 - ζ * star w ≠ 0 := kernel_denominator_ne_zero_closed_left hζ hwd
    have hconj : conj (1 - ζ * star w) = 1 - star ζ * w := by simp
    have hform : G w = (q w * kernel ζ w / c) *
        (‖1 - ζ * star w‖ ^ 4 : ℝ) := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ← Complex.normSq_eq_norm_sq]
      push_cast
      rw [← Complex.mul_conj, hconj]
      dsimp [G, kernel]
      simp only [← starRingEnd_apply] at hd ⊢
      field_simp [hd, hc]
    have him := hphase w hw
    change (q w * kernel ζ w / c).im = 0 at him
    rw [hform, Complex.mul_im, Complex.ofReal_im, him]
    ring
  have hsub : ball (0 : ℂ) r ⊆ disk := fun _ hw ↦ lt_trans hw hr1
  obtain ⟨d, hd⟩ := (hGd.analyticOnNhd isOpen_ball).mono hsub |>.eq_const_of_im_eq_const
    hinner isOpen_ball ⟨⟨0, mem_ball_self hr⟩, (convex_ball 0 r).isPreconnected⟩
  have hall : EqOn G (fun _ ↦ d) disk :=
    (hGd.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (convex_ball (0 : ℂ) 1).isPreconnected (by simp [disk])
      ((isOpen_ball.eventually_mem (mem_ball_self hr)).mono fun w hw ↦ hd w hw)
  intro w hw
  have hval : G w = G 0 := (hall hw).trans (hall (by simp [disk])).symm
  dsimp [G] at hval
  change q w * (1 - conj ζ * w) ^ 2 = q 0
  simpa only [mul_zero, sub_zero, one_pow, mul_one] using
    (div_left_inj' hc).mp hval

end BergmanWeakType
