/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.MobiusGeometry
public import BergmanWeakType.CompactGap
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

noncomputable section

open Set MeasureTheory Metric Filter
open scoped Topology

namespace BergmanWeakType

/-- A continuous family on a compact product is continuous after integration against a finite
measure supported on the integration compact set. -/
theorem continuousOn_integral_of_compact_product {X Y E : Type*}
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [FirstCountableTopology Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopologyEither X E]
    {μ : Measure X} [IsFiniteMeasure μ] {K : Set X} {S : Set Y}
    (hK : IsCompact K) (hμ : ∀ᵐ w ∂μ, w ∈ K) (hS : IsCompact S)
    {F : Y → X → E} (hF : ContinuousOn (fun p : Y × X ↦ F p.1 p.2) (S ×ˢ K)) :
    ContinuousOn (fun z ↦ ∫ w, F z w ∂μ) S := by
  have hm {z : Y} (hz : z ∈ S) : AEStronglyMeasurable (F z) μ := by
    have hc : ContinuousOn (F z) K :=
      hF.comp (continuous_const.prodMk continuous_id).continuousOn fun w hw ↦ ⟨hz, hw⟩
    simpa only [Measure.restrict_eq_self_of_ae_mem hμ] using
      hc.aestronglyMeasurable hK.isClosed.measurableSet (μ := μ)
  obtain ⟨M, hM⟩ := (hS.prod hK).bddAbove_image hF.norm
  apply continuousOn_of_dominated (bound := fun _ ↦ M) (fun z hz ↦ hm hz)
    (fun z hz ↦ hμ.mono fun w hw ↦ ?_) (integrable_const M)
    (hμ.mono fun w hw ↦ ?_)
  · exact hM (mem_image_of_mem _ (show (z, w) ∈ S ×ˢ K from ⟨hz, hw⟩))
  · exact hF.comp (continuous_id.prodMk continuous_const).continuousOn fun z hz ↦ ⟨hz, hw⟩

theorem continuousOn_coreIntegrand_product {q : ℂ → ℂ} (hq : ContinuousOn q disk)
    {r : ℝ} (hr : r < 1) :
    ContinuousOn (fun p : ℂ × ℂ ↦ q p.2 * kernel p.1 p.2)
      (closedBall 0 1 ×ˢ closedBall 0 r) := by
  have hq' := hq.comp continuous_snd.continuousOn
    (show MapsTo Prod.snd (closedBall (0 : ℂ) 1 ×ˢ closedBall (0 : ℂ) r) disk from
      fun p hp ↦ lt_of_le_of_lt hp.2 hr)
  refine hq'.mul ?_
  unfold kernel
  refine ((continuousOn_const.sub (continuous_fst.continuousOn.mul
    continuous_snd.star.continuousOn)).inv₀ ?_).pow 2
  intro p hp
  exact kernel_denominator_ne_zero_closed_left (by simpa using hp.1)
    (lt_of_le_of_lt hp.2 hr)

theorem core_norm_integral_pos {q : ℂ → ℂ} (hq : ContinuousOn q disk)
    (hne : ∀ w ∈ disk, q w ≠ 0) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    0 < ∫ w in ball 0 r, ‖q w * kernel ζ w‖ ∂area := by
  have hi : IntegrableOn (fun w ↦ q w * kernel ζ w) (ball 0 r) area :=
    ((continuousOn_coreIntegrand hq hζ hr1).integrableOn_compact
      (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  apply (integral_pos_iff_support_of_nonneg (fun _ ↦ norm_nonneg _) hi.norm).mpr
  have hsub : ball (0 : ℂ) r ⊆ Function.support (fun w ↦ ‖q w * kernel ζ w‖) := by
    intro w hw
    have hwd : w ∈ disk := lt_trans hw hr1
    apply norm_ne_zero_iff.mpr
    exact mul_ne_zero (hne w hwd) (pow_ne_zero 2
      (inv_ne_zero (kernel_denominator_ne_zero_closed_left hζ hwd)))
  calc
    0 < area (ball (0 : ℂ) r) := measure_ball_pos area 0 hr
    _ = (area.restrict (ball (0 : ℂ) r)) (ball 0 r) := by simp
    _ ≤ (area.restrict (ball (0 : ℂ) r))
        (Function.support (fun w ↦ ‖q w * kernel ζ w‖)) := measure_mono hsub

/-- Every bounded nondisk conformal image has a uniform cancellation gap on each fixed inner
disk, including all parameters on the closed unit disk. -/
theorem exists_core_relative_gap {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ disk)
    (hne : ∀ w ∈ disk, deriv φ w ≠ 0) (hbdd : Bornology.IsBounded (φ '' disk))
    (hnd : ¬∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ φ '' disk = ball c R)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ ζ ∈ closedBall (0 : ℂ) 1,
      ‖∫ w in ball 0 r, deriv φ w * kernel ζ w ∂area‖ ≤
        (1 - η) * ∫ w in ball 0 r, ‖deriv φ w * kernel ζ w‖ ∂area := by
  have hq : DifferentiableOn ℂ (deriv φ) disk :=
    (hφ.analyticOnNhd isOpen_ball).deriv.differentiableOn
  have hprod := continuousOn_coreIntegrand_product hq.continuousOn hr1
  have : IsFiniteMeasure (area.restrict (ball (0 : ℂ) r)) :=
    isFiniteMeasure_restrict.mpr ((isBounded_ball (x := (0 : ℂ)) (r := r)).measure_lt_top).ne
  have hμ : ∀ᵐ w ∂area.restrict (ball (0 : ℂ) r), w ∈ closedBall 0 r :=
    (ae_restrict_mem isOpen_ball.measurableSet).mono fun _ hw ↦ ball_subset_closedBall hw
  have hI := continuousOn_integral_of_compact_product (isCompact_closedBall 0 r) hμ
    (isCompact_closedBall (0 : ℂ) 1) (F := fun ζ w ↦ deriv φ w * kernel ζ w) hprod
  have hJ := continuousOn_integral_of_compact_product (isCompact_closedBall 0 r) hμ
    (isCompact_closedBall (0 : ℂ) 1) (F := fun ζ w ↦ ‖deriv φ w * kernel ζ w‖) hprod.norm
  apply exists_uniform_relative_gap (isCompact_closedBall (0 : ℂ) 1)
    ⟨0, by simp⟩ hI.norm hJ (fun _ _ ↦ norm_nonneg _) (fun ζ hζ ↦
      core_norm_integral_pos hq.continuousOn hne (by simpa using hζ) hr hr1)
  intro ζ hζ
  have hζnorm : ‖ζ‖ ≤ 1 := by simpa using hζ
  have hle := norm_integral_le_integral_norm (fun w ↦ deriv φ w * kernel ζ w)
    (μ := area.restrict (ball 0 r))
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hIne : (∫ w in ball 0 r, deriv φ w * kernel ζ w ∂area) ≠ 0 := by
    have hp := core_norm_integral_pos hq.continuousOn hne hζnorm hr hr1
    rw [← heq] at hp
    exact norm_pos_iff.mp hp
  exact hnd (image_is_disk_of_derivative_form hφ (hne 0 (by simp [disk])) hbdd hζnorm
    (derivative_form_of_core_triangle_eq hq hζnorm hr hr1 hIne heq))

end BergmanWeakType
