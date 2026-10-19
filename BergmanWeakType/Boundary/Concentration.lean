/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Reproduction
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! # Interior kernel columns as limits of admissible inputs -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Topology

namespace BergmanWeakType

theorem ball_subset_disk {a : ℂ} {r : ℝ} (hr : r ≤ 1 - ‖a‖) :
    Metric.ball a r ⊆ disk := by
  intro w hw
  apply (mem_disk_iff w).mpr
  have hw' : ‖w - a‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have := norm_add_le (w - a) a
  rw [sub_add_cancel] at this
  linarith

theorem weightedArea_interior_ball_pos (α : ℝ) (hα : -1 < α) {a : ℂ} {r : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1 - ‖a‖) : 0 < weightedArea α (Metric.ball a r) := by
  apply pos_iff_ne_zero.mpr
  intro h
  have hd := diskArea_absolutelyContinuous_weightedArea α hα h
  rw [diskArea, Measure.restrict_eq_self _ (ball_subset_disk hr1), area_ball] at hd
  have hp : 0 < ENNReal.ofReal r ^ 2 := by positivity
  exact hp.ne' hd

/-- Nearby interior source points produce uniformly close kernel columns on the whole disk. -/
theorem exists_uniform_weightedKernel_near_source (α : ℝ) {a : ℂ} (ha : a ∈ disk)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 - ‖a‖ ∧ ∀ z ∈ disk, ∀ w ∈ Metric.ball a r,
      ‖weightedKernel α z w - weightedKernel α z a‖ < ε := by
  let R := (1 + ‖a‖) / 2
  have ha' : ‖a‖ < 1 := (mem_disk_iff a).mp ha
  have haR : ‖a‖ < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  have hcont : ContinuousOn (fun u : ℂ ↦ (1 - u) ^ (-(α + 2) : ℂ))
      (Metric.closedBall 0 R) := by
    apply (continuous_const.sub continuous_id).continuousOn.cpow_const
    intro u hu
    have hu' : ‖u‖ ≤ R := by simpa using hu
    apply Complex.mem_slitPlane_iff.mpr
    left
    change 0 < 1 - u.re
    linarith [Complex.re_le_norm u]
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_closedBall (0 : ℂ) R).uniformContinuousOn_of_continuous hcont) ε hε
  refine ⟨min δ (R - ‖a‖), lt_min hδ (sub_pos.mpr haR), ?_, ?_⟩
  · exact (min_le_right _ _).trans (by linarith)
  intro z hz w hw
  have hz' : ‖z‖ ≤ 1 := ((mem_disk_iff z).mp hz).le
  have hw' : ‖w - a‖ < min δ (R - ‖a‖) := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hwR : ‖w‖ ≤ R := by
    have htri := norm_add_le (w - a) a
    rw [sub_add_cancel] at htri
    have := hw'.trans_le (min_le_right _ _)
    linarith
  have hza : z * star a ∈ Metric.closedBall 0 R := by
    simp only [Metric.mem_closedBall, dist_zero_right, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg a) hz').trans haR.le
  have hzw : z * star w ∈ Metric.closedBall 0 R := by
    simp only [Metric.mem_closedBall, dist_zero_right, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg w) hz').trans hwR
  have hdist : dist (z * star w) (z * star a) < δ := by
    rw [dist_eq_norm, ← mul_sub, ← star_sub, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) hz').trans_lt
      (hw'.trans_le (min_le_left _ _))
  simpa only [weightedKernel, dist_eq_norm] using hclose _ hzw _ hza hdist

theorem norm_weightedProjection_indicator_sub_column_le {α : ℝ} (hα : -1 < α)
    {s : Set ℂ} (hs : MeasurableSet s) {z a : ℂ} (hz : z ∈ disk) {ε : ℝ}
    (hclose : ∀ w ∈ s, ‖weightedKernel α z w - weightedKernel α z a‖ ≤ ε) :
    ‖weightedProjection α (s.indicator (fun _ ↦ (1 : ℂ))) z -
      (weightedArea α).real s * weightedKernel α z a‖ ≤
        ε * (weightedArea α).real s := by
  let := weightedArea_isProbabilityMeasure α hα
  have hK : Integrable (weightedKernel α z) (weightedArea α) := by
    simpa only [mul_one] using
      integrable_weightedKernel_mul hα (integrable_const (1 : ℂ)) hz
  calc
    _ = ‖∫ w in s, weightedKernel α z w - weightedKernel α z a ∂weightedArea α‖ := by
      rw [integral_sub hK.integrableOn (integrable_const _), setIntegral_const,
        weightedProjection_indicator_eq_setIntegral α hs z]
      simp only [Complex.real_smul]
    _ ≤ ε * (weightedArea α).real s :=
      norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) hclose

/-- A strict column lower bound on a target set transfers to every weak type bound. -/
theorem column_threshold_le_weakBound {α L ℓ : ℝ} {C : ℝ≥0∞} (hα : -1 < α)
    (hC : IsWeakTypeBound (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) C)
    {a : ℂ} (ha : a ∈ disk) {E : Set ℂ} (hE : E ⊆ disk)
    (hcol : ∀ z ∈ E, L ≤ ‖weightedKernel α z a‖) (hℓ : 0 < ℓ) (hℓL : ℓ < L) :
    ENNReal.ofReal ℓ * weightedArea α E ≤ C := by
  let := weightedArea_isProbabilityMeasure α hα
  obtain ⟨r, hr, hr1, hclose⟩ := exists_uniform_weightedKernel_near_source α ha
    (show 0 < (L - ℓ) / 2 by linarith)
  let s := Metric.ball a r
  let f : ℂ → ℂ := s.indicator (fun _ ↦ 1)
  let m := (weightedArea α).real s
  have hs : MeasurableSet s := Metric.isOpen_ball.measurableSet
  have hspos : 0 < weightedArea α s := weightedArea_interior_ball_pos α hα hr hr1
  have hsfinite : weightedArea α s ≠ ∞ := measure_ne_top _ _
  have hm : 0 < m := ENNReal.toReal_pos hspos.ne' hsfinite
  have hf : Integrable f (weightedArea α) := (integrable_const (1 : ℂ)).indicator hs
  have hmass : (∫⁻ w, ‖f w‖ₑ ∂weightedArea α) = weightedArea α s := by
    simp [f, enorm_indicator_eq_indicator_enorm, hs]
  have hsub : E ⊆ {z | ENNReal.ofReal (ℓ * m) < ‖weightedProjection α f z‖ₑ} := by
    intro z hz
    have herr := norm_weightedProjection_indicator_sub_column_le hα hs (hE hz)
      (fun w hw ↦ (hclose z (hE hz) w hw).le)
    have hrev : m * ‖weightedKernel α z a‖ - ‖weightedProjection α f z‖ ≤
        ‖weightedProjection α f z - (m : ℂ) * weightedKernel α z a‖ := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm, norm_sub_rev]
        using norm_sub_norm_le ((m : ℂ) * weightedKernel α z a)
          (weightedProjection α f z)
    have hout : ℓ * m < ‖weightedProjection α f z‖ := by
      have hprod := mul_le_mul_of_nonneg_left (hcol z hz) hm.le
      change ‖weightedProjection α f z - (m : ℂ) * weightedKernel α z a‖ ≤
        (L - ℓ) / 2 * m at herr
      nlinarith
    change ENNReal.ofReal (ℓ * m) < ‖weightedProjection α f z‖ₑ
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_lt_ofReal_iff ((mul_pos hℓ hm).trans hout)).mpr hout
  have hb : ENNReal.ofReal (ℓ * m) * weightedArea α E ≤ C * weightedArea α s := by
    calc
      _ ≤ ENNReal.ofReal (ℓ * m) *
          weightedArea α {z | ENNReal.ofReal (ℓ * m) < ‖weightedProjection α f z‖ₑ} :=
        mul_le_mul_right (measure_mono hsub) _
      _ ≤ _ := by simpa only [hmass] using hC f hf (ℓ * m) (mul_pos hℓ hm)
  have hmcoe : ENNReal.ofReal m = weightedArea α s := ENNReal.ofReal_toReal hsfinite
  rw [ENNReal.ofReal_mul hℓ.le, hmcoe] at hb
  rw [mul_assoc, mul_comm (weightedArea α s), ← mul_assoc] at hb
  exact (ENNReal.mul_le_mul_iff_left hspos.ne' hsfinite).mp hb

/-- Every interior kernel column satisfies the weak bound of the complex projection. -/
theorem column_le_weakBound {α L : ℝ} {C : ℝ≥0∞} (hα : -1 < α)
    (hC : IsWeakTypeBound (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) C)
    {a : ℂ} (ha : a ∈ disk) {E : Set ℂ} (hE : E ⊆ disk)
    (hcol : ∀ z ∈ E, L ≤ ‖weightedKernel α z a‖) (hL : 0 < L) :
    ENNReal.ofReal L * weightedArea α E ≤ C := by
  let := weightedArea_isProbabilityMeasure α hα
  have hlim : Filter.Tendsto (fun ℓ : ℝ ↦ ENNReal.ofReal ℓ * weightedArea α E)
      (𝓝[<] L) (𝓝 (ENNReal.ofReal L * weightedArea α E)) := by
    exact ((ENNReal.continuous_mul_const (measure_ne_top (weightedArea α) E)).comp
      ENNReal.continuous_ofReal).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT hL] with ℓ hℓ
  exact column_threshold_le_weakBound hα hC ha hE hcol hℓ.1 hℓ.2

end BergmanWeakType
