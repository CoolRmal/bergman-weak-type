/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.KernelIntegrability
public import BergmanWeakType.Comparison
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # The lower bound one for weighted weak type constants

Inputs supported on small disks about zero have projections uniformly close to their total mass.
They provide the sharp universal lower bound one without any boundary or point-mass input.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

/-- The weighted kernels tend uniformly to one as the input point tends to zero. -/
theorem exists_uniform_weightedKernel_near_one (α : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ z ∈ disk, ∀ w ∈ Metric.ball (0 : ℂ) r,
      ‖weightedKernel α z w - 1‖ < ε := by
  have hc : ContinuousAt (fun u : ℂ ↦ u ^ (-(α + 2) : ℂ)) 1 :=
    continuousAt_cpow_const Complex.one_mem_slitPlane
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨min (δ / 2) (1 / 2), lt_min (half_pos hδ) (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  intro z hz w hw
  have hw' : ‖w‖ < δ := by
    have := (Metric.mem_ball.mp hw)
    simp only [dist_zero_right] at this
    exact (this.trans_le (min_le_left _ _)).trans (half_lt_self hδ)
  have hmul : ‖z * star w‖ < δ := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg w) ((mem_disk_iff z).mp hz).le).trans_lt hw'
  have hbase : dist (1 - z * star w) 1 < δ := by
    simpa [dist_eq_norm] using hmul
  simpa [weightedKernel, dist_eq_norm] using hclose hbase

theorem weightedProjection_indicator_eq_setIntegral (α : ℝ) {s : Set ℂ}
    (hs : MeasurableSet s) (z : ℂ) :
    weightedProjection α (s.indicator (fun _ ↦ (1 : ℂ))) z =
      ∫ w in s, weightedKernel α z w ∂weightedArea α := by
  rw [weightedProjection, ← integral_indicator hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w ↦ by
    by_cases hw : w ∈ s <;> simp [hw]

/-- Averaging a kernel that is close to one keeps the output close to the input mass. -/
theorem norm_weightedProjection_indicator_sub_measure_le {α : ℝ} (hα : -1 < α)
    {s : Set ℂ} (hs : MeasurableSet s) {z : ℂ} (hz : z ∈ disk) {ε : ℝ}
    (hclose : ∀ w ∈ s, ‖weightedKernel α z w - 1‖ ≤ ε) :
    ‖weightedProjection α (s.indicator (fun _ ↦ (1 : ℂ))) z -
      ((weightedArea α).real s : ℂ)‖ ≤ ε * (weightedArea α).real s := by
  let := weightedArea_isProbabilityMeasure α hα
  have hK : Integrable (weightedKernel α z) (weightedArea α) := by
    simpa only [mul_one] using
      integrable_weightedKernel_mul hα (integrable_const (1 : ℂ)) hz
  calc
    _ = ‖∫ w in s, weightedKernel α z w - 1 ∂weightedArea α‖ := by
      rw [integral_sub hK.integrableOn (integrable_const (1 : ℂ)),
        setIntegral_const, weightedProjection_indicator_eq_setIntegral α hs z]
      simp
    _ ≤ ε * (weightedArea α).real s :=
      norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) hclose

/-- Interior concentration gives the universal complex weighted lower bound. -/
theorem one_le_weightedProjection_constant (α : ℝ) (hα : -1 < α) :
    1 ≤ weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) := by
  let := weightedArea_isProbabilityMeasure α hα
  apply le_sInf
  intro C hC
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro t ht ht1
  have ht' : 0 < (t : ℝ) := ht
  have ht1' : (t : ℝ) < 1 := by exact_mod_cast ht1
  have hε : 0 < (1 - (t : ℝ)) / 2 := by linarith
  obtain ⟨r, hr, hr1, hclose⟩ := exists_uniform_weightedKernel_near_one α hε
  let s := Metric.ball (0 : ℂ) r
  let f : ℂ → ℂ := s.indicator (fun _ ↦ 1)
  let m := (weightedArea α).real s
  have hs : MeasurableSet s := Metric.isOpen_ball.measurableSet
  have hspos : 0 < weightedArea α s := weightedArea_ball_pos α hα hr hr1.le
  have hsfinite : weightedArea α s ≠ ∞ := measure_ne_top _ _
  have hm : 0 < m := ENNReal.toReal_pos hspos.ne' hsfinite
  have hf : Integrable f (weightedArea α) := (integrable_const (1 : ℂ)).indicator hs
  have hmass : (∫⁻ w, ‖f w‖ₑ ∂weightedArea α) = weightedArea α s := by
    simp [f, enorm_indicator_eq_indicator_enorm, hs]
  have hsuper : (weightedArea α) {z | ENNReal.ofReal ((t : ℝ) * m) <
      ‖weightedProjection α f z‖ₑ} = 1 := by
    rw [← measure_univ (μ := weightedArea α)]
    apply measure_congr
    filter_upwards [ae_mem_disk_weightedArea α] with z hz
    simp only [Set.mem_univ]
    have herr : ‖weightedProjection α f z - (m : ℂ)‖ ≤
        ((1 - (t : ℝ)) / 2) * m :=
      norm_weightedProjection_indicator_sub_measure_le hα hs hz
        (fun w hw ↦ (hclose z hz w hw).le)
    have hreverse : m - ‖weightedProjection α f z‖ ≤
        ‖weightedProjection α f z - (m : ℂ)‖ := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm, norm_sub_rev] using
        norm_sub_norm_le (m : ℂ) (weightedProjection α f z)
    have hout : (t : ℝ) * m < ‖weightedProjection α f z‖ := by
      nlinarith
    rw [← ofReal_norm]
    exact eq_true ((ENNReal.ofReal_lt_ofReal_iff ((mul_pos ht' hm).trans hout)).mpr hout)
  have hbound := hC f hf ((t : ℝ) * m) (mul_pos ht' hm)
  rw [hsuper, hmass, mul_one, ENNReal.ofReal_mul t.coe_nonneg,
    ENNReal.ofReal_coe_nnreal] at hbound
  have hmcoe : ENNReal.ofReal m = weightedArea α s := ENNReal.ofReal_toReal hsfinite
  rw [hmcoe] at hbound
  exact (ENNReal.mul_le_mul_iff_left hspos.ne' hsfinite).mp hbound

theorem one_le_projection_constant :
    1 ≤ weakTypeConstant diskArea (fun f z ↦ ‖projection f z‖ₑ) := by
  simpa using one_le_weightedProjection_constant 0 (by norm_num)

theorem one_le_positiveProjection_constant :
    1 ≤ weakTypeConstant diskArea positiveProjection :=
  one_le_projection_constant.trans projection_constant_le_positiveProjection_constant

theorem one_le_weightedPositiveProjection_constant (α : ℝ) (hα : -1 < α) :
    1 ≤ weakTypeConstant (weightedArea α) (weightedPositiveProjection α) :=
  (one_le_weightedProjection_constant α hα).trans
    (weightedProjection_constant_le_weightedPositiveProjection_constant α)

end BergmanWeakType
