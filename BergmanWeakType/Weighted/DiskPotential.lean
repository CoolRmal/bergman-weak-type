/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.DiskSupermean
public import BergmanWeakType.Weighted.CompactIntegral

/-! # The normalized positive Bergman potential -/

@[expose] public section

noncomputable section

open MeasureTheory Complex
open scoped Topology ENNReal

namespace BergmanWeakType.Weighted

/-- Normalizing the positive Bergman potential by the radial mass. -/
def normalizedPotential (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  ∫ w, normalizedKernel z w * ‖f w‖ ∂diskArea

theorem ae_mem_closedDisk : ∀ᵐ w ∂diskArea, w ∈ Metric.closedBall 0 1 :=
  ae_mem_disk.mono fun _ hw ↦ Metric.ball_subset_closedBall hw

theorem kernel_denominator_ne_zero_closed_input {R : ℝ} (hR : R < 1) {z w : ℂ}
    (hz : z ∈ Metric.closedBall 0 R) (hw : w ∈ Metric.closedBall 0 1) :
    1 - z * star w ≠ 0 := by
  have hz' : ‖z‖ < 1 := (by simpa using hz : ‖z‖ ≤ R).trans_lt hR
  have hw' : ‖w‖ ≤ 1 := by simpa using hw
  have hm : ‖z * star w‖ < 1 := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_right (norm_nonneg _) hw').trans_lt hz'
  intro heq
  have : z * star w = 1 := (sub_eq_zero.mp heq).symm
  rw [this, norm_one] at hm
  exact (lt_irrefl _ hm)

theorem continuousOn_normalizedKernel_cylinder {R : ℝ} (hR : R < 1) :
    ContinuousOn (fun p : ℂ × ℂ ↦ normalizedKernel p.1 p.2)
      (Metric.closedBall 0 R ×ˢ Metric.closedBall 0 1) := by
  have hden : ContinuousOn (fun p : ℂ × ℂ ↦ 1 - p.1 * star p.2)
      (Metric.closedBall 0 R ×ˢ Metric.closedBall 0 1) :=
    (continuous_const.sub (continuous_fst.mul (continuous_star.comp continuous_snd))).continuousOn
  have hinv := hden.inv₀ (fun p hp ↦ kernel_denominator_ne_zero_closed_input hR hp.1 hp.2)
  exact (continuous_const.sub (continuous_fst.norm.pow 2)).continuousOn.mul (hinv.pow 2).norm

theorem integrable_normalizedKernel_mul {f : ℂ → ℂ} (hf : Integrable f diskArea)
    {z : ℂ} (hz : z ∈ disk) :
    Integrable (fun w ↦ normalizedKernel z w * ‖f w‖) diskArea := by
  have hi := ((integrable_kernel_mul hf hz).norm).const_mul (1 - ‖z‖ ^ 2)
  simpa only [normalizedKernel, norm_mul, mul_assoc] using hi

theorem continuousOn_normalizedPotential {f : ℂ → ℂ} (hf : Integrable f diskArea)
    {R : ℝ} (hR : R < 1) :
    ContinuousOn (normalizedPotential f) (Metric.closedBall 0 R) :=
  continuousOn_integral_mul_of_compact (isCompact_closedBall 0 1) ae_mem_closedDisk
    (isCompact_closedBall 0 R) hf.norm (continuousOn_normalizedKernel_cylinder hR)

theorem continuousOn_normalizedPotential_disk {f : ℂ → ℂ} (hf : Integrable f diskArea) :
    ContinuousOn (normalizedPotential f) disk := by
  intro z hz
  have hz' := (mem_disk_iff z).mp hz
  have hR : (‖z‖ + 1) / 2 < 1 := by linarith
  have hzR : z ∈ Metric.ball 0 ((‖z‖ + 1) / 2) := by
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  exact ((continuousOn_normalizedPotential hf hR).continuousAt
    (Metric.closedBall_mem_nhds_of_mem hzR)).continuousWithinAt

theorem normalizedPotential_nonneg {f : ℂ → ℂ} {z : ℂ} (hz : z ∈ disk) :
    0 ≤ normalizedPotential f z := by
  apply integral_nonneg
  intro w
  apply mul_nonneg _ (norm_nonneg _)
  apply mul_nonneg _ (norm_nonneg _)
  have hz' := (mem_disk_iff z).mp hz
  nlinarith [norm_nonneg z]

@[simp] theorem normalizedPotential_zero (f : ℂ → ℂ) :
    normalizedPotential f 0 = ∫ w, ‖f w‖ ∂diskArea := by
  simp [normalizedPotential, normalizedKernel, kernel_zero_left]

theorem normalizedPotential_eq_mul_positiveProjection_toReal {f : ℂ → ℂ}
    (hf : Integrable f diskArea) {z : ℂ} (hz : z ∈ disk) :
    normalizedPotential f z = (1 - ‖z‖ ^ 2) * (positiveProjection f z).toReal := by
  have hi := (integrable_kernel_mul hf hz).norm
  rw [normalizedPotential]
  simp only [normalizedKernel, mul_assoc, integral_const_mul]
  congr 1
  rw [positiveProjection]
  simp only [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun w ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  simpa only [norm_mul] using hi.aestronglyMeasurable

set_option maxHeartbeats 2000000 in
theorem integrable_poisson_normalizedKernel_product {f : ℂ → ℂ}
    (hf : Integrable f diskArea) {R : ℝ} (hR : R < 1) {z : ℂ}
    (hz : z ∈ Metric.ball 0 R) :
    Integrable (fun p : ℝ × ℂ ↦
      (poissonKernel 0 z (circleMap 0 R p.1) * normalizedKernel (circleMap 0 R p.1) p.2) *
        ‖f p.2‖) ((volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod diskArea) := by
  have hR0 : 0 < R := Metric.pos_of_mem_ball hz
  let : IsFiniteMeasure (volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))) :=
    ⟨by simp [Set.uIoc_of_le Real.two_pi_pos.le, ENNReal.mul_lt_top]⟩
  have hs : ∀ θ, circleMap 0 R θ ∈ Metric.closedBall (0 : ℂ) R := by
    intro θ
    exact Metric.sphere_subset_closedBall (by
      simpa only [abs_of_pos hR0] using circleMap_mem_sphere' 0 R θ)
  have hK : IsCompact (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Metric.closedBall (0 : ℂ) 1) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hμ : ∀ᵐ p ∂(volume.restrict (Set.uIoc 0 (2 * Real.pi))).prod diskArea,
      p ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Metric.closedBall (0 : ℂ) 1 := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_Icc.prod Metric.isClosed_closedBall.measurableSet)).mpr
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with θ hθ
    rw [Set.uIoc_of_le Real.two_pi_pos.le] at hθ
    exact ae_mem_closedDisk.mono fun w hw ↦ ⟨Set.Ioc_subset_Icc_self hθ, hw⟩
  apply integrable_mul_of_continuousOn_compact hK hμ
    (hf.norm.comp_snd (volume.restrict (Set.uIoc 0 (2 * Real.pi))))
  have hp : ContinuousOn (fun p : ℝ × ℂ ↦ poissonKernel 0 z (circleMap 0 R p.1))
      (Set.Icc 0 (2 * Real.pi) ×ˢ Metric.closedBall 0 1) :=
    (continuousOn_poisson_circle hz).comp
      ((continuous_circleMap 0 R).comp continuous_fst).continuousOn
      (fun p _ ↦ circleMap_mem_sphere' 0 R p.1)
  have hn : ContinuousOn (fun p : ℝ × ℂ ↦ normalizedKernel (circleMap 0 R p.1) p.2)
      (Set.Icc 0 (2 * Real.pi) ×ˢ Metric.closedBall 0 1) :=
    (continuousOn_normalizedKernel_cylinder hR).comp
      (((continuous_circleMap 0 R).comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun p hp ↦ ⟨hs p.1, hp.2⟩)
  exact hp.mul hn

theorem circleAverage_poisson_normalizedPotential {f : ℂ → ℂ}
    (hf : Integrable f diskArea) {R : ℝ} (hR : R < 1) {z : ℂ}
    (hz : z ∈ Metric.ball 0 R) :
    Real.circleAverage (fun ζ ↦ poissonKernel 0 z ζ * normalizedPotential f ζ) 0 R =
      ∫ w, Real.circleAverage (fun ζ ↦ poissonKernel 0 z ζ * normalizedKernel ζ w) 0 R *
        ‖f w‖ ∂diskArea := by
  have hi := integrable_poisson_normalizedKernel_product hf hR hz
  simp only [Real.circleAverage_def, normalizedPotential, smul_eq_mul]
  simp_rw [← integral_const_mul, ← mul_assoc]
  rw [intervalIntegral_integral_swap hi]
  simp_rw [intervalIntegral.integral_mul_const]
  simp only [mul_assoc]
  rw [integral_const_mul]

/-- The actual normalized potential, for every admissible input, satisfies the Poisson
supermean inequality. -/
theorem normalizedPotential_poisson_supermean {f : ℂ → ℂ}
    (hf : Integrable f diskArea) {R : ℝ} (hR : R < 1) {z : ℂ}
    (hz : z ∈ Metric.ball 0 R) :
    Real.circleAverage (fun ζ ↦ poissonKernel 0 z ζ * normalizedPotential f ζ) 0 R ≤
      normalizedPotential f z := by
  rw [circleAverage_poisson_normalizedPotential hf hR hz, normalizedPotential]
  have hiprod := integrable_poisson_normalizedKernel_product hf hR hz
  have hiavg : Integrable (fun w ↦
      Real.circleAverage (fun ζ ↦ poissonKernel 0 z ζ * normalizedKernel ζ w) 0 R * ‖f w‖)
      diskArea := by
    convert hiprod.integral_prod_right.const_mul ((2 * Real.pi)⁻¹) using 1
    funext w
    simp only [Real.circleAverage_def, smul_eq_mul, integral_mul_const,
      intervalIntegral.integral_of_le Real.two_pi_pos.le, Set.uIoc_of_le Real.two_pi_pos.le]
    ring
  apply integral_mono_ae hiavg
    (integrable_normalizedKernel_mul hf ((mem_disk_iff z).mpr
      ((by simpa using hz : ‖z‖ < R).trans hR)))
  exact ae_mem_disk.mono fun w hw ↦
    mul_le_mul_of_nonneg_right (normalizedKernel_poisson_supermean hR hz hw) (norm_nonneg _)

end BergmanWeakType.Weighted
