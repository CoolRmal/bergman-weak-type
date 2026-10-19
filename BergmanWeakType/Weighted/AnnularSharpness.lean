/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.RadialKernel
public import BergmanWeakType.Weighted.PolarIntegral
public import BergmanWeakType.Weighted.AnnulusMeasure
public import BergmanWeakType.Comparison

/-! # Admissible annular inputs for positive weighted sharpness -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Topology

namespace BergmanWeakType

def outerAnnulus (t : ℝ) : Set ℂ := {w | t < ‖w‖ ∧ ‖w‖ < 1}

theorem measurableSet_outerAnnulus (t : ℝ) : MeasurableSet (outerAnnulus t) := by
  exact (isOpen_lt continuous_const continuous_norm |>.inter
    (isOpen_lt continuous_norm continuous_const)).measurableSet

theorem continuousOn_normalizer_radial (α : ℝ) {z : ℂ} (hz : z ∈ disk) :
    ContinuousOn (fun w : ℂ ↦ normalizer α (‖w‖ * ‖z‖)) disk := by
  apply (continuousOn_normalizer α).comp (by fun_prop)
  intro w hw
  refine ⟨mul_nonneg (norm_nonneg _) (norm_nonneg _), ?_⟩
  have hz' := (mem_disk_iff z).mp hz
  have hw' := (mem_disk_iff w).mp hw
  exact (mul_le_of_le_one_left (norm_nonneg z) hw'.le).trans_lt hz'

theorem integrable_normalizer_radial {α : ℝ} (hα : -1 < α) {z : ℂ} (hz : z ∈ disk) :
    Integrable (fun w : ℂ ↦ normalizer α (‖w‖ * ‖z‖)) (weightedArea α) := by
  let := weightedArea_isProbabilityMeasure α hα
  have hm : AEStronglyMeasurable (fun w : ℂ ↦ normalizer α (‖w‖ * ‖z‖))
      (weightedArea α) :=
    ((continuousOn_normalizer_radial α hz).aestronglyMeasurable
      (μ := area) measurableSet_disk).mono_ac (withDensity_absolutelyContinuous diskArea _)
  apply (integrable_const (normalizer α ‖z‖)).mono' hm
  filter_upwards [ae_mem_disk_weightedArea α] with w hw
  rw [Real.norm_eq_abs, abs_of_nonneg (normalizer_nonneg α _)]
  exact normalizer_mono α (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (mul_le_of_le_one_left (norm_nonneg z) ((mem_disk_iff w).mp hw).le)
    ((mem_disk_iff z).mp hz)

theorem integral_kernel_outerAnnulus_eq_normalizer {α : ℝ} (hα : -1 < α)
    {z : ℂ} (hz : z ∈ disk) (t : ℝ) :
    (∫ w in outerAnnulus t, ‖weightedKernel α z w‖ ∂weightedArea α) =
      ∫ w in outerAnnulus t, normalizer α (‖w‖ * ‖z‖) ∂weightedArea α := by
  let := weightedArea_isProbabilityMeasure α hα
  have hK : Integrable (fun w ↦ ‖weightedKernel α z w‖) (weightedArea α) := by
    simpa only [mul_one] using
      (integrable_weightedKernel_mul hα (integrable_const (1 : ℂ)) hz).norm
  rw [← integral_indicator (measurableSet_outerAnnulus t),
    ← integral_indicator (measurableSet_outerAnnulus t),
    integral_weightedArea_eq_circleAverage hα (hK.indicator (measurableSet_outerAnnulus t)),
    integral_weightedArea_eq_circleAverage hα
      ((integrable_normalizer_radial hα hz).indicator (measurableSet_outerAnnulus t))]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r hr
  dsimp only
  congr 1
  by_cases htr : t < r
  · have hleft : Real.circleAverage
        ((outerAnnulus t).indicator (fun w ↦ ‖weightedKernel α z w‖)) 0 r =
        Real.circleAverage (fun w ↦ ‖weightedKernel α z w‖) 0 r := by
      apply Real.circleAverage_congr_sphere
      intro w hw
      have hw' : ‖w‖ = r := by simpa [abs_of_pos hr.1] using hw
      exact Set.indicator_of_mem (by exact ⟨by rwa [hw'], by rw [hw']; exact hr.2⟩) _
    have hright : Real.circleAverage
        ((outerAnnulus t).indicator (fun w ↦ normalizer α (‖w‖ * ‖z‖))) 0 r =
        normalizer α (r * ‖z‖) := by
      apply Real.circleAverage_const_on_circle
      intro w hw
      have hw' : ‖w‖ = r := by simpa [abs_of_pos hr.1] using hw
      rw [Set.indicator_of_mem (by exact ⟨by rwa [hw'], by rw [hw']; exact hr.2⟩), hw']
    rw [hleft, hright, circleAverage_weightedKernel_norm α z hr.1.le]
  · have heq (g : ℂ → ℝ) : Real.circleAverage ((outerAnnulus t).indicator g) 0 r = 0 := by
      apply Real.circleAverage_const_on_circle
      intro w hw
      have hw' : ‖w‖ = r := by simpa [abs_of_pos hr.1] using hw
      exact Set.indicator_of_notMem (by simpa only [outerAnnulus, Set.mem_ofPred_eq, hw',
        hr.2, and_true] using htr) _
    rw [heq, heq]

theorem normalizer_mul_annulusMass_le_integral {α R t : ℝ} (hα : -1 < α)
    (hR : 0 ≤ R) (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ disk) (hRz : R ≤ ‖z‖) :
    normalizer α (t * R) * (weightedArea α).real (outerAnnulus t) ≤
      ∫ w in outerAnnulus t, ‖weightedKernel α z w‖ ∂weightedArea α := by
  let := weightedArea_isProbabilityMeasure α hα
  rw [integral_kernel_outerAnnulus_eq_normalizer hα hz]
  calc
    _ = ∫ w in outerAnnulus t, normalizer α (t * R) ∂weightedArea α := by
      simp [mul_comm]
    _ ≤ _ := by
      apply integral_mono_ae (integrable_const _) (integrable_normalizer_radial hα hz).integrableOn
      filter_upwards [ae_restrict_mem (measurableSet_outerAnnulus t)] with w hw
      apply normalizer_mono α (mul_nonneg ht hR)
      · exact mul_le_mul hw.1.le hRz hR (norm_nonneg w)
      · exact (mul_le_of_le_one_left (norm_nonneg z) hw.2.le).trans_lt ((mem_disk_iff z).mp hz)

theorem weightedPositiveProjection_outerAnnulus_eq {α : ℝ} (hα : -1 < α)
    {z : ℂ} (hz : z ∈ disk) (t : ℝ) :
    weightedPositiveProjection α ((outerAnnulus t).indicator (fun _ ↦ (1 : ℂ))) z =
      ENNReal.ofReal (∫ w in outerAnnulus t, ‖weightedKernel α z w‖ ∂weightedArea α) := by
  let := weightedArea_isProbabilityMeasure α hα
  have hK : Integrable (fun w ↦ ‖weightedKernel α z w‖) (weightedArea α) := by
    simpa only [mul_one] using
      (integrable_weightedKernel_mul hα (integrable_const (1 : ℂ)) hz).norm
  rw [ofReal_integral_eq_lintegral_ofReal hK.integrableOn
    (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)]
  rw [weightedPositiveProjection, ← lintegral_indicator (measurableSet_outerAnnulus t)]
  apply lintegral_congr
  intro w
  by_cases hw : w ∈ outerAnnulus t <;> simp [hw, ← ofReal_norm]

theorem annular_threshold_le_weakBound {α R t ℓ : ℝ} {C : ℝ≥0∞} (hα : -1 < α)
    (hC : IsWeakTypeBound (weightedArea α) (weightedPositiveProjection α) C)
    (hR : 0 ≤ R) (hR1 : R < 1) (ht : 0 ≤ t) (ht1 : t < 1)
    (hℓ : 0 < ℓ) (hℓJ : ℓ < normalizer α (t * R)) :
    ENNReal.ofReal (ℓ * (1 - R ^ 2) ^ (α + 1)) ≤ C := by
  let := weightedArea_isProbabilityMeasure α hα
  let s := outerAnnulus t
  let f : ℂ → ℂ := s.indicator (fun _ ↦ 1)
  let m := (weightedArea α).real s
  have hs : MeasurableSet s := measurableSet_outerAnnulus t
  have hspos : 0 < weightedArea α s := weightedArea_outerAnnulus_pos hα ht ht1
  have hsfinite : weightedArea α s ≠ ∞ := measure_ne_top _ _
  have hm : 0 < m := ENNReal.toReal_pos hspos.ne' hsfinite
  have hf : Integrable f (weightedArea α) := (integrable_const (1 : ℂ)).indicator hs
  have hmass : (∫⁻ w, ‖f w‖ₑ ∂weightedArea α) = weightedArea α s := by
    simp [f, enorm_indicator_eq_indicator_enorm, hs]
  have hsub : outerAnnulus R ⊆
      {z | ENNReal.ofReal (ℓ * m) < weightedPositiveProjection α f z} := by
    intro z hz
    have hzd : z ∈ disk := (mem_disk_iff z).mpr hz.2
    change ENNReal.ofReal (ℓ * m) <
      weightedPositiveProjection α ((outerAnnulus t).indicator (fun _ ↦ (1 : ℂ))) z
    rw [weightedPositiveProjection_outerAnnulus_eq hα hzd t]
    have hout := (mul_lt_mul_of_pos_right hℓJ hm).trans_le
      (normalizer_mul_annulusMass_le_integral hα hR ht hzd hz.1.le)
    exact (ENNReal.ofReal_lt_ofReal_iff ((mul_pos hℓ hm).trans hout)).mpr hout
  have hbound : ENNReal.ofReal (ℓ * m) * weightedArea α (outerAnnulus R) ≤
      C * weightedArea α s := by
    calc
      _ ≤ ENNReal.ofReal (ℓ * m) *
          weightedArea α {z | ENNReal.ofReal (ℓ * m) < weightedPositiveProjection α f z} := by
        gcongr
      _ ≤ _ := by simpa only [hmass] using hC f hf (ℓ * m) (mul_pos hℓ hm)
  have htail : weightedArea α (outerAnnulus R) =
      ENNReal.ofReal ((1 - R ^ 2) ^ (α + 1)) := weightedArea_outerAnnulus hα hR hR1
  rw [htail,
    ENNReal.ofReal_mul hℓ.le] at hbound
  have hmcoe : ENNReal.ofReal m = weightedArea α s := ENNReal.ofReal_toReal hsfinite
  rw [hmcoe] at hbound
  rw [mul_assoc, mul_comm (weightedArea α s), ← mul_assoc] at hbound
  have hcancel := (ENNReal.mul_le_mul_iff_left hspos.ne' hsfinite).mp hbound
  simpa only [ENNReal.ofReal_mul hℓ.le] using hcancel

theorem annular_normalizer_le_weakBound {α R t : ℝ} {C : ℝ≥0∞} (hα : -1 < α)
    (hC : IsWeakTypeBound (weightedArea α) (weightedPositiveProjection α) C)
    (hR : 0 ≤ R) (hR1 : R < 1) (ht : 0 ≤ t) (ht1 : t < 1) :
    ENNReal.ofReal (normalizer α (t * R) * (1 - R ^ 2) ^ (α + 1)) ≤ C := by
  have htR : |t * R| < 1 := by
    rw [abs_of_nonneg (mul_nonneg ht hR)]
    exact (mul_le_of_le_one_left hR ht1.le).trans_lt hR1
  have hJ := normalizer_pos hα htR
  have hlim : Filter.Tendsto (fun ℓ : ℝ ↦ ENNReal.ofReal (ℓ * (1 - R ^ 2) ^ (α + 1)))
      (𝓝[<] normalizer α (t * R))
      (𝓝 (ENNReal.ofReal (normalizer α (t * R) * (1 - R ^ 2) ^ (α + 1)))) := by
    exact (ENNReal.continuous_ofReal.comp (continuous_id.mul_const _)).continuousAt.tendsto
      |>.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT hJ] with ℓ hℓ
  exact annular_threshold_le_weakBound hα hC hR hR1 ht ht1 hℓ.1 hℓ.2

theorem radialMass_normalizer_le_weakBound {α R : ℝ} {C : ℝ≥0∞} (hα : -1 < α)
    (hC : IsWeakTypeBound (weightedArea α) (weightedPositiveProjection α) C)
    (hR : 0 ≤ R) (hR1 : R < 1) :
    ENNReal.ofReal ((1 - R ^ 2) ^ (α + 1) * normalizer α R) ≤ C := by
  have hnormal : Filter.Tendsto (fun t : ℝ ↦ normalizer α (t * R)) (𝓝[<] 1)
      (𝓝 (normalizer α R)) := by
    apply ((continuousOn_normalizer α) R ⟨hR, hR1⟩).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [id_eq, one_mul] using!
        (continuousAt_id.mul_const R).tendsto.mono_left
          (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
    · filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ht
      exact ⟨mul_nonneg ht.1.le hR, (mul_le_of_le_one_left hR ht.2.le).trans_lt hR1⟩
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (hnormal.const_mul ((1 - R ^ 2) ^ (α + 1)))
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ht
  simpa only [Function.comp_def, mul_comm] using!
    annular_normalizer_le_weakBound hα hC hR hR1 ht.1.le ht.2

/-- Admissible outer-annulus inputs recover the exact positive weighted lower constant. -/
theorem gammaConstant_le_weightedPositiveProjection_constant (α : ℝ) (hα : -1 < α) :
    ENNReal.ofReal (gammaConstant α) ≤
      weakTypeConstant (weightedArea α) (weightedPositiveProjection α) := by
  apply le_sInf
  intro C hC
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_radialMass_mul_normalizer hα)
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with R hR
  exact radialMass_normalizer_le_weakBound hα hC hR.1.le hR.2

end BergmanWeakType
