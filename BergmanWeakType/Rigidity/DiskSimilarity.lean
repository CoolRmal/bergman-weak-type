/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.DomainGap
public import BergmanWeakType.DiskSharp
public import BergmanWeakType.DomainLowerBound

@[expose] public section

noncomputable section

open Set MeasureTheory Metric Filter
open scoped ComplexConjugate Topology ENNReal

namespace BergmanWeakType

/-- A nondegenerate complex affine map, as a measurable equivalence. -/
def affineMeasurableEquiv (a b : ℂ) (hb : b ≠ 0) : ℂ ≃ᵐ ℂ where
  toFun w := a + b * w
  invFun z := (z - a) / b
  left_inv w := by field_simp; ring
  right_inv z := by field_simp; ring
  measurable_toFun := by change Measurable (fun w : ℂ ↦ a + b * w); fun_prop
  measurable_invFun := by change Measurable (fun z : ℂ ↦ (z - a) / b); fun_prop

theorem hasDerivAt_affine (a b w : ℂ) :
    HasDerivAt (fun z : ℂ ↦ a + b * z) b w := by
  convert ((hasDerivAt_id w).const_mul b).const_add a using 1
  · rfl
  · simp

theorem deriv_affine (a b w : ℂ) : deriv (fun z : ℂ ↦ a + b * z) w = b :=
  (hasDerivAt_affine a b w).deriv

theorem affine_bijOn_disk (a b : ℂ) (hb : b ≠ 0) :
    BijOn (fun w ↦ a + b * w) disk (ball a ‖b‖) := by
  rw [← image_affine_disk hb]
  exact (affineMeasurableEquiv a b hb).injective.injOn.bijOn_image

/-- Area under a complex similarity changes by the squared modulus of its multiplier. -/
theorem area_restrict_ball_eq_affine_map (a b : ℂ) (hb : b ≠ 0) :
    area.restrict (ball a ‖b‖) = ENNReal.ofReal (‖b‖ ^ 2) •
      Measure.map (affineMeasurableEquiv a b hb) diskArea := by
  let e := affineMeasurableEquiv a b hb
  have he : DifferentiableOn ℂ e disk := fun w _ ↦
    (hasDerivAt_affine a b w).differentiableAt.differentiableWithinAt
  have himage : e '' disk = ball a ‖b‖ := image_affine_disk hb
  have hederiv (w : ℂ) : deriv e w = b := deriv_affine a b w
  ext S hS
  rw [Measure.smul_apply, smul_eq_mul, e.map_apply]
  calc
    (area.restrict (ball a ‖b‖)) S =
        ∫⁻ w in e '' disk, S.indicator (fun _ ↦ (1 : ℝ≥0∞)) w ∂area := by
      rw [himage]
      simpa using (lintegral_indicator_const (μ := area.restrict (ball a ‖b‖)) hS 1).symm
    _ = ∫⁻ w in disk, ENNReal.ofReal (‖b‖ ^ 2) *
        S.indicator (fun _ ↦ (1 : ℝ≥0∞)) (e w) ∂area := by
      rw [area_lintegral_image_eq (U := disk) isOpen_ball he
        (affine_bijOn_disk a b hb).injOn]
      apply lintegral_congr
      intro w
      rw [hederiv]
    _ = ENNReal.ofReal (‖b‖ ^ 2) * diskArea (e ⁻¹' S) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      change (∫⁻ w, S.indicator (fun _ ↦ (1 : ℝ≥0∞)) (e w) ∂diskArea) = _
      rw [← lintegral_indicator_one (e.measurable hS)]
      apply lintegral_congr
      intro w
      by_cases hw : e w ∈ S <;> simp [hw]

/-- The positive Bergman operator commutes with similarities after pulling back its input. -/
theorem IsBergmanKernel.positiveProjection_affine {a b : ℂ} (hb : b ≠ 0)
    {K : ℂ → ℂ → ℂ} (hK : IsBergmanKernel (ball a ‖b‖) K)
    (f : ℂ → ℂ) {z : ℂ} (hz : z ∈ disk) :
    domainPositiveProjection (ball a ‖b‖) K f (a + b * z) =
      positiveProjection (fun w ↦ f (a + b * w)) z := by
  let e := affineMeasurableEquiv a b hb
  have he : DifferentiableOn ℂ e disk := fun w _ ↦
    (hasDerivAt_affine a b w).differentiableAt.differentiableWithinAt
  have hbij : BijOn e disk (ball a ‖b‖) := affine_bijOn_disk a b hb
  have hinv : InvOn e.symm e disk (ball a ‖b‖) :=
    ⟨fun _ _ ↦ e.symm_apply_apply _, fun _ _ ↦ e.apply_symm_apply _⟩
  have heinv : DifferentiableOn ℂ e.symm (ball a ‖b‖) :=
    differentiableOn_inverse isOpen_ball isOpen_ball he hinv
      (hinv.1.mapsTo hbij.surjOn)
  have hederiv (w : ℂ) : deriv e w = b := deriv_affine a b w
  have hcoef {w : ℂ} (hw : w ∈ disk) :
      ENNReal.ofReal (‖b‖ ^ 2) * ENNReal.ofReal ‖K (e z) (e w)‖ =
        ENNReal.ofReal ‖kernel z w‖ := by
    have hk := hK.disk_coordinate_formula isOpen_ball he heinv hbij hinv hz hw
    rw [hederiv, hederiv] at hk
    have hreal : ‖b‖ ^ 2 * ‖K (e z) (e w)‖ = ‖kernel z w‖ := by
      rw [hk, norm_div, norm_mul, norm_star]
      field_simp
    simpa only [ENNReal.ofReal_mul (sq_nonneg ‖b‖)] using congrArg ENNReal.ofReal hreal
  change (∫⁻ w, ENNReal.ofReal ‖K (e z) w‖ * ‖f w‖ₑ
    ∂area.restrict (ball a ‖b‖)) = _
  rw [area_restrict_ball_eq_affine_map a b hb, lintegral_smul_measure,
    e.measurableEmbedding.lintegral_map, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [ae_mem_disk] with w hw
  rw [← mul_assoc, hcoef hw]
  rfl

/-- The sharp positive weak type bound is unchanged by translation, rotation, and dilation. -/
theorem IsBergmanKernel.isWeakTypeBound_affine_one {a b : ℂ} (hb : b ≠ 0)
    {K : ℂ → ℂ → ℂ} (hK : IsBergmanKernel (ball a ‖b‖) K) :
    IsWeakTypeBound (area.restrict (ball a ‖b‖))
      (domainPositiveProjection (ball a ‖b‖) K) 1 := by
  let e := affineMeasurableEquiv a b hb
  let c := ENNReal.ofReal (‖b‖ ^ 2)
  have hc : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hb))
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hμ : area.restrict (ball a ‖b‖) = c • Measure.map e diskArea :=
    area_restrict_ball_eq_affine_map a b hb
  intro f hf t ht
  have hfmap : Integrable f (Measure.map e diskArea) := by
    rw [hμ] at hf
    exact (integrable_smul_measure hc hct).mp hf
  have hfi : Integrable (fun w ↦ f (a + b * w)) diskArea :=
    (e.measurableEmbedding.integrable_map_iff).mp hfmap
  have hbound := isWeakTypeBound_positiveProjection_one _ hfi t ht
  have hlevel : diskArea (e ⁻¹' {z | ENNReal.ofReal t <
      domainPositiveProjection (ball a ‖b‖) K f z}) =
      diskArea {z | ENNReal.ofReal t < positiveProjection (fun w ↦ f (a + b * w)) z} := by
    apply measure_congr
    filter_upwards [ae_mem_disk] with w hw
    simp only [mem_preimage, mem_ofPred_eq]
    rw [show e w = a + b * w from rfl, hK.positiveProjection_affine hb f hw]
  rw [hμ, Measure.smul_apply, smul_eq_mul, e.map_apply, hlevel,
    lintegral_smul_measure, e.measurableEmbedding.lintegral_map, one_mul]
  simp only [one_mul] at hbound
  rw [smul_eq_mul, ← mul_assoc, mul_comm (ENNReal.ofReal t) c, mul_assoc]
  convert mul_le_mul_right hbound c using 1
  rfl

/-- Every Euclidean disk has positive Bergman weak type constant one. -/
theorem weakTypeConstant_domainPositiveProjection_ball_eq_one (a : ℂ) {R : ℝ} (hR : 0 < R)
    {K : ℂ → ℂ → ℂ} (hK : IsBergmanKernel (ball a R) K) :
    weakTypeConstant (area.restrict (ball a R)) (domainPositiveProjection (ball a R) K) = 1 := by
  have hnorm : ‖(R : ℂ)‖ = R := by simp [abs_of_pos hR]
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have : IsFiniteMeasure (area.restrict (ball a R)) :=
    isFiniteMeasure_restrict.mpr isBounded_ball.measure_lt_top.ne
  apply le_antisymm
  · apply weakTypeConstant_le_of_bound
    have hK' : IsBergmanKernel (ball a ‖(R : ℂ)‖) K := by simpa only [hnorm] using hK
    simpa only [hnorm] using hK'.isWeakTypeBound_affine_one hRne
  · exact hK.one_le_weakTypeConstant isOpen_ball.measurableSet
      (measure_ball_pos area a hR).ne'

end BergmanWeakType
