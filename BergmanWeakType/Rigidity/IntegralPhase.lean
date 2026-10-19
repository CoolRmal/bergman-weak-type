/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Definitions
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

open Set MeasureTheory Filter
open scoped ComplexConjugate

namespace BergmanWeakType

instance area_isFiniteMeasureOnCompacts : IsFiniteMeasureOnCompacts area :=
  IsFiniteMeasureOnCompacts.smul volume ENNReal.ofReal_ne_top

instance area_isOpenPosMeasure : Measure.IsOpenPosMeasure area :=
  Measure.isOpenPosMeasure_smul volume (by positivity)

/-- Equality in the integral triangle inequality forces a single complex phase almost everywhere. -/
theorem im_div_integral_eq_zero_ae {μ : Measure ℂ} {f : ℂ → ℂ} (hf : Integrable f μ)
    (hne : (∫ z, f z ∂μ) ≠ 0)
    (heq : ‖∫ z, f z ∂μ‖ = ∫ z, ‖f z‖ ∂μ) :
    ∀ᵐ z ∂μ, (f z / (∫ w, f w ∂μ)).im = 0 := by
  let c := ∫ z, f z ∂μ
  let g : ℂ → ℂ := fun z ↦ f z / c
  have hg : Integrable g μ := hf.div_const c
  have hgint : (∫ z, g z ∂μ) = 1 := by
    rw [show g = fun z ↦ f z / c from rfl, integral_div, div_self hne]
  have hgnorm : (∫ z, ‖g z‖ ∂μ) = 1 := by
    simp only [g, norm_div]
    rw [integral_div, ← heq, div_self (norm_ne_zero_iff.mpr hne)]
  have hreal : (fun z ↦ (g z).re) =ᵐ[μ] (fun z ↦ ‖g z‖) := by
    apply (integral_eq_iff_of_ae_le hg.re hg.norm
      (Eventually.of_forall fun z ↦ Complex.re_le_norm (g z))).mp
    rw [integral_re hg, hgint, hgnorm]
    rfl
  filter_upwards [hreal] with z hz
  apply Complex.abs_re_eq_norm.mp
  rw [hz, abs_of_nonneg (norm_nonneg _)]

/-- On an open set, continuity upgrades the almost-everywhere phase identity to pointwise. -/
theorem im_div_integral_eq_zero_on {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U)
    (hf : ContinuousOn f U) (hfi : Integrable f (area.restrict U))
    (hne : (∫ z in U, f z ∂area) ≠ 0)
    (heq : ‖∫ z in U, f z ∂area‖ = ∫ z in U, ‖f z‖ ∂area) :
    ∀ z ∈ U, (f z / (∫ w in U, f w ∂area)).im = 0 := by
  have hae := im_div_integral_eq_zero_ae hfi hne heq
  have hae' : (fun z ↦ (f z / (∫ w in U, f w ∂area)).im) =ᵐ[volume.restrict U]
      (fun _ ↦ (0 : ℝ)) := by
    change ∀ᵐ z ∂volume.restrict U, (f z / (∫ w in U, f w ∂area)).im = 0
    simpa only [area, Measure.restrict_smul,
      Measure.ae_ennreal_smul_measure_eq (by positivity : ENNReal.ofReal Real.pi⁻¹ ≠ 0)] using hae
  exact Measure.eqOn_open_of_ae_eq hae' hU
    (Complex.continuous_im.comp_continuousOn (hf.div_const _)) continuousOn_const

end BergmanWeakType
