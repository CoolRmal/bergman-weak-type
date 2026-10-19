/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.DomainLowerBound
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Compact interior perturbations of the constant input -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BergmanWeakType.Rigidity

/-- Cancellation on a measurable core gives a strict surplus in the positive row integral. -/
theorem norm_integral_add_gap_le_integral_norm {μ : Measure ℂ} {g : ℂ → ℂ}
    {E : Set ℂ} {η : ℝ} (hE : MeasurableSet E) (hg : Integrable g μ)
    (hgap : ‖∫ w in E, g w ∂μ‖ ≤ (1 - η) * ∫ w in E, ‖g w‖ ∂μ) :
    ‖∫ w, g w ∂μ‖ + η * (∫ w in E, ‖g w‖ ∂μ) ≤ ∫ w, ‖g w‖ ∂μ := by
  have hsplit := integral_add_compl hE hg
  have hsplitnorm := integral_add_compl hE hg.norm
  have htriangle := norm_add_le (∫ w in E, g w ∂μ) (∫ w in Eᶜ, g w ∂μ)
  rw [hsplit] at htriangle
  have hcomp := norm_integral_le_integral_norm (μ := μ.restrict Eᶜ) g
  nlinarith

/-- The constant input reduced by `ρ` on the chosen core. -/
def corePerturbation (E : Set ℂ) (ρ : ℝ) (w : ℂ) : ℂ :=
  1 - E.indicator (fun _ ↦ (ρ : ℂ)) w

theorem norm_corePerturbation {E : Set ℂ} {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) (w : ℂ) :
    ‖corePerturbation E ρ w‖ = 1 - E.indicator (fun _ ↦ ρ) w := by
  by_cases hw : w ∈ E
  · simp only [corePerturbation, indicator_of_mem hw]
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (sub_nonneg.mpr hρ.2)]
  · simp [corePerturbation, hw]

theorem integrable_corePerturbation {μ : Measure ℂ} [IsFiniteMeasure μ]
    {E : Set ℂ} (hE : MeasurableSet E) (ρ : ℝ) :
    Integrable (corePerturbation E ρ) μ :=
  (integrable_const (1 : ℂ)).sub ((integrable_const (ρ : ℂ)).indicator hE)

theorem integral_norm_corePerturbation {μ : Measure ℂ} [IsFiniteMeasure μ]
    {E : Set ℂ} (hE : MeasurableSet E) {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    (∫ w, ‖corePerturbation E ρ w‖ ∂μ) = μ.real univ - ρ * μ.real E := by
  simp_rw [norm_corePerturbation hρ]
  rw [integral_sub (integrable_const 1) ((integrable_const ρ).indicator hE),
    integral_indicator hE, integral_const, setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  ring

theorem integrable_norm_mul_corePerturbation {μ : Measure ℂ} {g : ℂ → ℂ}
    {E : Set ℂ} (hE : MeasurableSet E) (hg : Integrable g μ)
    {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    Integrable (fun w ↦ ‖g w‖ * ‖corePerturbation E ρ w‖) μ := by
  have heq : (fun w ↦ ‖g w‖ * ‖corePerturbation E ρ w‖) =
      (fun w ↦ ‖g w‖ - E.indicator (fun w ↦ ρ * ‖g w‖) w) := by
    funext w
    rw [norm_corePerturbation hρ]
    by_cases hw : w ∈ E <;> simp [hw]
    ring
  rw [heq]
  exact hg.norm.sub ((hg.norm.const_mul ρ).indicator hE)

theorem integral_norm_mul_corePerturbation {μ : Measure ℂ} {g : ℂ → ℂ}
    {E : Set ℂ} (hE : MeasurableSet E) (hg : Integrable g μ)
    {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    (∫ w, ‖g w‖ * ‖corePerturbation E ρ w‖ ∂μ) =
      (∫ w, ‖g w‖ ∂μ) - ρ * ∫ w in E, ‖g w‖ ∂μ := by
  have heq : (fun w ↦ ‖g w‖ * ‖corePerturbation E ρ w‖) =
      (fun w ↦ ‖g w‖ - E.indicator (fun w ↦ ρ * ‖g w‖) w) := by
    funext w
    rw [norm_corePerturbation hρ]
    by_cases hw : w ∈ E <;> simp [hw]
    ring
  rw [heq, integral_sub hg.norm ((hg.norm.const_mul ρ).indicator hE),
    integral_indicator hE, integral_const_mul]

/-- A positive-area core with uniform cancellation forces the positive weak constant above one. -/
theorem weakTypeConstant_gt_one_of_core_gap {Ω E : Set ℂ} {K : ℂ → ℂ → ℂ}
    [IsFiniteMeasure (area.restrict Ω)] (hΩ : MeasurableSet Ω)
    (hK : IsBergmanKernel Ω K) (hE : MeasurableSet E) (hsub : E ⊆ Ω)
    (hEpos : 0 < area E) {η : ℝ} (hη : 0 < η) (hηone : η ≤ 1)
    (hgap : ∀ a ∈ Ω, ‖∫ w in E, K a w ∂area‖ ≤
      (1 - η) * ∫ w in E, ‖K a w‖ ∂area) :
    1 < weakTypeConstant (area.restrict Ω) (domainPositiveProjection Ω K) := by
  let μ := area.restrict Ω
  have hre : μ.restrict E = area.restrict E := by
    rw [Measure.restrict_restrict hE, inter_eq_left.mpr hsub]
  have hmeasure : μ E = area E := by
    rw [Measure.restrict_apply hE, inter_eq_left.mpr hsub]
  have hEr : 0 < μ.real E := ENNReal.toReal_pos (by rw [hmeasure]; exact hEpos.ne')
    (measure_ne_top _ _)
  have hf := integrable_corePerturbation (μ := μ) hE η
  apply weakTypeConstant_gt_one_of_witness hf
  · rw [← ofReal_integral_norm_eq_lintegral_enorm hf,
      integral_norm_corePerturbation hE ⟨hη.le, hηone⟩]
    have hlt : μ.real univ - η * μ.real E < μ.real univ :=
      sub_lt_self _ (mul_pos hη hEr)
    have hμpos : 0 < μ.real univ := hEr.trans_le (measureReal_mono (subset_univ E))
    have ho := (ENNReal.ofReal_lt_ofReal_iff hμpos).mpr hlt
    simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using ho
  · filter_upwards [ae_restrict_mem hΩ] with a ha
    have hk : Integrable (K a) μ := (hK.squareIntegrable a ha).integrable (by norm_num)
    have hg : ‖∫ w in E, K a w ∂μ‖ ≤ (1 - η) * ∫ w in E, ‖K a w‖ ∂μ := by
      simpa only [hre] using hgap a ha
    have hs := norm_integral_add_gap_le_integral_norm hE hk hg
    rw [hK.integral_section_eq_one ha, norm_one] at hs
    have hi := integrable_norm_mul_corePerturbation hE hk ⟨hη.le, hηone⟩
    have hout : 1 ≤ ∫ w, ‖K a w‖ * ‖corePerturbation E η w‖ ∂μ := by
      rw [integral_norm_mul_corePerturbation hE hk ⟨hη.le, hηone⟩]
      linarith
    have heq : domainPositiveProjection Ω K (corePerturbation E η) a =
        ENNReal.ofReal (∫ w, ‖K a w‖ * ‖corePerturbation E η w‖ ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun w ↦ mul_nonneg (norm_nonneg _) (norm_nonneg _))]
      simp only [domainPositiveProjection, ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, μ]
    rw [heq]
    exact_mod_cast ENNReal.ofReal_le_ofReal hout

end BergmanWeakType.Rigidity
