/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Definitions

/-! # An abstract witness for a weak type constant greater than one

These measure-theoretic lemmas isolate the last step of the positive Bergman rigidity argument.
They do not construct a Bergman witness or prove geometric rigidity.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

/-- An integrable input whose output is at least one almost everywhere gives a lower bound by
the ratio of total measure to input mass. The zero-mass case is included. -/
theorem measure_univ_div_mass_le_weakTypeConstant_of_witness
    {μ : Measure ℂ} {T : (ℂ → ℂ) → ℂ → ℝ≥0∞} {f : ℂ → ℂ}
    (hf : Integrable f μ) (hout : ∀ᵐ z ∂μ, 1 ≤ T f z) :
    μ Set.univ / (∫⁻ z, ‖f z‖ₑ ∂μ) ≤ weakTypeConstant μ T := by
  apply le_sInf
  intro C hC
  apply ENNReal.div_le_of_le_mul
  apply ENNReal.le_of_forall_lt_one_mul_le
  intro a ha
  by_cases ha0 : a = 0
  · simp [ha0]
  have hatop : a ≠ ⊤ := ne_top_of_lt ha
  have hlevel : {z | a < T f z} =ᵐ[μ] Set.univ := by
    filter_upwards [hout] with z hz
    exact propext (iff_true_intro (ha.trans_le hz))
  have hbound := hC f hf a.toReal (ENNReal.toReal_pos ha0 hatop)
  rw [ENNReal.ofReal_toReal hatop, measure_congr hlevel] at hbound
  exact hbound

/-- If an integrable witness has output at least one almost everywhere and input mass smaller
than the total measure, then the sharp weak type constant is strictly greater than one. -/
theorem weakTypeConstant_gt_one_of_witness
    {μ : Measure ℂ} {T : (ℂ → ℂ) → ℂ → ℝ≥0∞} {f : ℂ → ℂ}
    (hf : Integrable f μ) (hmass : (∫⁻ z, ‖f z‖ₑ ∂μ) < μ Set.univ)
    (hout : ∀ᵐ z ∂μ, 1 ≤ T f z) :
    1 < weakTypeConstant μ T := by
  have hratio : (1 : ℝ≥0∞) < μ Set.univ / (∫⁻ z, ‖f z‖ₑ ∂μ) := by
    apply (ENNReal.lt_div_iff_mul_lt (Or.inr ENNReal.one_ne_top) (Or.inr one_ne_zero)).2
    simpa only [one_mul] using hmass
  exact hratio.trans_le (measure_univ_div_mass_le_weakTypeConstant_of_witness hf hout)

end BergmanWeakType
