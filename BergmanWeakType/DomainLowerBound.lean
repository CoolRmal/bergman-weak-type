/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Domain
public import BergmanWeakType.RigidityWitness

/-! # The universal positive Bergman weak lower bound

On a domain of finite positive area, the reproducing property of the actual Bergman kernel
gives the weak type lower bound one. This is separate from strictness on nondisks.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

variable {Ω : Set ℂ} {K : ℂ → ℂ → ℂ} [IsFiniteMeasure (area.restrict Ω)]

/-- A Bergman kernel on a finite-area domain reproduces the constant function one. -/
theorem IsBergmanKernel.integral_section_eq_one (hK : IsBergmanKernel Ω K)
    {z : ℂ} (hz : z ∈ Ω) :
    (∫ w, K z w ∂area.restrict Ω) = 1 := by
  simpa only [mul_one] using
    hK.reproduces (fun _ ↦ 1) (differentiableOn_const 1) (memLp_const 1) z hz

/-- The positive Bergman image of the constant input is at least one on the domain. -/
theorem IsBergmanKernel.one_le_positiveProjection_one (hK : IsBergmanKernel Ω K)
    {z : ℂ} (hz : z ∈ Ω) :
    1 ≤ domainPositiveProjection Ω K (fun _ ↦ 1) z := by
  have hnorm := enorm_integral_le_lintegral_enorm (μ := area.restrict Ω) (fun w ↦ K z w)
  rw [hK.integral_section_eq_one hz] at hnorm
  simpa [domainPositiveProjection, ← ofReal_norm] using hnorm

/-- Every Bergman kernel on a measurable domain of finite positive area has positive weak
type constant at least one. Simple connectivity and boundary regularity are not needed. -/
theorem IsBergmanKernel.one_le_weakTypeConstant (hK : IsBergmanKernel Ω K)
    (hΩ : MeasurableSet Ω) (harea : area Ω ≠ 0) :
    1 ≤ weakTypeConstant (area.restrict Ω) (domainPositiveProjection Ω K) := by
  have hout : ∀ᵐ z ∂area.restrict Ω, 1 ≤ domainPositiveProjection Ω K (fun _ ↦ 1) z := by
    filter_upwards [ae_restrict_mem hΩ] with z hz
    exact hK.one_le_positiveProjection_one hz
  have huniv : (area.restrict Ω) Set.univ ≠ 0 := by simpa using harea
  have hfinite : (area.restrict Ω) Set.univ ≠ ⊤ := measure_ne_top _ _
  have hratio := measure_univ_div_mass_le_weakTypeConstant_of_witness
    (integrable_const (1 : ℂ)) hout
  simpa only [enorm_one, lintegral_const, one_mul, ENNReal.div_self huniv hfinite] using hratio

end BergmanWeakType
