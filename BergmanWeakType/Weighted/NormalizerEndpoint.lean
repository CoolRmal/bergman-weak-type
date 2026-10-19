/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.Normalizer
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The sharp bound and endpoint limit of the weighted circular normalizer -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BergmanWeakType

theorem circleIntegrable_boundaryPower {α : ℝ} (hα : -1 < α) :
    CircleIntegrable (fun ζ : ℂ ↦ ‖1 - ζ‖ ^ α) 0 1 := by
  by_contra hn
  have h := Real.circleAverage.integral_undef hn
  rw [circleAverage_boundary_power hα] at h
  exact (gammaConstant_pos hα).ne' h

theorem boundary_circleDenominator_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    0 < circleDenominator 1 (Real.cos θ) := by
  have hs : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hn : ‖1 - circleMap 0 1 θ‖ = 2 * Real.sin (θ / 2) := by
    rw [circleMap, zero_add, Complex.ofReal_one, one_mul, norm_sub_rev,
      mul_comm (θ : ℂ) Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one,
      Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) hs)]
  rw [← norm_boundaryKernel_circleMap_sq]
  simpa only [Complex.ofReal_one, one_mul, hn] using sq_pos_of_pos (mul_pos (by norm_num) hs)

theorem tendsto_circleAverage_boundaryPower_neg {α : ℝ} (hα : -1 < α) (hα0 : α < 0) :
    Tendsto (fun r : ℝ ↦ Real.circleAverage (fun ζ : ℂ ↦ ‖1 - (r : ℂ) * ζ‖ ^ α) 0 1)
      (𝓝[<] 1) (𝓝 (gammaConstant α)) := by
  let F : ℝ → ℝ → ℝ := fun r θ ↦ circleDenominator r (Real.cos θ) ^ (α / 2)
  have hi : IntervalIntegrable (F 1) volume 0 (2 * Real.pi) := by
    have h := circleIntegrable_boundaryPower hα
    change IntervalIntegrable (fun θ ↦ ‖1 - circleMap 0 1 θ‖ ^ α) volume 0 (2 * Real.pi) at h
    simpa only [F, ← norm_boundaryKernel_circleMap_rpow, Complex.ofReal_one, one_mul] using h
  have hb : ∀ᶠ r : ℝ in 𝓝[<] 1, r ∈ Set.Ioo (1 / 2 : ℝ) 1 :=
    Ioo_mem_nhdsLT (by norm_num)
  have hlim : Tendsto (fun r ↦ ∫ θ in (0 : ℝ)..2 * Real.pi, F r θ)
      (𝓝[<] 1) (𝓝 (∫ θ in (0 : ℝ)..2 * Real.pi, F 1 θ)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun θ ↦ (1 / 2 : ℝ) ^ (α / 2) * F 1 θ)
    · filter_upwards [hb] with r hr
      have hc : Continuous (F r) := by
        apply Continuous.rpow_const (by dsimp [circleDenominator]; fun_prop)
        intro θ
        left
        apply (circleDenominator_pos (r := r) (by rw [abs_of_pos (by linarith [hr.1])]; exact hr.2)
          ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩).ne'
      exact hc.aestronglyMeasurable
    · filter_upwards [hb] with r hr
      filter_upwards [show ∀ᵐ θ : ℝ, θ ≠ 2 * Real.pi by rw [ae_iff]; simp] with θ hθ
      intro hθmem
      have hθ' : θ ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) := by
        simp only [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi), Set.mem_Ioc] at hθmem
        exact ⟨hθmem.1, lt_of_le_of_ne hθmem.2 hθ⟩
      have hd := boundary_circleDenominator_pos hθ'
      have he : (1 / 2 : ℝ) * circleDenominator 1 (Real.cos θ) ≤
          circleDenominator r (Real.cos θ) := by
        have hmul := mul_nonneg (by linarith [hr.1] : 0 ≤ 2 * r - 1)
          (sub_nonneg.mpr (Real.cos_le_one θ))
        unfold circleDenominator
        nlinarith [sq_nonneg (1 - r)]
      dsimp only [F]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by
        linarith [mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hd]) _)]
      simpa only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) hd.le] using
        Real.rpow_le_rpow_of_nonpos (mul_pos (by norm_num) hd) he (by linarith)
    · exact hi.const_mul _
    · filter_upwards [show ∀ᵐ θ : ℝ, θ ≠ 2 * Real.pi by rw [ae_iff]; simp] with θ hθ
      intro hθmem
      have hθ' : θ ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) := by
        simp only [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi), Set.mem_Ioc] at hθmem
        exact ⟨hθmem.1, lt_of_le_of_ne hθmem.2 hθ⟩
      have hc : ContinuousAt (fun r ↦ F r θ) 1 :=
        (show ContinuousAt (fun r ↦ circleDenominator r (Real.cos θ)) 1 by
          dsimp [circleDenominator]; fun_prop).rpow_const
          (Or.inl (boundary_circleDenominator_pos hθ').ne')
      exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have havg := hlim.const_mul (2 * Real.pi)⁻¹
  have heq : ∀ r : ℝ, Real.circleAverage (fun ζ : ℂ ↦ ‖1 - (r : ℂ) * ζ‖ ^ α) 0 1 =
      (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..2 * Real.pi, F r θ) := by
    intro r
    simp only [Real.circleAverage_def, norm_boundaryKernel_circleMap_rpow, smul_eq_mul, F]
  simp_rw [← heq] at havg
  simpa only [Complex.ofReal_one, one_mul, circleAverage_boundary_power hα] using havg

theorem circleAverage_boundaryPower_eq_radius (α r : ℝ) :
    Real.circleAverage (fun ζ : ℂ ↦ ‖1 - (r : ℂ) * ζ‖ ^ α) 0 1 =
      Real.circleAverage (fun z : ℂ ↦ ‖1 - z‖ ^ α) 0 r := by
  simpa only [add_zero] using
    (Real.circleAverage_eq_circleAverage_zero_one
      (f := fun z : ℂ ↦ ‖1 - z‖ ^ α) (c := 0) (R := r)).symm

theorem tendsto_circleAverage_boundaryPower {α : ℝ} (hα : -1 < α) :
    Tendsto (fun r : ℝ ↦ Real.circleAverage (fun ζ : ℂ ↦ ‖1 - (r : ℂ) * ζ‖ ^ α) 0 1)
      (𝓝[<] 1) (𝓝 (gammaConstant α)) := by
  by_cases hα0 : 0 ≤ α
  · have hc : Continuous (fun z : ℂ ↦ ‖1 - z‖ ^ α) :=
      (continuous_const.sub continuous_id).norm.rpow_const fun _ ↦ Or.inr hα0
    have hlim := (Real.Continuous.circleAverage (c := 0) hc).continuousAt.tendsto
      |>.mono_left (show 𝓝[<] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds)
    rw [circleAverage_boundary_power hα] at hlim
    simpa only [circleAverage_boundaryPower_eq_radius] using hlim
  · exact tendsto_circleAverage_boundaryPower_neg hα (lt_of_not_ge hα0)

theorem circleAverage_boundaryPower_le_gammaConstant {α r : ℝ}
    (hα : -1 < α) (hr : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage (fun ζ : ℂ ↦ ‖1 - (r : ℂ) * ζ‖ ^ α) 0 1 ≤ gammaConstant α := by
  apply ge_of_tendsto (tendsto_circleAverage_boundaryPower hα)
  filter_upwards [Ioo_mem_nhdsLT hr1] with R hR
  simp only [circleAverage_boundaryPower_eq_radius]
  exact circleAverage_boundaryPower_mono α hr hR.1.le hR.2

/-- The sharp radial estimate used by the weighted weak-type upper bound. -/
theorem radialMass_mul_normalizer_le {α r : ℝ}
    (hα : -1 < α) (hr : 0 ≤ r) (hr1 : r < 1) :
    (1 - r ^ 2) ^ (α + 1) * normalizer α r ≤ gammaConstant α := by
  rw [radialMass_mul_normalizer α (by simpa only [abs_of_nonneg hr] using hr1)]
  exact circleAverage_boundaryPower_le_gammaConstant hα hr hr1

theorem tendsto_radialMass_mul_normalizer {α : ℝ} (hα : -1 < α) :
    Tendsto (fun r : ℝ ↦ (1 - r ^ 2) ^ (α + 1) * normalizer α r)
      (𝓝[<] 1) (𝓝 (gammaConstant α)) := by
  apply (tendsto_circleAverage_boundaryPower hα).congr'
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with r hr
  exact (radialMass_mul_normalizer α (by simpa only [abs_of_pos hr.1] using hr.2)).symm

theorem normalizer_le_gammaConstant_div {α r : ℝ}
    (hα : -1 < α) (hr : 0 ≤ r) (hr1 : r < 1) :
    normalizer α r ≤ gammaConstant α / (1 - r ^ 2) ^ (α + 1) := by
  have hd : 0 < 1 - r ^ 2 := by nlinarith
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hd _)).mpr
  simpa only [mul_comm] using radialMass_mul_normalizer_le hα hr hr1

end BergmanWeakType
