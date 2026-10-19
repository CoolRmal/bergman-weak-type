/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Measure

/-! # Exact masses of weighted outer annuli -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

theorem weightedArea_norm_gt {α r : ℝ} (hα : -1 < α) (hr : 0 ≤ r) (hr1 : r < 1) :
    weightedArea α {z : ℂ | r < ‖z‖} = ENNReal.ofReal ((1 - r ^ 2) ^ (α + 1)) := by
  have hr₂ : r ^ 2 < 1 := by nlinarith
  have hpre : {z : ℂ | r < ‖z‖} =
      (fun z : ℂ ↦ ‖z‖ ^ 2) ⁻¹' Set.Ioi (r ^ 2) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi]
    exact (sq_lt_sq₀ hr (norm_nonneg z)).symm
  have hm : Measurable (fun u : ℝ ↦ ENNReal.ofReal ((α + 1) * (1 - u) ^ α)) := by
    fun_prop
  rw [hpre, weightedArea, withDensity_apply _ (measurableSet_Ioi.preimage (by fun_prop)),
    ← setLIntegral_map measurableSet_Ioi hm (by fun_prop : Measurable (fun z : ℂ ↦ ‖z‖ ^ 2)),
    map_norm_sq_diskArea, Measure.restrict_restrict measurableSet_Ioi]
  have hset : Set.Ioi (r ^ 2) ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc (r ^ 2) 1 := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨hx, _, hx1⟩
      exact ⟨hx, hx1⟩
    · rintro ⟨hx, hx1⟩
      exact ⟨hx, (sq_nonneg r).trans hx.le, hx1⟩
  rw [hset]
  have hf : IntervalIntegrable (fun u : ℝ ↦ (1 - u) ^ α) volume (r ^ 2) 1 := by
    convert! ((intervalIntegral.intervalIntegrable_rpow'
      (a := 0) (b := 1 - r ^ 2) hα).comp_sub_left 1).symm using 1 <;> ring
  have hfi : IntegrableOn (fun u : ℝ ↦ (α + 1) * (1 - u) ^ α) (Set.Ioc (r ^ 2) 1) :=
    (hf.const_mul (α + 1)).1
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (r ^ 2) 1)]
      (fun u : ℝ ↦ (α + 1) * (1 - u) ^ α) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (sub_nonneg.mpr hu.2) _)
  rw [← ofReal_integral_eq_lintegral_ofReal hfi hnonneg,
    ← intervalIntegral.integral_of_le hr₂.le, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ α) 1]
  simp only [sub_self]
  rw [integral_rpow (Or.inl hα)]
  have hpos : 0 < α + 1 := by linarith
  simp only [Real.zero_rpow hpos.ne', sub_zero]
  rw [mul_div_cancel₀ _ hpos.ne']

theorem weightedArea_outerAnnulus {α r : ℝ} (hα : -1 < α) (hr : 0 ≤ r) (hr1 : r < 1) :
    weightedArea α {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} =
      ENNReal.ofReal ((1 - r ^ 2) ^ (α + 1)) := by
  rw [← weightedArea_norm_gt hα hr hr1]
  apply measure_congr
  filter_upwards [ae_mem_disk_weightedArea α] with z hz
  simp only [(by simpa [disk] using hz : ‖z‖ < 1), and_true]

theorem weightedArea_outerAnnulus_pos {α r : ℝ} (hα : -1 < α) (hr : 0 ≤ r) (hr1 : r < 1) :
    0 < weightedArea α {z : ℂ | r < ‖z‖ ∧ ‖z‖ < 1} := by
  rw [weightedArea_outerAnnulus hα hr hr1]
  apply ENNReal.ofReal_pos.mpr
  exact Real.rpow_pos_of_pos (by nlinarith) _

end BergmanWeakType
