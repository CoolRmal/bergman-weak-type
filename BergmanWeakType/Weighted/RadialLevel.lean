/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.DiskCap

/-! # Distribution estimates from increasing truncations in a radial mass coordinate -/

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Set
open scoped Topology

namespace BergmanWeakType.Weighted

def radialCapMean (U : ℂ → ℝ) (ρ : ℝ → ℝ) (y c : ℝ) : ℝ :=
  circleAverage (fun z ↦ min (U z) c) 0 (ρ y)

def radialLevelFraction (U : ℂ → ℝ) (ρ : ℝ → ℝ) (t y : ℝ) : ℝ :=
  circleAverage (fun z ↦ if t * y < U z then (1 : ℝ) else 0) 0 (ρ y)

theorem circleIntegrable_radialLevel {U : ℂ → ℝ} (hU : Measurable U) (t y r : ℝ) :
    CircleIntegrable (fun z ↦ if t * y < U z then (1 : ℝ) else 0) 0 r := by
  apply circleIntegrable_of_measurable_bounded
    (measurable_const.ite (measurableSet_lt measurable_const hU) measurable_const) (M := 1) _ r
  intro z
  split_ifs <;> norm_num

theorem circleIntegrable_radialCap {U : ℂ → ℝ} (hU : Measurable U)
    (hUpos : ∀ z, 0 ≤ U z) (c r : ℝ) :
    CircleIntegrable (fun z ↦ min (U z) c) 0 r := by
  apply circleIntegrable_of_measurable_bounded (hU.inf measurable_const) (M := |c|) _ r
  intro z
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_min ((neg_nonpos.mpr (abs_nonneg c)).trans (hUpos z)) (neg_abs_le c),
    (min_le_right _ _).trans (le_abs_self c)⟩

theorem radialLevelFraction_mem_Icc {U : ℂ → ℝ} (hU : Measurable U)
    (ρ : ℝ → ℝ) (t y : ℝ) : radialLevelFraction U ρ t y ∈ Icc (0 : ℝ) 1 := by
  constructor
  · apply circleAverage_nonneg_of_nonneg
    intro z _
    split_ifs <;> norm_num
  · apply circleAverage_mono_on_of_le_circle (circleIntegrable_radialLevel hU t y _)
    intro z _
    split_ifs <;> norm_num

theorem measurable_radialLevelFraction {U : ℂ → ℝ} (hU : Measurable U)
    {ρ : ℝ → ℝ} (hρ : Measurable ρ) (t : ℝ) :
    Measurable (radialLevelFraction U ρ t) := by
  have hpoint : Measurable (fun p : ℝ × ℝ ↦ circleMap 0 (ρ p.1) p.2) :=
    circleMap.continuous.measurable.comp ((hρ.comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun p : ℝ × ℝ ↦ if t * p.1 < U (circleMap 0 (ρ p.1) p.2)
      then (1 : ℝ) else 0) := measurable_const.ite
    (measurableSet_lt (measurable_const.mul measurable_fst) (hU.comp hpoint)) measurable_const
  have hi := hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) (2 * π)))
  change Measurable (fun y ↦ radialLevelFraction U ρ t y)
  simp only [radialLevelFraction, circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le two_pi_pos.le]
  exact measurable_const.mul hi.measurable

theorem integrableOn_radialLevelFraction {U : ℂ → ℝ} (hU : Measurable U)
    {ρ : ℝ → ℝ} (hρ : Measurable ρ) (t : ℝ) :
    IntegrableOn (radialLevelFraction U ρ t) (Icc (0 : ℝ) 1) := by
  apply Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
    (measurable_radialLevelFraction hU hρ t).aestronglyMeasurable (M := 1)
  exact Filter.Eventually.of_forall fun y ↦ by
    rw [Real.norm_of_nonneg (radialLevelFraction_mem_Icc hU ρ t y).1]
    exact (radialLevelFraction_mem_Icc hU ρ t y).2

theorem radialCapMean_nonneg {U : ℂ → ℝ} (hUpos : ∀ z, 0 ≤ U z)
    (ρ : ℝ → ℝ) (y : ℝ) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ radialCapMean U ρ y c := by
  apply circleAverage_nonneg_of_nonneg
  exact fun z _ ↦ le_min (hUpos z) hc

theorem radialCapMean_le_level {U : ℂ → ℝ} (hU : Measurable U)
    (hUpos : ∀ z, 0 ≤ U z) (ρ : ℝ → ℝ) (y c : ℝ) : radialCapMean U ρ y c ≤ c := by
  apply circleAverage_mono_on_of_le_circle (circleIntegrable_radialCap hU hUpos c _)
  exact fun _ _ ↦ min_le_right _ _

theorem measurable_radialCapMean_diagonal {U : ℂ → ℝ} (hU : Measurable U)
    {ρ : ℝ → ℝ} (hρ : Measurable ρ) (t : ℝ) :
    Measurable (fun y ↦ radialCapMean U ρ y (t * y)) := by
  have hpoint : Measurable (fun p : ℝ × ℝ ↦ circleMap 0 (ρ p.1) p.2) :=
    circleMap.continuous.measurable.comp ((hρ.comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun p : ℝ × ℝ ↦ min (U (circleMap 0 (ρ p.1) p.2)) (t * p.1)) :=
    (hU.comp hpoint).inf (measurable_const.mul measurable_fst)
  have hi := hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) (2 * π)))
  simp only [radialCapMean, circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le two_pi_pos.le]
  exact measurable_const.mul hi.measurable

theorem integrableOn_radialCapMean_diagonal {U : ℂ → ℝ} (hU : Measurable U)
    (hUpos : ∀ z, 0 ≤ U z) {ρ : ℝ → ℝ} (hρ : Measurable ρ)
    {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun y ↦ radialCapMean U ρ y (t * y)) (Icc (0 : ℝ) 1) := by
  apply Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
    (measurable_radialCapMean_diagonal hU hρ t).aestronglyMeasurable (M := t)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  rw [Real.norm_of_nonneg (radialCapMean_nonneg hUpos ρ y (mul_nonneg ht hy.1))]
  exact (radialCapMean_le_level hU hUpos ρ y _).trans (mul_le_of_le_one_right ht hy.2)

theorem radialCapMean_increment {U : ℂ → ℝ} (hU : Measurable U)
    (hUpos : ∀ z, 0 ≤ U z) (ρ : ℝ → ℝ) (t y : ℝ) {c : ℝ} (hc : c ≤ t * y) :
    (t * y - c) * radialLevelFraction U ρ t y ≤
      radialCapMean U ρ y (t * y) - radialCapMean U ρ y c := by
  have hiL : CircleIntegrable
      (fun z ↦ (t * y - c) • (if t * y < U z then (1 : ℝ) else 0)) 0 (ρ y) :=
    (circleIntegrable_radialLevel hU t y _).const_smul
  have hiR := (circleIntegrable_radialCap hU hUpos (t * y) (ρ y)).sub
    (circleIntegrable_radialCap hU hUpos c (ρ y))
  have hpoint (z : ℂ) : (t * y - c) • (if t * y < U z then (1 : ℝ) else 0) ≤
      min (U z) (t * y) - min (U z) c := by
    by_cases hz : t * y < U z
    · rw [ite_eq_left hz, smul_eq_mul, mul_one, min_eq_right hz.le,
        min_eq_right (hc.trans hz.le)]
    · rw [ite_eq_right hz, smul_eq_mul, mul_zero]
      exact sub_nonneg.mpr (min_le_min_left _ hc)
  have havg := circleAverage_mono hiL hiR (fun z _ ↦ hpoint z)
  rw [circleAverage_fun_smul, circleAverage_sub
    (circleIntegrable_radialCap hU hUpos (t * y) _) (circleIntegrable_radialCap hU hUpos c _)] at havg
  exact havg

/-- Increasing cap means in the mass coordinate give the integrated level-set estimate. -/
theorem integral_mul_radialLevelFraction_le {U : ℂ → ℝ} (hU : Measurable U)
    (hUpos : ∀ z, 0 ≤ U z) {ρ : ℝ → ℝ} (hρ : Measurable ρ) {M : ℝ}
    (hmono : ∀ c, MonotoneOn (fun y ↦ radialCapMean U ρ y c) (Ioo 0 1))
    (hbound : ∀ y ∈ Ioo (0 : ℝ) 1, ∀ c, radialCapMean U ρ y c ≤ M)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ y in (0 : ℝ)..1, t * radialLevelFraction U ρ t y) ≤ M := by
  apply integral_le_of_finite_difference_domination
    ((integrableOn_radialLevelFraction hU hρ t).const_mul t)
    (integrableOn_radialCapMean_diagonal hU hUpos hρ ht)
  · intro y hy
    exact radialCapMean_nonneg hUpos ρ y (mul_nonneg ht hy.1.le)
  · intro y hy
    exact hbound y hy _
  · intro y h hy hh hyh
    have hy' : y ∈ Ioo (0 : ℝ) 1 := ⟨hy, by linarith⟩
    have hyh' : y + h ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, hyh⟩
    have hinc := radialCapMean_increment hU hUpos ρ t (y + h)
      (mul_le_mul_of_nonneg_left (by linarith : y ≤ y + h) ht)
    have hm := hmono (t * y) hy' hyh' (by linarith)
    have heq : t * (y + h) - t * y = h * t := by ring
    rw [heq] at hinc
    calc
      _ = (h * t) * radialLevelFraction U ρ t (y + h) := by ring
      _ ≤ _ := hinc
      _ ≤ _ := sub_le_sub_left hm _

end BergmanWeakType.Weighted
