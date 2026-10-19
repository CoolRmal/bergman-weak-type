/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.DiskPotential
public import BergmanWeakType.Weighted.PoissonCap
public import BergmanWeakType.Weighted.MovingCap
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Moving circular truncations of the normalized disk potential -/

@[expose] public section

noncomputable section

open MeasureTheory Complex Real Set
open scoped Topology ENNReal

namespace BergmanWeakType.Weighted

/-- A measurable extension by zero; all interior values are the actual normalized potential. -/
def diskPotential (f : ℂ → ℂ) : ℂ → ℝ := disk.indicator (normalizedPotential f)

theorem diskPotential_eq {f : ℂ → ℂ} {z : ℂ} (hz : z ∈ disk) :
    diskPotential f z = normalizedPotential f z := Set.indicator_of_mem hz _

theorem diskPotential_nonneg (f : ℂ → ℂ) (z : ℂ) : 0 ≤ diskPotential f z :=
  Set.indicator_nonneg (fun _ hz ↦ normalizedPotential_nonneg hz) z

theorem measurable_diskPotential {f : ℂ → ℂ} (hf : Integrable f diskArea) :
    Measurable (diskPotential f) := by
  classical
  exact (continuousOn_normalizedPotential_disk hf).measurable_piecewise
    continuousOn_const measurableSet_disk

def capMean (f : ℂ → ℂ) (y c : ℝ) : ℝ :=
  circleAverage (fun z ↦ min (diskPotential f z) c) 0 (sqrt (1 - y))

def levelFraction (f : ℂ → ℂ) (t y : ℝ) : ℝ :=
  circleAverage (fun z ↦ if t * y < diskPotential f z then (1 : ℝ) else 0) 0 (sqrt (1 - y))

theorem circleIntegrable_of_measurable_bounded {g : ℂ → ℝ} (hg : Measurable g)
    {M : ℝ} (hbound : ∀ z, ‖g z‖ ≤ M) (r : ℝ) : CircleIntegrable g 0 r := by
  rw [CircleIntegrable, intervalIntegrable_iff_integrableOn_Icc_of_le Real.two_pi_pos.le]
  apply Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
    (hg.comp (continuous_circleMap 0 r).measurable).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun θ ↦ hbound _

theorem circleIntegrable_level {f : ℂ → ℂ} (hf : Integrable f diskArea) (t y r : ℝ) :
    CircleIntegrable (fun z ↦ if t * y < diskPotential f z then (1 : ℝ) else 0) 0 r := by
  apply circleIntegrable_of_measurable_bounded
    (measurable_const.ite (measurableSet_lt measurable_const (measurable_diskPotential hf))
      measurable_const) (M := 1) _ r
  intro z
  split_ifs <;> norm_num

theorem levelFraction_nonneg (f : ℂ → ℂ) (t y : ℝ) : 0 ≤ levelFraction f t y := by
  apply circleAverage_nonneg_of_nonneg
  intro z _
  split_ifs <;> norm_num

theorem levelFraction_le_one {f : ℂ → ℂ} (hf : Integrable f diskArea) (t y : ℝ) :
    levelFraction f t y ≤ 1 := by
  apply circleAverage_mono_on_of_le_circle (circleIntegrable_level hf t y _)
  intro z _
  split_ifs <;> norm_num

theorem measurable_levelFraction {f : ℂ → ℂ} (hf : Integrable f diskArea) (t : ℝ) :
    Measurable (levelFraction f t) := by
  have hpoint : Continuous (fun p : ℝ × ℝ ↦ circleMap 0 (sqrt (1 - p.1)) p.2) :=
    circleMap.continuous.comp ((Real.continuous_sqrt.comp
      (continuous_const.sub continuous_fst)).prodMk continuous_snd)
  have hpred : MeasurableSet {p : ℝ × ℝ | t * p.1 <
      diskPotential f (circleMap 0 (sqrt (1 - p.1)) p.2)} :=
    measurableSet_lt (measurable_const.mul measurable_fst)
      ((measurable_diskPotential hf).comp hpoint.measurable)
  have hm : Measurable (fun p : ℝ × ℝ ↦ if t * p.1 <
      diskPotential f (circleMap 0 (sqrt (1 - p.1)) p.2) then (1 : ℝ) else 0) :=
    measurable_const.ite hpred measurable_const
  have hi : StronglyMeasurable (fun y ↦ ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi),
      if t * y < diskPotential f (circleMap 0 (sqrt (1 - y)) θ) then (1 : ℝ) else 0) :=
    hm.stronglyMeasurable.integral_prod_right'
  change Measurable (fun y ↦ levelFraction f t y)
  simp only [levelFraction, circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  exact measurable_const.mul hi.measurable

theorem integrableOn_levelFraction {f : ℂ → ℂ} (hf : Integrable f diskArea) (t : ℝ) :
    IntegrableOn (levelFraction f t) (Icc (0 : ℝ) 1) := by
  apply Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
    (measurable_levelFraction hf t).aestronglyMeasurable (M := 1)
  exact Filter.Eventually.of_forall fun y ↦ by
    rw [Real.norm_of_nonneg (levelFraction_nonneg f t y)]
    exact levelFraction_le_one hf t y

theorem circleIntegrable_cap {f : ℂ → ℂ} (hf : Integrable f diskArea) (c r : ℝ) :
    CircleIntegrable (fun z ↦ min (diskPotential f z) c) 0 r := by
  apply circleIntegrable_of_measurable_bounded
    ((measurable_diskPotential hf).inf measurable_const) (M := |c|) _ r
  intro z
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · exact le_min ((neg_nonpos.mpr (abs_nonneg c)).trans (diskPotential_nonneg f z)) (neg_abs_le c)
  · exact (min_le_right _ _).trans (le_abs_self c)

theorem capMean_nonneg (f : ℂ → ℂ) (y : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ capMean f y c := by
  apply circleAverage_nonneg_of_nonneg
  intro z _
  exact le_min (diskPotential_nonneg f z) hc

theorem capMean_le_level {f : ℂ → ℂ} (hf : Integrable f diskArea) (y c : ℝ) :
    capMean f y c ≤ c := by
  apply circleAverage_mono_on_of_le_circle (circleIntegrable_cap hf c _)
  exact fun _ _ ↦ min_le_right _ _

theorem measurable_capMean_diagonal {f : ℂ → ℂ} (hf : Integrable f diskArea) (t : ℝ) :
    Measurable (fun y ↦ capMean f y (t * y)) := by
  have hpoint : Continuous (fun p : ℝ × ℝ ↦ circleMap 0 (sqrt (1 - p.1)) p.2) :=
    circleMap.continuous.comp ((Real.continuous_sqrt.comp
      (continuous_const.sub continuous_fst)).prodMk continuous_snd)
  have hm : Measurable (fun p : ℝ × ℝ ↦
      min (diskPotential f (circleMap 0 (sqrt (1 - p.1)) p.2)) (t * p.1)) :=
    ((measurable_diskPotential hf).comp hpoint.measurable).inf
      (measurable_const.mul measurable_fst)
  have hi := hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))
  simp only [capMean, circleAverage_def, smul_eq_mul,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  exact measurable_const.mul hi.measurable

theorem integrableOn_capMean_diagonal {f : ℂ → ℂ} (hf : Integrable f diskArea)
    {t : ℝ} (ht : 0 ≤ t) : IntegrableOn (fun y ↦ capMean f y (t * y)) (Icc (0 : ℝ) 1) := by
  apply Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
    (measurable_capMean_diagonal hf t).aestronglyMeasurable (M := t)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  rw [Real.norm_of_nonneg (capMean_nonneg f y (mul_nonneg ht hy.1))]
  exact (capMean_le_level hf y _).trans (mul_le_of_le_one_right ht hy.2)

theorem radius_mem_unit {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    sqrt (1 - y) ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · exact sqrt_pos.mpr (sub_pos.mpr hy.2)
  · have h := sqrt_lt_sqrt (sub_nonneg.mpr hy.2.le) (show 1 - y < 1 by linarith [hy.1])
    simpa only [sqrt_one] using h

theorem capMean_eq_normalized {f : ℂ → ℂ} {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (c : ℝ) :
    capMean f y c = circleAverage (fun z ↦ min (normalizedPotential f z) c) 0 (sqrt (1 - y)) := by
  apply circleAverage_congr_sphere
  intro z hz
  have hz' : ‖z‖ = sqrt (1 - y) := by
    simpa only [Metric.mem_sphere, dist_zero_right, abs_of_nonneg (sqrt_nonneg _)] using hz
  dsimp only
  rw [diskPotential_eq (f := f) ((mem_disk_iff z).mpr (hz'.trans_lt (radius_mem_unit hy).2))]

theorem capMean_monotone_mass {f : ℂ → ℂ} (hf : Integrable f diskArea)
    {y u : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1) (hyu : y ≤ u) (c : ℝ) :
    capMean f y c ≤ capMean f u c := by
  rcases hyu.eq_or_lt with rfl | hyu
  · exact le_rfl
  rw [capMean_eq_normalized hy, capMean_eq_normalized hu]
  apply circleAverage_min_antitone_of_poisson_supermean (sqrt_nonneg _)
    (sqrt_lt_sqrt (sub_nonneg.mpr hu.2.le) (by linarith))
    (continuousOn_normalizedPotential hf (radius_mem_unit hy).2)
  intro z hz
  exact normalizedPotential_poisson_supermean hf (radius_mem_unit hy).2 hz

theorem capMean_le_mass {f : ℂ → ℂ} (hf : Integrable f diskArea)
    {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) (c : ℝ) :
    capMean f y c ≤ ∫ w, ‖f w‖ ∂diskArea := by
  rw [capMean_eq_normalized hy]
  have h := circleAverage_min_antitone_of_poisson_supermean (c := c) (le_refl 0)
    (radius_mem_unit hy).1 (continuousOn_normalizedPotential hf (radius_mem_unit hy).2)
    (fun z hz ↦ normalizedPotential_poisson_supermean hf (radius_mem_unit hy).2 hz)
  simp only [circleAverage_zero, normalizedPotential_zero] at h
  exact h.trans (min_le_left _ _)

theorem capMean_increment {f : ℂ → ℂ} (hf : Integrable f diskArea)
    (t y : ℝ) {c : ℝ} (hc : c ≤ t * y) :
    (t * y - c) * levelFraction f t y ≤ capMean f y (t * y) - capMean f y c := by
  have hiL : CircleIntegrable
      (fun z ↦ (t * y - c) • (if t * y < diskPotential f z then (1 : ℝ) else 0))
      0 (sqrt (1 - y)) := (circleIntegrable_level hf t y _).const_smul
  have hiR := (circleIntegrable_cap hf (t * y) (sqrt (1 - y))).sub
    (circleIntegrable_cap hf c (sqrt (1 - y)))
  have hpoint (z : ℂ) : (t * y - c) • (if t * y < diskPotential f z then (1 : ℝ) else 0) ≤
      min (diskPotential f z) (t * y) - min (diskPotential f z) c := by
    by_cases hz : t * y < diskPotential f z
    · rw [ite_eq_left hz, smul_eq_mul, mul_one, min_eq_right hz.le,
        min_eq_right (hc.trans hz.le)]
    · rw [ite_eq_right hz, smul_eq_mul, mul_zero]
      exact sub_nonneg.mpr (min_le_min_left _ hc)
  have havg := circleAverage_mono hiL hiR (fun z _ ↦ hpoint z)
  rw [circleAverage_fun_smul, circleAverage_sub
    (circleIntegrable_cap hf (t * y) _) (circleIntegrable_cap hf c _)] at havg
  exact havg

theorem capMean_finite_difference {f : ℂ → ℂ} (hf : Integrable f diskArea)
    {t : ℝ} (ht : 0 ≤ t) {y h : ℝ} (hy : 0 < y) (hh : 0 < h) (hyh : y + h < 1) :
    h * (t * levelFraction f t (y + h)) ≤
      capMean f (y + h) (t * (y + h)) - capMean f y (t * y) := by
  have hy' : y ∈ Ioo (0 : ℝ) 1 := ⟨hy, by linarith⟩
  have hyh' : y + h ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, hyh⟩
  have hinc := capMean_increment hf t (y + h)
    (mul_le_mul_of_nonneg_left (by linarith : y ≤ y + h) ht)
  have hmono := capMean_monotone_mass hf hy' hyh' (by linarith) (t * y)
  have heq : t * (y + h) - t * y = h * t := by ring
  rw [heq] at hinc
  calc
    _ = (h * t) * levelFraction f t (y + h) := by ring
    _ ≤ _ := hinc
    _ ≤ _ := sub_le_sub_left hmono _

/-- The moving-cap argument gives the sharp integrated distribution estimate. -/
theorem integral_mul_levelFraction_le {f : ℂ → ℂ} (hf : Integrable f diskArea)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ y in (0 : ℝ)..1, t * levelFraction f t y) ≤ ∫ w, ‖f w‖ ∂diskArea := by
  apply integral_le_of_finite_difference_domination
    ((integrableOn_levelFraction hf t).const_mul t) (integrableOn_capMean_diagonal hf ht)
  · intro y hy
    exact capMean_nonneg f y (mul_nonneg ht hy.1.le)
  · intro y hy
    exact capMean_le_mass hf hy _
  · intro y h hy hh hyh
    exact capMean_finite_difference hf ht hy hh hyh

end BergmanWeakType.Weighted
