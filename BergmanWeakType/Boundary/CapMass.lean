/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Boundary.ColumnBound
public import BergmanWeakType.Boundary.HalfDiskIntegral
public import BergmanWeakType.Weighted.PolarIntegral
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The mass of small caps at the boundary of the disk -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Topology

namespace BergmanWeakType

def capProfile (α R : ℝ) (u : ℂ) : ℝ :=
  if R * ‖u‖ ^ 2 < 2 * u.re then (2 * u.re - R * ‖u‖ ^ 2) ^ α else 0

theorem norm_sq_boundary_affine (R : ℝ) (u : ℂ) :
    ‖1 - (R : ℂ) * u‖ ^ 2 = 1 - 2 * R * u.re + R ^ 2 * ‖u‖ ^ 2 := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem boundary_affine_mem_disk {R : ℝ} (hR : 0 < R) (u : ℂ) :
    1 - (R : ℂ) * u ∈ disk ↔ R * ‖u‖ ^ 2 < 2 * u.re := by
  rw [mem_disk_iff]
  have hid := norm_sq_boundary_affine R u
  constructor
  · intro hu
    nlinarith [norm_nonneg (1 - (R : ℂ) * u)]
  · intro hu
    nlinarith [norm_nonneg (1 - (R : ℂ) * u)]

theorem integral_boundary_affine_area (f : ℂ → ℝ) {R : ℝ} (hR : 0 < R) :
    ∫ u, f (1 - (R : ℂ) * u) ∂area = (R ^ 2)⁻¹ * ∫ z, f z ∂area := by
  have hc := Measure.integral_comp_smul_of_nonneg (volume : Measure ℂ)
    (fun z : ℂ ↦ f (1 - z)) R (hR := hR.le)
  rw [Complex.finrank_real_complex, integral_sub_left_eq_self f volume 1] at hc
  simp only [Complex.real_smul, smul_eq_mul] at hc
  simp only [area, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ Real.pi⁻¹), smul_eq_mul]
  rw [hc]
  ring

theorem weightedArea_boundaryCap_real {α : ℝ} (hα : -1 < α) (R : ℝ) :
    (weightedArea α).real (boundaryCap R) = (α + 1) *
      ∫ z, (boundaryCap R).indicator (fun z ↦ (1 - ‖z‖ ^ 2) ^ α) z ∂area := by
  rw [← integral_indicator_one (measurableSet_boundaryCap R),
    integral_weightedArea_eq_diskArea hα, diskArea,
    ← integral_indicator measurableSet_disk, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z ↦ by
    by_cases hz : z ∈ boundaryCap R
    · simp [hz, hz.1]
    · by_cases hzd : z ∈ disk <;> simp [hz, hzd]

theorem boundary_affine_mem_cap {R : ℝ} (hR : 0 < R) (u : ℂ) :
    1 - (R : ℂ) * u ∈ boundaryCap R ↔ u ∈ disk ∧ R * ‖u‖ ^ 2 < 2 * u.re := by
  have hball : 1 - (R : ℂ) * u ∈ Metric.ball 1 R ↔ u ∈ disk := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : 1 - (R : ℂ) * u - 1 = -((R : ℂ) * u) := by ring
    rw [heq, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
      mem_disk_iff]
    constructor <;> intro h <;> nlinarith
  simp only [boundaryCap, Set.mem_inter_iff, boundary_affine_mem_disk hR, hball, and_comm]

theorem boundaryCap_integrand_affine (α : ℝ) {R : ℝ} (hR : 0 < R) (u : ℂ) :
    (boundaryCap R).indicator (fun z ↦ (1 - ‖z‖ ^ 2) ^ α) (1 - (R : ℂ) * u) =
      R ^ α * disk.indicator (capProfile α R) u := by
  by_cases hu : u ∈ disk
  · rw [Set.indicator_of_mem hu]
    by_cases hp : R * ‖u‖ ^ 2 < 2 * u.re
    · rw [Set.indicator_of_mem ((boundary_affine_mem_cap hR u).mpr ⟨hu, hp⟩),
        capProfile, ite_eq_left hp, norm_sq_boundary_affine]
      have heq : 1 - (1 - 2 * R * u.re + R ^ 2 * ‖u‖ ^ 2) =
          R * (2 * u.re - R * ‖u‖ ^ 2) := by ring
      rw [heq, Real.mul_rpow hR.le (by linarith)]
    · rw [Set.indicator_of_notMem (by simpa only [boundary_affine_mem_cap hR, hu,
        true_and] using hp), capProfile, ite_eq_right hp, mul_zero]
  · rw [Set.indicator_of_notMem hu, mul_zero, Set.indicator_of_notMem]
    exact fun h ↦ hu ((boundary_affine_mem_cap hR u).mp h).1

theorem weightedArea_boundaryCap_rescaled {α R : ℝ} (hα : -1 < α) (hR : 0 < R) :
    R ^ (-(α + 2)) * (weightedArea α).real (boundaryCap R) =
      (α + 1) * ∫ u, capProfile α R u ∂diskArea := by
  have heq := integral_boundary_affine_area
    ((boundaryCap R).indicator (fun z ↦ (1 - ‖z‖ ^ 2) ^ α)) hR
  simp_rw [boundaryCap_integrand_affine α hR] at heq
  rw [integral_const_mul, integral_indicator measurableSet_disk] at heq
  have hmass := weightedArea_boundaryCap_real hα R
  have hp : R ^ (-(α + 2)) * R ^ α * R ^ 2 = 1 := by
    rw [← Real.rpow_add hR]
    rw [← Real.rpow_natCast R 2]
    norm_num only [Nat.cast_ofNat]
    rw [← Real.rpow_add hR]
    have he : -(α + 2) + α + 2 = (0 : ℝ) := by ring
    rw [he, Real.rpow_zero]
  have hi : (∫ z, (boundaryCap R).indicator (fun z ↦ (1 - ‖z‖ ^ 2) ^ α) z ∂area) =
      R ^ α * R ^ 2 * ∫ u, capProfile α R u ∂diskArea := by
    change R ^ α * (∫ u, capProfile α R u ∂diskArea) = _ at heq
    have hR2 : R ^ 2 ≠ 0 := pow_ne_zero _ hR.ne'
    field_simp at heq
    nlinarith [heq]
  rw [hmass, hi]
  calc
    _ = (α + 1) * (R ^ (-(α + 2)) * R ^ α * R ^ 2) *
        ∫ u, capProfile α R u ∂diskArea := by ring
    _ = _ := by rw [hp, mul_one]

theorem measurable_capProfile (α R : ℝ) : Measurable (capProfile α R) := by
  unfold capProfile
  have hm : Measurable (fun u : ℂ ↦ (2 * u.re - R * ‖u‖ ^ 2) ^ α) := by fun_prop
  exact hm.ite (measurableSet_lt (by fun_prop) (by fun_prop)) measurable_const

theorem capProfile_nonneg (α R : ℝ) (u : ℂ) : 0 ≤ capProfile α R u := by
  unfold capProfile
  split_ifs with h
  · exact Real.rpow_nonneg (by linarith) _
  · exact le_rfl

theorem capProfile_le {α R : ℝ} (hα : 0 ≤ α) (hR : 0 ≤ R) {u : ℂ}
    (hu : u ∈ disk) : capProfile α R u ≤ 2 ^ α := by
  unfold capProfile
  split_ifs with h
  · apply Real.rpow_le_rpow (by linarith) _ hα
    have := (mem_disk_iff u).mp hu
    nlinarith [Complex.re_le_norm u, mul_nonneg hR (sq_nonneg ‖u‖)]
  · positivity

theorem tendsto_capProfile (α : ℝ) (u : ℂ) :
    Filter.Tendsto (fun R ↦ capProfile α R u) (𝓝[>] (0 : ℝ)) (𝓝 (halfDiskPower α u)) := by
  by_cases hu : 0 < u.re
  · have hbase : Filter.Tendsto (fun R : ℝ ↦ 2 * u.re - R * ‖u‖ ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (2 * u.re)) := by
      have hc : Continuous (fun R : ℝ ↦ 2 * u.re - R * ‖u‖ ^ 2) := by fun_prop
      simpa only [zero_mul, sub_zero] using
        hc.continuousAt.tendsto.mono_left
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    have hevent : ∀ᶠ R : ℝ in 𝓝[>] 0, R * ‖u‖ ^ 2 < 2 * u.re := by
      filter_upwards [hbase.eventually (lt_mem_nhds (by positivity : 0 < 2 * u.re))] with R hR
      linarith
    rw [halfDiskPower, ite_eq_left hu]
    apply Filter.Tendsto.congr' (hevent.mono fun R hR ↦ ?_)
      (hbase.rpow_const (Or.inl (by positivity)))
    simp only [capProfile, ite_eq_left hR]
  · have heq : ∀ᶠ R : ℝ in 𝓝[>] 0, capProfile α R u = 0 := by
      filter_upwards [self_mem_nhdsWithin] with R hR
      have hR' : 0 < R := hR
      have hn : ¬ R * ‖u‖ ^ 2 < 2 * u.re := by
        have := le_of_not_gt hu
        nlinarith [mul_nonneg hR'.le (sq_nonneg ‖u‖)]
      simp only [capProfile, ite_eq_right hn]
    rw [halfDiskPower, ite_eq_right hu]
    exact tendsto_const_nhds.congr' (heq.mono fun R hR ↦ hR.symm)

theorem tendsto_integral_capProfile {α : ℝ} (hα : 0 ≤ α) :
    Filter.Tendsto (fun R ↦ ∫ u, capProfile α R u ∂diskArea) (𝓝[>] (0 : ℝ))
      (𝓝 (gammaConstant α / (α + 2))) := by
  rw [← integral_halfDiskPower hα]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (2 : ℝ) ^ α)
  · exact Filter.Eventually.of_forall fun R ↦ (measurable_capProfile α R).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with R hR
    filter_upwards [ae_mem_disk] with u hu
    rw [Real.norm_of_nonneg (capProfile_nonneg α R u)]
    exact capProfile_le hα (le_of_lt hR) hu
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (tendsto_capProfile α)

theorem tendsto_rescaled_boundaryCap_real {α : ℝ} (hα : 0 ≤ α) :
    Filter.Tendsto (fun R ↦ R ^ (-(α + 2)) * (weightedArea α).real (boundaryCap R))
      (𝓝[>] (0 : ℝ)) (𝓝 (boundaryConstant α)) := by
  have hlim := (tendsto_integral_capProfile hα).const_mul (α + 1)
  have hconst : (α + 1) * (gammaConstant α / (α + 2)) = boundaryConstant α := by
    unfold boundaryConstant
    ring
  rw [hconst] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with R hR
  exact (weightedArea_boundaryCap_rescaled (by linarith : -1 < α) hR).symm

end BergmanWeakType
