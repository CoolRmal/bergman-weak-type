/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.CoreGap
public import BergmanWeakType.Rigidity.KernelTransform

@[expose] public section

noncomputable section

open Set MeasureTheory Metric Filter
open scoped ComplexConjugate Topology

namespace BergmanWeakType

theorem isOpen_image_of_holomorphic_injOn {U : Set ℂ} {φ : ℂ → ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) :
    IsOpen (φ '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨w, hw, rfl⟩
  have hopen : 𝓝 (φ w) ≤ Filter.map φ (𝓝 w) :=
    (hφ.analyticAt (hU.mem_nhds hw)).eventually_constant_or_nhds_le_map_nhds.resolve_left
      (not_eventually_constant_of_injOn hU hinj hw)
  exact hopen (image_mem_map (hU.mem_nhds hw))

theorem IsBergmanKernel.disk_jacobian_formula {Ω : Set ℂ} {K : ℂ → ℂ → ℂ}
    {φ ψ : ℂ → ℂ} (hK : IsBergmanKernel Ω K) (hΩ : IsOpen Ω)
    (hφ : DifferentiableOn ℂ φ disk) (hψ : DifferentiableOn ℂ ψ Ω)
    (hbij : BijOn φ disk Ω) (hinv : InvOn ψ φ disk Ω)
    {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk) :
    (‖deriv φ w‖ ^ 2 : ℝ) • K (φ z) (φ w) =
      (deriv φ w * kernel z w) / deriv φ z := by
  have hqz := deriv_ne_zero_of_bijOn isOpen_ball hΩ hφ hbij hz
  have hqw := deriv_ne_zero_of_bijOn isOpen_ball hΩ hφ hbij hw
  have hqwc : star (deriv φ w) ≠ 0 := star_ne_zero.mpr hqw
  rw [hK.disk_coordinate_formula hΩ hφ hψ hbij hinv hz hw,
    Complex.real_smul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [starRingEnd_apply]
  field_simp [hqz, hqw, hqwc]

theorem IsBergmanKernel.core_integral_coordinate_formula {Ω : Set ℂ}
    {K : ℂ → ℂ → ℂ} {φ ψ : ℂ → ℂ} (hK : IsBergmanKernel Ω K) (hΩ : IsOpen Ω)
    (hφ : DifferentiableOn ℂ φ disk) (hψ : DifferentiableOn ℂ ψ Ω)
    (hbij : BijOn φ disk Ω) (hinv : InvOn ψ φ disk Ω)
    {r : ℝ} (hr1 : r < 1) {z : ℂ} (hz : z ∈ disk) :
    (∫ w in φ '' ball 0 r, K (φ z) w ∂area) =
        (∫ w in ball 0 r, deriv φ w * kernel z w ∂area) / deriv φ z ∧
      (∫ w in φ '' ball 0 r, ‖K (φ z) w‖ ∂area) =
        (∫ w in ball 0 r, ‖deriv φ w * kernel z w‖ ∂area) / ‖deriv φ z‖ := by
  have hsub : ball (0 : ℂ) r ⊆ disk := fun w hw ↦ lt_trans hw hr1
  constructor
  · rw [area_integral_image_eq isOpen_ball (hφ.mono hsub) (hbij.injOn.mono hsub),
      ← integral_div]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with w hw
    exact hK.disk_jacobian_formula hΩ hφ hψ hbij hinv hz (hsub hw)
  · rw [area_integral_image_eq isOpen_ball (hφ.mono hsub) (hbij.injOn.mono hsub),
      ← integral_div]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with w hw
    have h := congrArg norm (hK.disk_jacobian_formula hΩ hφ hψ hbij hinv hz (hsub hw))
    simpa only [norm_smul, Real.norm_eq_abs, abs_sq, norm_div, smul_eq_mul] using h

/-- A bounded simply connected nondisk has a positive-area interior set with a uniform strict
triangle-inequality gap for all its Bergman kernel rows. -/
theorem exists_domain_core_gap {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hbdd : Bornology.IsBounded Ω) (hconn : IsSimplyConnected Ω)
    {K : ℂ → ℂ → ℂ} (hK : IsBergmanKernel Ω K)
    (hnd : ¬∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ Ω = ball c R) :
    ∃ E : Set ℂ, MeasurableSet E ∧ E ⊆ Ω ∧ 0 < area E ∧
      ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ a ∈ Ω,
        ‖∫ w in E, K a w ∂area‖ ≤ (1 - η) * ∫ w in E, ‖K a w‖ ∂area := by
  have hproper : Ω ≠ univ := fun heq ↦ NormedSpace.unbounded_univ ℝ ℂ (heq ▸ hbdd)
  obtain ⟨φ, ψ, hφ, hψ, hbij, hinv, hne, _⟩ :=
    exists_biholomorphic_unitBall hΩ hconn hproper
  have hsub : ball (0 : ℂ) (1 / 2 : ℝ) ⊆ disk :=
    ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1)
  let E := φ '' ball (0 : ℂ) (1 / 2 : ℝ)
  have hEopen : IsOpen E :=
    isOpen_image_of_holomorphic_injOn isOpen_ball (hφ.mono hsub) (hbij.injOn.mono hsub)
  have hEpos : 0 < area E := hEopen.measure_pos area
    ⟨φ 0, 0, mem_ball_self (by norm_num), rfl⟩
  have hφbdd : Bornology.IsBounded (φ '' disk) := hbij.image_eq.symm ▸ hbdd
  have hφnd : ¬∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ φ '' disk = ball c R := by
    simpa only [disk, hbij.image_eq] using hnd
  obtain ⟨η, hη, hη1, hgap⟩ := exists_core_relative_gap hφ hne hφbdd hφnd
    (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨E, hEopen.measurableSet, ?_, hEpos, η, hη, hη1, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hbij.mapsTo (hsub hw)
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := hbij.surjOn ha
    obtain ⟨hI, hJ⟩ := hK.core_integral_coordinate_formula hΩ hφ hψ hbij hinv
      (by norm_num : (1 / 2 : ℝ) < 1) hz
    dsimp [E]
    rw [hI, hJ, norm_div, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (hgap z (ball_subset_closedBall hz)) (norm_nonneg _)

end BergmanWeakType
