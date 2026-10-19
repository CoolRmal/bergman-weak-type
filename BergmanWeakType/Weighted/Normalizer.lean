/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.KernelIntegrability
public import BergmanWeakType.Weighted.BetaIntegral
public import BergmanWeakType.Weighted.CircleMobius
public import BergmanWeakType.Weighted.DiskSupermean
public import BergmanWeakType.Weighted.PoissonCap
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Complex.Harmonic.Poisson

/-! # The circular boundary-kernel normalizer

The normalizer is the average of the actual positive boundary kernel. Its sharp
bound requires a circle change of variables and a beta integral; neither estimate
is included as a hypothesis or an axiom here.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

/-- Circular mean of the positive boundary kernel at radial coordinate `r`. -/
def normalizer (α r : ℝ) : ℝ :=
  Real.circleAverage (fun ζ : ℂ ↦ ‖1 - (r : ℂ) * ζ‖ ^ (-(α + 2))) 0 1

theorem normalizer_eq_circleAverage_radius (α r : ℝ) :
    normalizer α r = Real.circleAverage (fun z : ℂ ↦ ‖1 - z‖ ^ (-(α + 2))) 0 r := by
  simpa [normalizer] using
    (Real.circleAverage_eq_circleAverage_zero_one
      (f := fun z : ℂ ↦ ‖1 - z‖ ^ (-(α + 2))) (c := 0) (R := r)).symm

@[simp] theorem normalizer_zero (α : ℝ) : normalizer α 0 = 1 := by
  simp [normalizer, Real.circleAverage_const]

theorem normalizer_nonneg (α r : ℝ) : 0 ≤ normalizer α r :=
  Real.circleAverage_nonneg_of_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _

theorem continuousOn_boundaryKernel_norm (p : ℝ) :
    ContinuousOn (fun z : ℂ ↦ ‖1 - z‖ ^ p) disk := by
  apply ContinuousOn.rpow_const (continuous_const.sub continuous_id).norm.continuousOn
  intro z hz
  left
  apply norm_ne_zero_iff.mpr
  apply sub_ne_zero.mpr
  intro h
  change (1 : ℂ) = z at h
  have hz' := (mem_disk_iff z).mp hz
  simp [← h] at hz'

theorem continuousOn_normalizer (α : ℝ) : ContinuousOn (normalizer α) (Set.Ico 0 1) := by
  change ContinuousOn (fun r ↦ normalizer α r) (Set.Ico 0 1)
  simp_rw [normalizer_eq_circleAverage_radius]
  apply Real.ContinuousOn.circleAverage
  · exact (continuousOn_boundaryKernel_norm (-(α + 2))).mono fun z hz ↦
      (mem_disk_iff z).mpr (by simpa using hz.2)
  · exact fun r hr ↦ hr.1

theorem circleIntegrable_boundaryKernel (α : ℝ) {r : ℝ} (hr : |r| < 1) :
    CircleIntegrable (fun z : ℂ ↦ ‖1 - z‖ ^ (-(α + 2))) 0 r := by
  apply ContinuousOn.circleIntegrable'
  apply (continuousOn_boundaryKernel_norm (-(α + 2))).mono
  intro z hz
  apply (mem_disk_iff z).mpr
  simpa only [Metric.mem_sphere, dist_zero_right] using lt_of_eq_of_lt hz hr

theorem normalizer_lower {α r : ℝ} (hα : -1 < α) (hr : |r| < 1) :
    (1 + |r|) ^ (-(α + 2)) ≤ normalizer α r := by
  rw [normalizer_eq_circleAverage_radius,
    ← Real.circleAverage_const ((1 + |r|) ^ (-(α + 2))) 0 r]
  apply Real.circleAverage_mono continuousOn_const.circleIntegrable'
    (circleIntegrable_boundaryKernel α hr)
  intro z hz
  have hz' : ‖z‖ = |r| := by simpa using hz
  have hn : 0 < ‖1 - z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) z
    simp only [norm_one, hz'] at h
    exact (sub_pos.mpr hr).trans_le h
  have hbound : ‖1 - z‖ ≤ 1 + |r| := by
    simpa only [norm_one, hz'] using norm_sub_le (1 : ℂ) z
  exact Real.rpow_le_rpow_of_nonpos hn hbound (by linarith)

theorem normalizer_pos {α r : ℝ} (hα : -1 < α) (hr : |r| < 1) :
    0 < normalizer α r :=
  (Real.rpow_pos_of_pos (by positivity) _).trans_le (normalizer_lower hα hr)

theorem normalizer_upper {α r : ℝ} (hα : -1 < α) (hr : |r| < 1) :
    normalizer α r ≤ (1 - |r|) ^ (-(α + 2)) := by
  rw [normalizer_eq_circleAverage_radius]
  apply Real.circleAverage_mono_on_of_le_circle (circleIntegrable_boundaryKernel α hr)
  intro z hz
  have hz' : ‖z‖ = |r| := by simpa using hz
  have hbound : 1 - |r| ≤ ‖1 - z‖ := by
    simpa only [norm_one, hz'] using norm_sub_norm_le (1 : ℂ) z
  exact Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hr) hbound (by linarith)

/-- Duplication expresses the proposed sharp constant in the boundary beta-integral form. -/
theorem gammaConstant_eq_boundaryGamma {α : ℝ} (hα : -1 < α) :
    gammaConstant α =
      2 ^ α * Real.Gamma ((α + 1) / 2) /
        (Real.sqrt Real.pi * Real.Gamma (1 + α / 2)) := by
  have hs : 0 < (α + 1) / 2 := by linarith
  have ht : 0 < 1 + α / 2 := by linarith
  have hG := Real.Gamma_mul_Gamma_add_half_of_pos hs
  have harg : (α + 1) / 2 + 1 / 2 = 1 + α / 2 := by ring
  have htwice : 2 * ((α + 1) / 2) = α + 1 := by ring
  rw [harg, htwice] at hG
  have hexp : 1 - (α + 1) = -α := by ring
  rw [hexp, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hG
  have htwo : (2 : ℝ) ^ α ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) α).ne'
  have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hGamma : Real.Gamma (1 + α / 2) ≠ 0 := (Real.Gamma_pos_of_pos ht).ne'
  have hdup : 2 ^ α * Real.Gamma ((α + 1) / 2) * Real.Gamma (1 + α / 2) =
      Real.Gamma (α + 1) * Real.sqrt Real.pi := by
    calc
      _ = (Real.Gamma ((α + 1) / 2) * Real.Gamma (1 + α / 2)) * 2 ^ α := by ring
      _ = (Real.Gamma (α + 1) * (2 ^ α)⁻¹ * Real.sqrt Real.pi) * 2 ^ α := by rw [hG]
      _ = _ := by field_simp
  unfold gammaConstant
  apply (div_eq_div_iff (pow_ne_zero 2 hGamma) (mul_ne_zero hpi hGamma)).mpr
  rw [← mul_assoc, ← hdup]
  ring

theorem norm_boundary_denominator_sq (r : ℝ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖ζ - (r : ℂ)‖ ^ 2 = ‖1 - (r : ℂ) * ζ‖ ^ 2 := by
  have hnormSq : Complex.normSq ζ = 1 := by rw [← Complex.sq_norm, hζ]; norm_num
  simp [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_mul, hnormSq]
  ring

/-- At weight zero the normalizer is exactly the reciprocal radial mass. -/
theorem radialMass_mul_normalizer_zero {r : ℝ} (hr : |r| < 1) :
    (1 - r ^ 2) * normalizer 0 r = 1 := by
  have hpoisson : Real.circleAverage (poissonKernel 0 (r : ℂ)) 0 1 = 1 := by
    simpa only [Pi.smul_def, smul_eq_mul, Pi.mul_def, mul_one] using
      (InnerProductSpace.harmonicOnNhd_const (1 : ℝ)).circleAverage_poissonKernel_smul
        (w := (r : ℂ)) (c := 0) (R := 1) (by simpa using hr)
  calc
    _ = Real.circleAverage (fun ζ : ℂ ↦ (1 - r ^ 2) * ‖1 - (r : ℂ) * ζ‖ ^ (-2 : ℝ)) 0 1 := by
      simpa [normalizer, smul_eq_mul] using
        (Real.circleAverage_fun_smul (a := (1 - r ^ 2 : ℝ))
          (f := fun ζ : ℂ ↦ ‖1 - (r : ℂ) * ζ‖ ^ (-2 : ℝ)) (c := 0) (R := 1)).symm
    _ = Real.circleAverage (poissonKernel 0 (r : ℂ)) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro ζ hζ
      have hζ' : ‖ζ‖ = 1 := by simpa using hζ
      rw [poissonKernel_def]
      simp only [sub_zero, hζ', one_pow, Complex.norm_real, Real.norm_eq_abs,
        sq_abs, norm_boundary_denominator_sq r hζ']
      rw [Real.rpow_neg (norm_nonneg _), Real.rpow_two, div_eq_mul_inv]
    _ = 1 := hpoisson

theorem circleAverage_boundary_power {α : ℝ} (hα : -1 < α) :
    Real.circleAverage (fun ζ : ℂ ↦ ‖1 - ζ‖ ^ α) 0 1 = gammaConstant α := by
  rw [Real.circleAverage_def]
  have heq : (∫ θ in (0 : ℝ)..2 * Real.pi, ‖1 - circleMap 0 1 θ‖ ^ α) =
      2 ^ α * (∫ θ in (0 : ℝ)..2 * Real.pi, Real.sin (θ / 2) ^ α) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by positivity)
    intro θ hθ
    dsimp only
    have hs : 0 ≤ Real.sin (θ / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
    rw [circleMap, zero_add, Complex.ofReal_one, one_mul, norm_sub_rev,
      mul_comm (θ : ℂ) Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hs),
      Real.mul_rpow (by norm_num) hs]
  rw [heq, intervalIntegral.integral_comp_div (fun θ ↦ Real.sin θ ^ α) (by norm_num)]
  simp only [zero_div, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), smul_eq_mul]
  rw [integral_sin_rpow hα, gammaConstant_eq_boundaryGamma hα]
  have hpi : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hpi0 : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hG : Real.Gamma (1 + α / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  field_simp
  rw [hpi]

theorem norm_boundaryKernel_circleMap_sq (r θ : ℝ) :
    ‖1 - (r : ℂ) * circleMap 0 1 θ‖ ^ 2 = circleDenominator r (Real.cos θ) := by
  have hn : Complex.normSq (Complex.exp ((θ : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.sq_norm]
    simp
  simp [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_mul, hn,
    circleDenominator, circleMap]
  ring

theorem norm_boundaryKernel_circleMap_rpow (p r θ : ℝ) :
    ‖1 - (r : ℂ) * circleMap 0 1 θ‖ ^ p =
      circleDenominator r (Real.cos θ) ^ (p / 2) := by
  rw [← norm_boundaryKernel_circleMap_sq, ← Real.rpow_natCast _ 2,
    ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  norm_num
  ring

theorem circleAverage_radialKernel_eq_arcsine (p : ℝ) {r : ℝ} (hr : |r| < 1) :
    Real.circleAverage (fun ζ : ℂ ↦ ‖1 - (r : ℂ) * ζ‖ ^ p) 0 1 =
      Real.pi⁻¹ * (∫ x in (-1 : ℝ)..1,
        circleDenominator r x ^ (p / 2) / Real.sqrt (1 - x ^ 2)) := by
  have hc : Continuous (fun θ ↦ circleDenominator r (Real.cos θ) ^ (p / 2)) := by
    apply Continuous.rpow_const (by unfold circleDenominator; fun_prop)
    exact fun θ ↦ Or.inl (circleDenominator_pos hr
      ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩).ne'
  have heq : (∫ θ in Real.pi..2 * Real.pi,
      circleDenominator r (Real.cos θ) ^ (p / 2)) =
      ∫ θ in (0 : ℝ)..Real.pi, circleDenominator r (Real.cos θ) ^ (p / 2) := by
    conv_lhs => arg 1; intro θ; rw [← Real.cos_two_pi_sub θ]
    rw [intervalIntegral.integral_comp_sub_left
      (fun θ ↦ circleDenominator r (Real.cos θ) ^ (p / 2)), sub_self,
      show 2 * Real.pi - Real.pi = Real.pi by ring]
  rw [Real.circleAverage_def]
  simp_rw [norm_boundaryKernel_circleMap_rpow]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := Real.pi) (c := 2 * Real.pi)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), heq,
    integral_cos_arcsine (fun x ↦ circleDenominator r x ^ (p / 2))]
  simp only [smul_eq_mul]
  ring

/-- The exact Möbius identity for the weighted boundary-kernel normalizer. -/
theorem radialMass_mul_normalizer (α : ℝ) {r : ℝ} (hr : |r| < 1) :
    (1 - r ^ 2) ^ (α + 1) * normalizer α r =
      Real.circleAverage (fun ζ : ℂ ↦ ‖1 - (r : ℂ) * ζ‖ ^ α) 0 1 := by
  unfold normalizer
  rw [circleAverage_radialKernel_eq_arcsine _ hr,
    circleAverage_radialKernel_eq_arcsine _ hr]
  calc
    _ = Real.pi⁻¹ * ((1 - r ^ 2) ^ (α + 1) *
        (∫ x in (-1 : ℝ)..1,
          circleDenominator r x ^ (-(α + 2) / 2) / Real.sqrt (1 - x ^ 2))) := by ring
    _ = _ := by rw [integral_circleDenominator_transform α hr]

theorem circleAverage_norm_sq_mono {g : ℂ → ℂ} {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hg : DifferentiableOn ℂ g (Metric.closedBall 0 R)) :
    Real.circleAverage (fun z ↦ ‖g z‖ ^ 2) 0 r ≤
      Real.circleAverage (fun z ↦ ‖g z‖ ^ 2) 0 R := by
  have hR : 0 ≤ R := hr.trans hrR.le
  have hv : ContinuousOn (fun z ↦ ‖g z‖ ^ 2) (Metric.closedBall 0 R) := by
    simpa only [Pi.pow_apply] using! hg.continuousOn.norm.pow 2
  have hi : CircleIntegrable (fun z ↦ ‖g z‖ ^ 2) 0 R := by
    apply ContinuousOn.circleIntegrable'
    simpa only [abs_of_nonneg hR] using hv.mono Metric.sphere_subset_closedBall
  have habs : |r| < |R| := by simpa only [abs_of_nonneg hr, abs_of_nonneg hR] using hrR
  rw [← circleAverage_poissonExtension hi habs]
  have hsub : Metric.sphere (0 : ℂ) |r| ⊆ (Metric.sphere 0 |R|)ᶜ := by
    intro z hz
    have hz' : ‖z‖ = |r| := by simpa using hz
    simpa [hz'] using habs.ne
  apply Real.circleAverage_mono
    (hv.mono (by simpa only [abs_of_nonneg hr] using
      (Metric.sphere_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall hrR.le)))).circleIntegrable'
    ((continuousOn_poissonExtension hi).mono hsub).circleIntegrable'
  intro z hz
  apply Weighted.norm_sq_le_circleAverage_poisson
    (hg.diffContOnCl_ball (Set.Subset.refl _))
  have hz' : ‖z‖ = r := by simpa [abs_of_nonneg hr] using hz
  simpa [Metric.mem_ball, dist_zero_right, hz'] using hrR

theorem differentiableOn_boundaryPower (α : ℝ) {R : ℝ} (hR : R < 1) :
    DifferentiableOn ℂ (fun z : ℂ ↦ (1 - z) ^ ((α / 2 : ℝ) : ℂ))
      (Metric.closedBall 0 R) := by
  apply DifferentiableOn.cpow_const
    ((differentiable_const (1 : ℂ)).sub differentiable_id).differentiableOn
  intro z hz
  apply Complex.mem_slitPlane_iff.mpr
  left
  have hz' : ‖z‖ ≤ R := by simpa using hz
  change 0 < (1 - z).re
  simp only [Complex.sub_re, Complex.one_re]
  linarith [Complex.re_le_norm z]

theorem norm_boundaryPower_sq (α : ℝ) (z : ℂ) :
    ‖(1 - z) ^ ((α / 2 : ℝ) : ℂ)‖ ^ 2 = ‖1 - z‖ ^ α := by
  rw [Complex.norm_cpow_real, ← Real.rpow_natCast _ 2,
    ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  norm_num

theorem circleAverage_boundaryPower_mono (α : ℝ) {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r ≤ R) (hR : R < 1) :
    Real.circleAverage (fun z : ℂ ↦ ‖1 - z‖ ^ α) 0 r ≤
      Real.circleAverage (fun z : ℂ ↦ ‖1 - z‖ ^ α) 0 R := by
  rcases hrR.eq_or_lt with rfl | hrR
  · rfl
  have h := circleAverage_norm_sq_mono hr hrR (differentiableOn_boundaryPower α hR)
  simpa only [norm_boundaryPower_sq] using h

end BergmanWeakType
