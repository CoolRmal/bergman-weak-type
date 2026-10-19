/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Tactic.Linarith
public import BergmanWeakType.Weighted.SmoothCap

/-! # Truncation of functions satisfying the Poisson supermean inequality -/

@[expose] public section

noncomputable section

open Complex InnerProductSpace MeasureTheory Metric Real Set

namespace BergmanWeakType

def poissonExtension (R : ℝ) (v : ℂ → ℝ) (z : ℂ) : ℝ :=
  circleAverage (fun ζ ↦ poissonKernel 0 z ζ * v ζ) 0 R

theorem poissonKernel_nonneg_on_sphere {R : ℝ} {z ζ : ℂ}
    (hz : z ∈ ball 0 R) (hζ : ζ ∈ sphere 0 |R|) :
    0 ≤ poissonKernel 0 z ζ := by
  have hz' : ‖z‖ < R := by simpa using hz
  have hζ' : ‖ζ‖ = |R| := by simpa using hζ
  have hR : 0 ≤ R := (norm_nonneg z).trans hz'.le
  simp only [poissonKernel_def, sub_zero, hζ', abs_of_nonneg hR]
  exact div_nonneg (by nlinarith [norm_nonneg z]) (sq_nonneg _)

theorem continuousOn_poissonKernel_sphere {R : ℝ} {z : ℂ}
    (hz : z ∈ ball 0 R) : ContinuousOn (poissonKernel 0 z) (sphere 0 |R|) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  apply continuous_re.comp_continuousOn
  apply continuousOn_herglotzRieszKernel_sphere
  have hz' : ‖z‖ < R := by simpa using hz
  have hR : 0 ≤ R := (norm_nonneg z).trans hz'.le
  simpa [mem_sphere, dist_zero_right, abs_of_nonneg hR] using hz'.ne

theorem poissonExtension_const {R c : ℝ} {z : ℂ} (hz : z ∈ ball 0 R) :
    poissonExtension R (fun _ ↦ c) z = c := by
  simpa only [poissonExtension, Pi.smul_def, smul_eq_mul, Pi.mul_def] using
    (harmonicOnNhd_const c).circleAverage_poissonKernel_smul hz

theorem poissonExtension_min_le {R c : ℝ} {v : ℂ → ℝ} {z : ℂ}
    (hv : ContinuousOn v (sphere 0 |R|)) (hz : z ∈ ball 0 R)
    (hsuper : poissonExtension R v z ≤ v z) :
    poissonExtension R (fun ζ ↦ min (v ζ) c) z ≤ min (v z) c := by
  have hp := continuousOn_poissonKernel_sphere hz
  have hm := hv.inf (continuousOn_const (c := c))
  apply le_min
  · apply le_trans _ hsuper
    apply circleAverage_mono (hp.mul hm).circleIntegrable' (hp.mul hv).circleIntegrable'
    intro ζ hζ
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (poissonKernel_nonneg_on_sphere hz hζ)
  · calc
      _ ≤ poissonExtension R (fun _ ↦ c) z := by
        apply circleAverage_mono (hp.mul hm).circleIntegrable'
          (hp.mul continuousOn_const).circleIntegrable'
        intro ζ hζ
        exact mul_le_mul_of_nonneg_left (min_le_right _ _)
          (poissonKernel_nonneg_on_sphere hz hζ)
      _ = c := poissonExtension_const hz

theorem poissonExtension_eq_re {R : ℝ} {v : ℂ → ℝ} {z : ℂ}
    (hv : CircleIntegrable v 0 R) (hz : z ∉ sphere 0 |R|) :
    poissonExtension R v z =
      (circleAverage (fun ζ ↦ herglotzRieszKernel 0 z ζ • (v ζ : ℂ)) 0 R).re := by
  simpa only [poissonExtension, ← poissonKernel_eq_re_herglotzRieszKernel,
    Pi.smul_def, smul_eq_mul, Pi.mul_def] using
      (re_circleAverage_herglotzRieszKernel_smul hv hz).symm

theorem poissonExtension_affine {R a b : ℝ} {v : ℂ → ℝ} {z : ℂ}
    (hv : ContinuousOn v (sphere 0 |R|)) (hz : z ∈ ball 0 R) :
    poissonExtension R (fun ζ ↦ a * v ζ + b) z = a * poissonExtension R v z + b := by
  have hp := continuousOn_poissonKernel_sphere hz
  calc
    _ = circleAverage (fun ζ ↦ a * (poissonKernel 0 z ζ * v ζ) +
        poissonKernel 0 z ζ * b) 0 R := by
      apply circleAverage_congr_sphere
      intro ζ _
      ring
    _ = a * poissonExtension R v z + poissonExtension R (fun _ ↦ b) z := by
      have hadd := circleAverage_fun_add
        ((continuousOn_const (c := a)).mul (hp.mul hv)).circleIntegrable'
        (hp.mul (continuousOn_const (c := b))).circleIntegrable'
      simp only [Pi.mul_def] at hadd
      rw [hadd]
      rw [show (fun ζ ↦ a * (poissonKernel 0 z ζ * v ζ)) =
        (fun ζ ↦ a • (poissonKernel 0 z ζ * v ζ)) by rfl, circleAverage_fun_smul]
      rfl
    _ = _ := by rw [poissonExtension_const hz]

theorem poissonExtension_smoothCap_le {R ε c : ℝ} {v : ℂ → ℝ} {z : ℂ}
    (hε : 0 < ε) (hv : ContinuousOn v (sphere 0 |R|)) (hz : z ∈ ball 0 R)
    (hsuper : poissonExtension R v z ≤ v z) :
    poissonExtension R (fun ζ ↦ smoothCap ε c (v ζ)) z ≤ smoothCap ε c (v z) := by
  let d := smoothCapInputDeriv ε c (v z)
  let b := smoothCap ε c (v z) - d * v z
  have hp := continuousOn_poissonKernel_sphere hz
  have hφ : Continuous (smoothCap ε c) :=
    continuous_iff_continuousAt.mpr fun _ ↦ (hasDerivAt_smoothCap_input hε).continuousAt
  calc
    _ ≤ poissonExtension R (fun ζ ↦ d * v ζ + b) z := by
      apply circleAverage_mono (hp.mul (hφ.comp_continuousOn hv)).circleIntegrable'
        (hp.mul ((continuousOn_const.mul hv).add continuousOn_const)).circleIntegrable'
      intro ζ hζ
      apply mul_le_mul_of_nonneg_left _ (poissonKernel_nonneg_on_sphere hz hζ)
      have ht := smoothCap_le_tangent (a := v z) (x := v ζ) (c := c) hε
      dsimp [b, d]
      nlinarith
    _ = d * poissonExtension R v z + b := poissonExtension_affine hv hz
    _ ≤ smoothCap ε c (v z) := by
      have hd : 0 ≤ d := (smoothCapInputDeriv_mem_Icc hε).1
      have hi := mul_le_mul_of_nonneg_left hsuper hd
      dsimp [b]
      linarith

theorem continuousOn_poissonExtension {R : ℝ} {v : ℂ → ℝ}
    (hv : CircleIntegrable v 0 R) :
    ContinuousOn (poissonExtension R v) (sphere (0 : ℂ) |R|)ᶜ := by
  have hvc : CircleIntegrable (fun ζ ↦ (v ζ : ℂ)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hv ⊢
    exact Complex.ofRealCLM.integrable_comp hv
  apply (continuous_re.comp_continuousOn
    (analyticOnNhd_circleAverage_herglotzRieszKernel_smul hvc).continuousOn).congr
  intro z hz
  exact poissonExtension_eq_re hv hz

theorem circleAverage_poissonExtension {R r : ℝ} {v : ℂ → ℝ}
    (hv : CircleIntegrable v 0 R) (hrR : |r| < |R|) :
    circleAverage (poissonExtension R v) 0 r = circleAverage v 0 R := by
  let F : ℂ → ℂ := fun z ↦
    circleAverage (fun ζ ↦ herglotzRieszKernel 0 z ζ • (v ζ : ℂ)) 0 R
  have hvc : CircleIntegrable (fun ζ ↦ (v ζ : ℂ)) 0 R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hv ⊢
    exact Complex.ofRealCLM.integrable_comp hv
  have hF := analyticOnNhd_circleAverage_herglotzRieszKernel_smul hvc
  have hsub : closedBall (0 : ℂ) |r| ⊆ (sphere 0 |R|)ᶜ := by
    intro z hz
    have hz' : ‖z‖ ≤ |r| := by simpa using hz
    simpa using (hz'.trans_lt hrR).ne
  have hdiff : DifferentiableOn ℂ F (closedBall 0 |r|) :=
    fun z hz ↦ (hF z (hsub hz)).differentiableWithinAt
  have hcircle : CircleIntegrable F 0 r :=
    (hdiff.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
  calc
    _ = circleAverage (Complex.reCLM ∘ F) 0 r :=
      circleAverage_congr_sphere fun z hz ↦ poissonExtension_eq_re hv
        (hsub (sphere_subset_closedBall hz))
    _ = (circleAverage F 0 r).re := Complex.reCLM.circleAverage_comp_comm hcircle
    _ = (F 0).re := by
      rw [(hdiff.mono closure_ball_subset_closedBall).diffContOnCl.circleAverage]
    _ = poissonExtension R v 0 := (poissonExtension_eq_re hv (hsub (by simp))).symm
    _ = circleAverage v 0 R := by
      apply circleAverage_congr_sphere
      intro ζ hζ
      have hζ' : ‖ζ‖ = |R| := by simpa using hζ
      have hR : 0 < |R| := (abs_nonneg r).trans_lt hrR
      have hRn : R ≠ 0 := abs_pos.mp hR
      simp [poissonKernel_def, hζ', hRn]

/-- Poisson supermean inequalities imply that the circular means of every upper truncation
decrease with the radius. -/
theorem circleAverage_min_antitone_of_poisson_supermean {R r c : ℝ} {v : ℂ → ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hv : ContinuousOn v (closedBall 0 R))
    (hsuper : ∀ z ∈ ball 0 R, poissonExtension R v z ≤ v z) :
    circleAverage (fun z ↦ min (v z) c) 0 R ≤
      circleAverage (fun z ↦ min (v z) c) 0 r := by
  have hR : 0 ≤ R := hr.trans hrR.le
  have hcap := hv.inf (continuousOn_const (c := c))
  have hcapR : CircleIntegrable (fun z ↦ min (v z) c) 0 R := by
    apply ContinuousOn.circleIntegrable'
    simpa only [abs_of_nonneg hR] using hcap.mono sphere_subset_closedBall
  have habs : |r| < |R| := by simpa only [abs_of_nonneg hr, abs_of_nonneg hR] using hrR
  rw [← circleAverage_poissonExtension hcapR habs]
  have hsub : sphere (0 : ℂ) |r| ⊆ (sphere 0 |R|)ᶜ := by
    intro z hz
    have hz' : ‖z‖ = |r| := by simpa using hz
    simpa [hz'] using habs.ne
  apply circleAverage_mono
    ((continuousOn_poissonExtension hcapR).mono hsub).circleIntegrable'
    (hcap.mono (by simpa only [abs_of_nonneg hr] using
      (sphere_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)))).circleIntegrable'
  intro z hz
  have hzR : z ∈ ball 0 R := by
    have hz' : ‖z‖ = r := by simpa [abs_of_nonneg hr] using hz
    simpa [mem_ball, dist_zero_right, hz'] using hrR
  apply poissonExtension_min_le _ hzR (hsuper z hzR)
  simpa only [abs_of_nonneg hR] using hv.mono sphere_subset_closedBall

theorem circleAverage_antitone_of_poisson_supermean {R r : ℝ} {v : ℂ → ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hv : ContinuousOn v (closedBall 0 R))
    (hsuper : ∀ z ∈ ball 0 R, poissonExtension R v z ≤ v z) :
    circleAverage v 0 R ≤ circleAverage v 0 r := by
  have hR : 0 ≤ R := hr.trans hrR.le
  have hRv : CircleIntegrable v 0 R := by
    apply ContinuousOn.circleIntegrable'
    simpa only [abs_of_nonneg hR] using hv.mono sphere_subset_closedBall
  have habs : |r| < |R| := by simpa only [abs_of_nonneg hr, abs_of_nonneg hR] using hrR
  rw [← circleAverage_poissonExtension hRv habs]
  have hsub : sphere (0 : ℂ) |r| ⊆ (sphere 0 |R|)ᶜ := by
    intro z hz
    have hz' : ‖z‖ = |r| := by simpa using hz
    simpa [hz'] using habs.ne
  apply circleAverage_mono
    ((continuousOn_poissonExtension hRv).mono hsub).circleIntegrable'
    (hv.mono (by simpa only [abs_of_nonneg hr] using
      (sphere_subset_closedBall.trans (closedBall_subset_closedBall hrR.le)))).circleIntegrable'
  intro z hz
  apply hsuper
  have hz' : ‖z‖ = r := by simpa [abs_of_nonneg hr] using hz
  simpa [mem_ball, dist_zero_right, hz'] using hrR

theorem circleAverage_smoothCap_antitone_of_poisson_supermean
    {R r ε c : ℝ} {v : ℂ → ℝ} (hε : 0 < ε)
    (hr : 0 ≤ r) (hrR : r < R) (hv : ContinuousOn v (closedBall 0 R))
    (hsuper : ∀ z ∈ ball 0 R, poissonExtension R v z ≤ v z) :
    circleAverage (fun z ↦ smoothCap ε c (v z)) 0 R ≤
      circleAverage (fun z ↦ smoothCap ε c (v z)) 0 r := by
  have hφ : Continuous (smoothCap ε c) :=
    continuous_iff_continuousAt.mpr fun _ ↦ (hasDerivAt_smoothCap_input hε).continuousAt
  apply circleAverage_antitone_of_poisson_supermean hr hrR (hφ.comp_continuousOn hv)
  intro z hz
  apply poissonExtension_smoothCap_le hε _ hz (hsuper z hz)
  simpa only [abs_of_nonneg (hr.trans hrR.le)] using hv.mono sphere_subset_closedBall

theorem circleAverage_smoothCap_bounds {ε c r : ℝ} {v : ℂ → ℝ} (hε : 0 < ε)
    (hv : ContinuousOn v (sphere 0 |r|)) :
    circleAverage (fun z ↦ min (v z) c) 0 r ≤
        circleAverage (fun z ↦ smoothCap ε c (v z)) 0 r ∧
      circleAverage (fun z ↦ smoothCap ε c (v z)) 0 r ≤
        circleAverage (fun z ↦ min (v z) c) 0 r + ε / 2 := by
  have hφ : Continuous (smoothCap ε c) :=
    continuous_iff_continuousAt.mpr fun _ ↦ (hasDerivAt_smoothCap_input hε).continuousAt
  have hmin := (hv.inf (continuousOn_const (c := c))).circleIntegrable'
  have hcap := (hφ.comp_continuousOn hv).circleIntegrable'
  constructor
  · exact circleAverage_mono hmin hcap fun _ _ ↦ min_le_smoothCap hε.le
  · have hi := circleAverage_mono hcap (hmin.add (circleIntegrable_const (ε / 2) 0 r))
      (fun z _ ↦ smoothCap_le_min_add (ε := ε) (c := c) (x := v z))
    simpa only [circleAverage_add hmin (circleIntegrable_const (ε / 2) 0 r),
      circleAverage_const, Function.comp_def] using hi

/-- Uniform approximation transfers decrease of smooth truncated means to exact truncation. -/
theorem circleAverage_min_le_of_smoothCap_le {r R c : ℝ} {v : ℂ → ℝ}
    (hr : ContinuousOn v (sphere 0 |r|)) (hR : ContinuousOn v (sphere 0 |R|))
    (hsmooth : ∀ ε : ℝ, 0 < ε →
      circleAverage (fun z ↦ smoothCap ε c (v z)) 0 R ≤
        circleAverage (fun z ↦ smoothCap ε c (v z)) 0 r) :
    circleAverage (fun z ↦ min (v z) c) 0 R ≤
      circleAverage (fun z ↦ min (v z) c) 0 r := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hε : 0 < 2 * δ := mul_pos (by norm_num) hδ
  have hupper := (circleAverage_smoothCap_bounds (c := c) hε hr).2
  have hlower := (circleAverage_smoothCap_bounds (c := c) hε hR).1
  have hmono := hsmooth (2 * δ) hε
  linarith

end BergmanWeakType
