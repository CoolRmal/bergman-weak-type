module

public import BergmanWeakType.Definitions
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith

/-! # Elementary identities for the Bergman kernels

These lemmas establish the kernels' normalizations and the pointwise comparison of the complex
projection with its positive majorant. They do not assert a sharp weak type estimate.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

@[simp]
theorem mem_disk_iff (z : ℂ) : z ∈ disk ↔ ‖z‖ < 1 := by
  simp [disk, Metric.mem_ball, dist_zero_right]

theorem kernel_denominator_ne_zero {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk) :
    1 - z * star w ≠ 0 := by
  have hz' : ‖z‖ < 1 := (mem_disk_iff z).mp hz
  have hw' : ‖w‖ < 1 := (mem_disk_iff w).mp hw
  have hmul : ‖z * star w‖ < 1 := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_right (norm_nonneg z) hw'.le).trans_lt hz'
  intro h
  have hzw : z * star w = 1 := (sub_eq_zero.mp h).symm
  rw [hzw, norm_one] at hmul
  exact (lt_irrefl 1) hmul

/-- The kernel's base lies in the right half-plane on the disk. -/
theorem kernel_denominator_re_pos {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk) :
    0 < (1 - z * star w).re := by
  have hmul : ‖z * star w‖ < 1 := by
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_right (norm_nonneg z) ((mem_disk_iff w).mp hw).le).trans_lt
      ((mem_disk_iff z).mp hz)
  simpa only [Complex.sub_re, Complex.one_re] using
    sub_pos.mpr ((Complex.re_le_norm _).trans_lt hmul)

@[simp]
theorem norm_kernel (z w : ℂ) : ‖kernel z w‖ = ‖1 - z * star w‖⁻¹ ^ 2 := by
  simp [kernel, norm_pow, norm_inv]

theorem kernel_ne_zero {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk) : kernel z w ≠ 0 := by
  exact pow_ne_zero _ (inv_ne_zero (kernel_denominator_ne_zero hz hw))

@[simp]
theorem kernel_zero_left (w : ℂ) : kernel 0 w = 1 := by
  simp [kernel]

@[simp]
theorem kernel_zero_right (z : ℂ) : kernel z 0 = 1 := by
  simp [kernel]

@[simp]
theorem projection_at_zero (f : ℂ → ℂ) : projection f 0 = ∫ w, f w ∂diskArea := by
  simp [projection]

@[simp]
theorem positiveProjection_at_zero (f : ℂ → ℂ) :
    positiveProjection f 0 = ∫⁻ w, ‖f w‖ₑ ∂diskArea := by
  simp [positiveProjection]

/-- The positive extended integral bounds the complex Bochner integral pointwise. -/
theorem enorm_projection_le_positiveProjection (f : ℂ → ℂ) (z : ℂ) :
    ‖projection f z‖ₑ ≤ positiveProjection f z := by
  simpa [projection, positiveProjection, enorm_mul, ← ofReal_norm] using
    (enorm_integral_le_lintegral_enorm (μ := diskArea) (fun w ↦ kernel z w * f w))

/-- The weighted pointwise comparison requires no weak type estimate. -/
theorem enorm_weightedProjection_le_weightedPositiveProjection (α : ℝ) (f : ℂ → ℂ)
    (z : ℂ) : ‖weightedProjection α f z‖ₑ ≤ weightedPositiveProjection α f z := by
  simpa [weightedProjection, weightedPositiveProjection, enorm_mul, ← ofReal_norm] using
    (enorm_integral_le_lintegral_enorm (μ := weightedArea α)
      (fun w ↦ weightedKernel α z w * f w))

@[simp]
theorem norm_weightedKernel (α : ℝ) (z w : ℂ) :
    ‖weightedKernel α z w‖ = ‖1 - z * star w‖ ^ (-(α + 2)) := by
  simpa [weightedKernel] using Complex.norm_cpow_real (1 - z * star w) (-(α + 2))

@[simp]
theorem weightedKernel_zero (z w : ℂ) : weightedKernel 0 z w = kernel z w := by
  simp [weightedKernel, kernel, Complex.cpow_neg, ← inv_pow]

@[simp]
theorem weightedArea_zero : weightedArea 0 = diskArea := by
  simp [weightedArea]

@[simp]
theorem weightedProjection_zero (f : ℂ → ℂ) : weightedProjection 0 f = projection f := by
  funext z
  simp [weightedProjection, projection]

@[simp]
theorem weightedPositiveProjection_zero (f : ℂ → ℂ) :
    weightedPositiveProjection 0 f = positiveProjection f := by
  funext z
  simp [weightedPositiveProjection, positiveProjection]

@[simp]
theorem gammaConstant_zero : gammaConstant 0 = 1 := by
  simp [gammaConstant]

theorem gammaConstant_pos {α : ℝ} (hα : -1 < α) : 0 < gammaConstant α := by
  apply div_pos
  · exact Real.Gamma_pos_of_pos (by linarith)
  · exact sq_pos_of_pos (Real.Gamma_pos_of_pos (by linarith))

end BergmanWeakType
