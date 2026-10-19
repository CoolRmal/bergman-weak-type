/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Linarith
public import BergmanWeakType.Weighted.SmoothCap

/-! # Radial flux and decreasing circular means

This module isolates the one-dimensional consequences of the polar divergence inequality.
-/

@[expose] public section

open MeasureTheory Set

namespace BergmanWeakType.Weighted

/-- A periodic derivative has zero integral over one period. -/
theorem integral_periodic_derivative_eq_zero {g g' : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hg : ∀ θ ∈ Icc 0 T, HasDerivAt g (g' θ) θ)
    (hgi : IntervalIntegrable g' volume 0 T) (hperiod : g T = g 0) :
    (∫ θ in (0 : ℝ)..T, g' θ) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (by simpa only [uIcc_of_le hT] using hg) hgi, hperiod, sub_self]

/-- A nonincreasing radial flux vanishing at the origin forces the mean to decrease. -/
theorem antitoneOn_of_radial_flux {M M' w F F' : ℝ → ℝ}
    (hM : ContinuousOn M (Ico 0 1))
    (hMd : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt M (M' r) r)
    (hw : ∀ r ∈ Ioo (0 : ℝ) 1, 0 < w r)
    (hF : ContinuousOn F (Ico 0 1)) (hFzero : F 0 = 0)
    (hFd : ∀ r ∈ Ioo (0 : ℝ) 1, HasDerivAt F (F' r) r)
    (hFnonpos : ∀ r ∈ Ioo (0 : ℝ) 1, F' r ≤ 0)
    (hflux : ∀ r ∈ Ioo (0 : ℝ) 1, F r = r * w r * M' r) :
    AntitoneOn M (Ico 0 1) := by
  have hanti : AntitoneOn F (Ico 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ico 0 1) hF
    · intro r hr
      exact (hFd r (by simpa only [interior_Ico] using hr)).hasDerivWithinAt
    · simpa only [interior_Ico] using hFnonpos
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ico 0 1) hM
  · intro r hr
    exact (hMd r (by simpa only [interior_Ico] using hr)).hasDerivWithinAt
  · intro r hr
    have hr' : r ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Ico] using hr
    have hle := hanti (show (0 : ℝ) ∈ Ico 0 1 by norm_num)
      ⟨hr'.1.le, hr'.2⟩ hr'.1.le
    rw [hFzero, hflux r hr'] at hle
    exact nonpos_of_mul_nonpos_right hle (mul_pos hr'.1 (hw r hr'))

/-- Integration of the angular divergence removes it from the radial flux inequality. -/
theorem integral_radial_term_nonpos {A B : ℝ → ℝ} {T c : ℝ}
    (hT : 0 ≤ T) (hA : IntervalIntegrable A volume 0 T)
    (hB : IntervalIntegrable B volume 0 T) (hBzero : (∫ θ in (0 : ℝ)..T, B θ) = 0)
    (hineq : ∀ θ ∈ Icc 0 T, A θ + c * B θ ≤ 0) :
    (∫ θ in (0 : ℝ)..T, A θ) ≤ 0 := by
  have hi := intervalIntegral.integral_mono_on hT (hA.add (hB.const_mul c))
    (intervalIntegrable_const (c := (0 : ℝ))) hineq
  rw [intervalIntegral.integral_add hA (hB.const_mul c),
    intervalIntegral.integral_const_mul, hBzero, mul_zero, add_zero,
    intervalIntegral.integral_zero] at hi
  exact hi

/-- Differentiating the first derivative of a smooth truncation of a one-variable function. -/
theorem hasDerivAt_smoothCap_comp_first {ε c x : ℝ} {U U' : ℝ → ℝ} {U'' : ℝ}
    (hε : 0 < ε) (hU : HasDerivAt U (U' x) x) (hU' : HasDerivAt U' U'' x) :
    HasDerivAt (fun y ↦ smoothCapInputDeriv ε c (U y) * U' y)
      ((-(ε ^ 2) / (2 * Real.sqrt ((U x - c) ^ 2 + ε ^ 2) ^ 3)) * (U' x) ^ 2 +
        smoothCapInputDeriv ε c (U x) * U'') x := by
  convert ((hasDerivAt_smoothCapInputDeriv (c := c) hε).comp x hU).mul hU' using 1 <;>
    simp only [Function.comp_def, Pi.mul_def]
  ring

/-- Increasing concave truncation preserves the polar divergence inequality. -/
theorem smoothCap_polar_flux_nonpos {ε c u r w w' ur urr uθ uθθ : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hw : 0 < w)
    (hL : r * w * urr + (w + r * w') * ur + (w / r) * uθθ ≤ 0) :
    let d₁ := smoothCapInputDeriv ε c u
    let d₂ := -(ε ^ 2) / (2 * Real.sqrt ((u - c) ^ 2 + ε ^ 2) ^ 3)
    r * w * (d₂ * ur ^ 2 + d₁ * urr) +
      (w + r * w') * (d₁ * ur) + (w / r) * (d₂ * uθ ^ 2 + d₁ * uθθ) ≤ 0 := by
  dsimp only
  have hd₁ := (smoothCapInputDeriv_mem_Icc (c := c) (x := u) hε).1
  have hd₂ := smoothCap_secondDeriv_nonpos (ε := ε) (c := c) (x := u)
  have hfirst := mul_nonpos_of_nonneg_of_nonpos hd₁ hL
  have hsecond := mul_nonpos_of_nonpos_of_nonneg hd₂
    (show 0 ≤ r * w * ur ^ 2 + (w / r) * uθ ^ 2 by positivity)
  nlinarith

/-- Dividing an elliptic supersolution by a positive radial solution removes the potential term.
The displayed first and second derivatives are the ordinary quotient-rule expressions. -/
theorem quotient_polar_operator_nonpos {F Fr Frr Fθθ J Jr Jrr a b r : ℝ}
    (hJ : 0 < J) (hr : r ≠ 0) (hJode : Jrr + a * Jr + b * J = 0)
    (hFode : Frr + a * Fr + Fθθ / r ^ 2 + b * F ≤ 0) :
    (Frr / J - F * Jrr / J ^ 2 - 2 * Fr * Jr / J ^ 2 + 2 * F * Jr ^ 2 / J ^ 3) +
      (a + 2 * Jr / J) * ((Fr * J - F * Jr) / J ^ 2) + (Fθθ / J) / r ^ 2 ≤ 0 := by
  have heq : J * ((Frr / J - F * Jrr / J ^ 2 - 2 * Fr * Jr / J ^ 2 +
        2 * F * Jr ^ 2 / J ^ 3) + (a + 2 * Jr / J) * ((Fr * J - F * Jr) / J ^ 2) +
        (Fθθ / J) / r ^ 2) =
      Frr + a * Fr + Fθθ / r ^ 2 + b * F - (F / J) * (Jrr + a * Jr + b * J) := by
    field_simp [hJ.ne', hr]
    ring
  rw [hJode, mul_zero, sub_zero] at heq
  exact nonpos_of_mul_nonpos_right (heq.trans_le hFode) hJ

end BergmanWeakType.Weighted
