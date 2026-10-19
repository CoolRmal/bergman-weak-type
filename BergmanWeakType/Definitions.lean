/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Bergman projections and their weak type constants -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

/-- The open unit disk in the complex plane. -/
def disk : Set ℂ := Metric.ball 0 1

/-- Euclidean area divided by π. -/
def area : Measure ℂ := ENNReal.ofReal Real.pi⁻¹ • volume

/-- Probability area on the unit disk. -/
def diskArea : Measure ℂ := area.restrict disk

/-- Standard radial weighted area, for parameters greater than −1. -/
def weightedArea (α : ℝ) : Measure ℂ :=
  diskArea.withDensity (fun z ↦ ENNReal.ofReal ((α + 1) * (1 - ‖z‖ ^ 2) ^ α))

/-- The unweighted Bergman kernel, normalized for area divided by π. -/
def kernel (z w : ℂ) : ℂ := (1 - z * star w)⁻¹ ^ 2

/-- The complex Bergman projection on the unit disk. -/
def projection (f : ℂ → ℂ) (z : ℂ) : ℂ := ∫ w, kernel z w * f w ∂diskArea

/-- The positive Bergman operator on the unit disk. -/
def positiveProjection (f : ℂ → ℂ) (z : ℂ) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal ‖kernel z w‖ * ‖f w‖ₑ ∂diskArea

/-- The weighted kernel uses the principal complex power; its base has positive real part. -/
def weightedKernel (α : ℝ) (z w : ℂ) : ℂ := (1 - z * star w) ^ (-(α + 2) : ℂ)

/-- The standard weighted complex Bergman projection. -/
def weightedProjection (α : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ w, weightedKernel α z w * f w ∂weightedArea α

/-- The standard weighted positive Bergman operator, with its full extended integral. -/
def weightedPositiveProjection (α : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal ‖weightedKernel α z w‖ * ‖f w‖ₑ ∂weightedArea α

/-- A weak type (1,1) bound for an operator with nonnegative extended-real output. -/
def IsWeakTypeBound (μ : Measure ℂ) (T : (ℂ → ℂ) → ℂ → ℝ≥0∞) (C : ℝ≥0∞) : Prop :=
  ∀ f : ℂ → ℂ, Integrable f μ → ∀ t : ℝ, 0 < t →
    ENNReal.ofReal t * μ {z | ENNReal.ofReal t < T f z} ≤ C * ∫⁻ z, ‖f z‖ₑ ∂μ

/-- The optimal weak type (1,1) constant, including infinity when no finite bound exists. -/
def weakTypeConstant (μ : Measure ℂ) (T : (ℂ → ℂ) → ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  sInf {C | IsWeakTypeBound μ T C}

/-- The sharp constant of the positive weighted kernel. -/
def gammaConstant (α : ℝ) : ℝ := Real.Gamma (α + 1) / Real.Gamma (1 + α / 2) ^ 2

/-- The boundary point-mass lower bound for the complex weighted projection. -/
def boundaryConstant (α : ℝ) : ℝ :=
  (α + 1) / (α + 2) * gammaConstant α

end BergmanWeakType
