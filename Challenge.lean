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
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Main statements for Bergman weak type constants

This standalone statement surface imports only mathlib. Its theorem holes are intentional.
The comparison must check the same declarations in Solution, with only standard Lean axioms.
All seven statements below are currently proof targets, not completed formalizations.
-/

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

/-- The standard reproducing-kernel characterization of the Bergman kernel of a planar domain. -/
structure IsBergmanKernel (Ω : Set ℂ) (K : ℂ → ℂ → ℂ) : Prop where
  holomorphic : ∀ w ∈ Ω, DifferentiableOn ℂ (fun z ↦ K z w) Ω
  hermitian : ∀ z ∈ Ω, ∀ w ∈ Ω, K z w = star (K w z)
  squareIntegrable : ∀ z ∈ Ω, MemLp (fun w ↦ K z w) 2 (area.restrict Ω)
  reproduces : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f Ω → MemLp f 2 (area.restrict Ω) →
    ∀ z ∈ Ω, (∫ w, K z w * f w ∂area.restrict Ω) = f z

/-- The positive Bergman operator of a domain with its normalized-area kernel. -/
def domainPositiveProjection (Ω : Set ℂ) (K : ℂ → ℂ → ℂ) (f : ℂ → ℂ)
    (z : ℂ) : ℝ≥0∞ := ∫⁻ w, ENNReal.ofReal ‖K z w‖ * ‖f w‖ₑ ∂area.restrict Ω

/-- The unweighted disk Bergman projection has sharp weak type (1,1) constant one. -/
theorem projection_constant_eq_one :
    weakTypeConstant diskArea (fun f z ↦ ‖projection f z‖ₑ) = 1 := by
  sorry

/-- The positive unweighted disk Bergman operator has sharp weak constant one. -/
theorem positiveProjection_constant_eq_one :
    weakTypeConstant diskArea positiveProjection = 1 := by
  sorry

/-- The exact positive weighted constant for every standard radial weight parameter. -/
theorem weightedPositiveProjection_constant_eq (α : ℝ) (hα : -1 < α) :
    weakTypeConstant (weightedArea α) (weightedPositiveProjection α) =
      ENNReal.ofReal (gammaConstant α) := by
  sorry

/-- Reproduction of constants gives the universal complex weighted lower bound. -/
theorem one_le_weightedProjection_constant (α : ℝ) (hα : -1 < α) :
    1 ≤ weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) := by
  sorry

/-- Positive-kernel domination gives the complex weighted upper bound. -/
theorem weightedProjection_constant_le (α : ℝ) (hα : -1 < α) :
    weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) ≤
      ENNReal.ofReal (gammaConstant α) := by
  sorry

/-- Boundary concentration gives the additional complex lower bound for nonnegative parameters. -/
theorem boundaryConstant_le_weightedProjection_constant (α : ℝ) (hα : 0 ≤ α) :
    ENNReal.ofReal (boundaryConstant α) ≤
      weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) := by
  sorry

/-- Among bounded simply connected domains, positive weak constant one characterizes disks. -/
theorem positive_constant_eq_one_iff_disk (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsSimplyConnected Ω)
    (K : ℂ → ℂ → ℂ) (hK : IsBergmanKernel Ω K) :
    weakTypeConstant (area.restrict Ω) (domainPositiveProjection Ω K) = 1 ↔
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ Ω = Metric.ball c R := by
  sorry

end BergmanWeakType
