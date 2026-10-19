/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Definitions
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Bergman kernels on planar domains

The kernel is characterized by its usual holomorphic, Hermitian and L² reproducing properties.
Existence and its relation to orthogonal projection are separate analytic proof obligations.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

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

end BergmanWeakType
