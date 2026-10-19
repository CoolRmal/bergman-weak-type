/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.Order.Compact

/-! # Differentiating compact families against integrable densities -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace BergmanWeakType.Weighted

theorem integrable_mul_of_continuousOn_compact {X : Type*} [TopologicalSpace X]
    [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} {K : Set X}
    (hK : IsCompact K) (hμ : ∀ᵐ w ∂μ, w ∈ K) {f g : X → ℝ}
    (hf : Integrable f μ) (hg : ContinuousOn g K) :
    Integrable (fun w ↦ g w * f w) μ := by
  have hm : AEStronglyMeasurable g μ := by
    simpa only [Measure.restrict_eq_self_of_ae_mem hμ] using
      hg.aestronglyMeasurable hK.isClosed.measurableSet (μ := μ)
  obtain ⟨M, hM⟩ := hK.bddAbove_image hg.norm
  apply hf.bdd_mul hm
  exact hμ.mono fun w hw ↦ hM (mem_image_of_mem _ hw)

theorem continuousOn_integral_mul_of_compact {μ : Measure ℂ} {K S : Set ℂ}
    (hK : IsCompact K) (hμ : ∀ᵐ w ∂μ, w ∈ K) (hS : IsCompact S)
    {f : ℂ → ℝ} (hf : Integrable f μ) {F : ℂ → ℂ → ℝ}
    (hF : ContinuousOn (fun p : ℂ × ℂ ↦ F p.1 p.2) (S ×ˢ K)) :
    ContinuousOn (fun z ↦ ∫ w, F z w * f w ∂μ) S := by
  have hslice {z : ℂ} (hz : z ∈ S) : ContinuousOn (F z) K :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn fun w hw ↦ ⟨hz, hw⟩
  obtain ⟨M, hM⟩ := (hS.prod hK).bddAbove_image hF.norm
  apply continuousOn_of_dominated (bound := fun w ↦ M * ‖f w‖)
    (fun z hz ↦ (integrable_mul_of_continuousOn_compact hK hμ hf (hslice hz)).aestronglyMeasurable)
    (fun z hz ↦ hμ.mono fun w hw ↦ ?_) (hf.norm.const_mul M)
    (hμ.mono fun w hw ↦ ?_)
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (hM (mem_image_of_mem (fun p : ℂ × ℂ ↦ ‖F p.1 p.2‖)
        (show (z, w) ∈ S ×ˢ K from ⟨hz, hw⟩))) (norm_nonneg _)
  · exact (hF.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun z hz ↦ ⟨hz, hw⟩)).mul_const _

/-- Continuous kernel derivatives on a compact parameter cylinder can be integrated against any
integrable density. Compactness supplies the common domination needed by differentiation. -/
theorem hasDerivAt_integral_mul_of_continuousOn_compact {μ : Measure ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hμ : ∀ᵐ w ∂μ, w ∈ K) {S : Set ℝ}
    (hS : IsCompact S) {x : ℝ} (hSx : S ∈ nhds x) {f : ℂ → ℝ}
    (hf : Integrable f μ) {F F' : ℝ → ℂ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℂ ↦ F p.1 p.2) (S ×ˢ K))
    (hF' : ContinuousOn (fun p : ℝ × ℂ ↦ F' p.1 p.2) (S ×ˢ K))
    (hderiv : ∀ w ∈ K, ∀ u ∈ S, HasDerivAt (fun v ↦ F v w) (F' u w) u) :
    Integrable (fun w ↦ F' x w * f w) μ ∧
      HasDerivAt (fun u ↦ ∫ w, F u w * f w ∂μ) (∫ w, F' x w * f w ∂μ) x := by
  have hx : x ∈ S := mem_of_mem_nhds hSx
  have hslice {G : ℝ → ℂ → ℝ}
      (hG : ContinuousOn (fun p : ℝ × ℂ ↦ G p.1 p.2) (S ×ˢ K))
      {u : ℝ} (hu : u ∈ S) : ContinuousOn (G u) K := by
    exact hG.comp (continuous_const.prodMk continuous_id).continuousOn fun w hw ↦ ⟨hu, hw⟩
  obtain ⟨M, hM⟩ := (hS.prod hK).bddAbove_image hF'.norm
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u w ↦ F u w * f w) (F' := fun u w ↦ F' u w * f w) hSx ?_
    (integrable_mul_of_continuousOn_compact hK hμ hf (hslice hF hx))
    (integrable_mul_of_continuousOn_compact hK hμ hf (hslice hF' hx)).aestronglyMeasurable
    (bound := fun w ↦ M * ‖f w‖) ?_ (hf.norm.const_mul M) ?_
  · exact Filter.mem_of_superset hSx fun u hu ↦
      (integrable_mul_of_continuousOn_compact hK hμ hf (hslice hF hu)).aestronglyMeasurable
  · exact hμ.mono fun w hw u hu ↦ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hM (mem_image_of_mem (fun p : ℝ × ℂ ↦ ‖F' p.1 p.2‖)
          (show (u, w) ∈ S ×ˢ K from ⟨hu, hw⟩))) (norm_nonneg _)
  · exact hμ.mono fun w hw u hu ↦ (hderiv w hw u hu).mul_const (f w)

end BergmanWeakType.Weighted
