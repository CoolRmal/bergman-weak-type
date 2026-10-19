/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.KernelPDE
public import BergmanWeakType.Weighted.CompactIntegral
public import Mathlib.Topology.Order.Basic

/-! # Differential equations for positive kernel integrals

The source is allowed to be any compactly supported measure in the closed disk. This includes
both weighted area potentials and the circular boundary normalizer.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace BergmanWeakType.Weighted

def powerKernelX (q a b x y : ℝ) : ℝ :=
  2 * q * ((a ^ 2 + b ^ 2) * x - a) * powerKernel (q - 1) a b x y

def powerKernelXX (q a b x y : ℝ) : ℝ :=
  2 * q * (a ^ 2 + b ^ 2) * powerKernel (q - 1) a b x y +
    4 * q * (q - 1) * ((a ^ 2 + b ^ 2) * x - a) ^ 2 * powerKernel (q - 2) a b x y

def kernelPotential (q : ℝ) (a b : ℂ → ℝ) (μ : Measure ℂ) (f : ℂ → ℝ) (x y : ℝ) : ℝ :=
  ∫ w, powerKernel q (a w) (b w) x y * f w ∂μ

theorem denominator_pos_coordinates {a b x y : ℝ}
    (hz : x ^ 2 + y ^ 2 < 1) (hw : a ^ 2 + b ^ 2 ≤ 1) :
    0 < denominator a b x y := by
  have hz' : (⟨x, y⟩ : ℂ) ∈ disk := by
    apply (mem_disk_iff _).mpr
    have heq : ‖(⟨x, y⟩ : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply]
      ring
    nlinarith [norm_nonneg (⟨x, y⟩ : ℂ)]
  have hw' : ‖(⟨a, b⟩ : ℂ)‖ ≤ 1 := by
    have heq : ‖(⟨a, b⟩ : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply]
      ring
    nlinarith [norm_nonneg (⟨a, b⟩ : ℂ)]
  exact denominator_pos hz' hw'

theorem powerKernelX_hasDerivAt (q a b x y : ℝ) (hd : 0 < denominator a b x y) :
    HasDerivAt (fun u ↦ powerKernelX q a b u y) (powerKernelXX q a b x y) x := by
  apply (powerKernel_hasDerivAt_deriv_x q a b x y hd).congr_of_eventuallyEq
  have hpos : ∀ᶠ u in nhds x, 0 < denominator a b u y :=
    (denominator_hasDerivAt_x a b x y).continuousAt.eventually (lt_mem_nhds hd)
  exact hpos.mono fun u hu ↦ (powerKernel_deriv_x q a b u y hu).symm

theorem exists_coordinate_interval {x y : ℝ} (hxy : x ^ 2 + y ^ 2 < 1) :
    ∃ S : Set ℝ, IsCompact S ∧ S ∈ nhds x ∧ ∀ u ∈ S, u ^ 2 + y ^ 2 < 1 := by
  have hn : {u : ℝ | u ^ 2 + y ^ 2 < 1} ∈ nhds x :=
    ((continuous_id.pow 2).add_const (y ^ 2)).continuousAt.eventually (gt_mem_nhds hxy)
  obtain ⟨l, r, _, hmem, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds hn
  exact ⟨Icc l r, isCompact_Icc, hmem, hsub⟩

section Cylinder

variable {K : Set ℂ} {S : Set ℝ} {a b : ℂ → ℝ}
  (ha : ContinuousOn a K) (hb : ContinuousOn b K) (y : ℝ)

include ha hb

theorem continuousOn_denominator_cylinder :
    ContinuousOn (fun p : ℝ × ℂ ↦ denominator (a p.2) (b p.2) p.1 y) (S ×ˢ K) := by
  have ha' : ContinuousOn (fun p : ℝ × ℂ ↦ a p.2) (S ×ˢ K) :=
    ha.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)
  have hb' : ContinuousOn (fun p : ℝ × ℂ ↦ b p.2) (S ×ˢ K) :=
    hb.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)
  exact (((ha'.pow 2).add (hb'.pow 2)).mul
    ((continuous_fst.pow 2).add_const (y ^ 2)).continuousOn).sub
      ((ha'.mul continuous_fst.continuousOn).add (hb'.mul_const y) |>.const_mul 2) |>.add_const 1

variable (hsource : ∀ w ∈ K, a w ^ 2 + b w ^ 2 ≤ 1)
  (htarget : ∀ u ∈ S, u ^ 2 + y ^ 2 < 1)

include hsource htarget

theorem continuousOn_powerKernel_cylinder (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℂ ↦ powerKernel q (a p.2) (b p.2) p.1 y) (S ×ˢ K) := by
  apply (continuousOn_denominator_cylinder ha hb y).rpow_const
  intro p hp
  exact Or.inl (denominator_pos_coordinates (htarget p.1 hp.1) (hsource p.2 hp.2)).ne'

theorem continuousOn_powerKernelX_cylinder (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℂ ↦ powerKernelX q (a p.2) (b p.2) p.1 y) (S ×ˢ K) := by
  have ha' : ContinuousOn (fun p : ℝ × ℂ ↦ a p.2) (S ×ˢ K) :=
    ha.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)
  have hb' : ContinuousOn (fun p : ℝ × ℂ ↦ b p.2) (S ×ˢ K) :=
    hb.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)
  exact (((((ha'.pow 2).add (hb'.pow 2)).mul continuous_fst.continuousOn).sub ha').const_mul
    (2 * q)).mul (continuousOn_powerKernel_cylinder ha hb y hsource htarget (q - 1))

theorem continuousOn_powerKernelXX_cylinder (q : ℝ) :
    ContinuousOn (fun p : ℝ × ℂ ↦ powerKernelXX q (a p.2) (b p.2) p.1 y) (S ×ˢ K) := by
  have ha' : ContinuousOn (fun p : ℝ × ℂ ↦ a p.2) (S ×ˢ K) :=
    ha.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)
  have hb' : ContinuousOn (fun p : ℝ × ℂ ↦ b p.2) (S ×ˢ K) :=
    hb.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)
  exact ((((ha'.pow 2).add (hb'.pow 2)).const_mul (2 * q)).mul
    (continuousOn_powerKernel_cylinder ha hb y hsource htarget (q - 1))).add
    ((((((ha'.pow 2).add (hb'.pow 2)).mul continuous_fst.continuousOn).sub ha').pow 2).const_mul
      (4 * q * (q - 1)) |>.mul
      (continuousOn_powerKernel_cylinder ha hb y hsource htarget (q - 2)))

end Cylinder

theorem kernelPotential_swap (q : ℝ) (a b : ℂ → ℝ) (μ : Measure ℂ) (f : ℂ → ℝ)
    (x y : ℝ) : kernelPotential q a b μ f x y = kernelPotential q b a μ f y x := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w ↦ by
    dsimp only
    rw [powerKernel_swap q (a w) (b w) x y]

section Integral

variable {K : Set ℂ} {a b : ℂ → ℝ} {μ : Measure ℂ} {f : ℂ → ℝ}
  (hK : IsCompact K) (hμ : ∀ᵐ w ∂μ, w ∈ K) (hf : Integrable f μ)
  (ha : ContinuousOn a K) (hb : ContinuousOn b K)
  (hsource : ∀ w ∈ K, a w ^ 2 + b w ^ 2 ≤ 1)

include hK hμ hf ha hb hsource

theorem kernelPotential_hasDerivAt_x (q : ℝ) {x y : ℝ} (hxy : x ^ 2 + y ^ 2 < 1) :
    Integrable (fun w ↦ powerKernelX q (a w) (b w) x y * f w) μ ∧
      HasDerivAt (fun u ↦ kernelPotential q a b μ f u y)
        (∫ w, powerKernelX q (a w) (b w) x y * f w ∂μ) x := by
  obtain ⟨S, hS, hSx, htarget⟩ := exists_coordinate_interval hxy
  apply hasDerivAt_integral_mul_of_continuousOn_compact hK hμ hS hSx hf
    (continuousOn_powerKernel_cylinder ha hb y hsource htarget q)
    (continuousOn_powerKernelX_cylinder ha hb y hsource htarget q)
  intro w hw u hu
  exact powerKernel_hasDerivAt_x q (a w) (b w) u y
    (denominator_pos_coordinates (htarget u hu) (hsource w hw))

theorem kernelPotential_hasDerivAt_xx (q : ℝ) {x y : ℝ} (hxy : x ^ 2 + y ^ 2 < 1) :
    Integrable (fun w ↦ powerKernelXX q (a w) (b w) x y * f w) μ ∧
      HasDerivAt (fun u ↦ deriv (fun v ↦ kernelPotential q a b μ f v y) u)
        (∫ w, powerKernelXX q (a w) (b w) x y * f w ∂μ) x := by
  obtain ⟨S, hS, hSx, htarget⟩ := exists_coordinate_interval hxy
  have hi := hasDerivAt_integral_mul_of_continuousOn_compact hK hμ hS hSx hf
    (continuousOn_powerKernelX_cylinder ha hb y hsource htarget q)
    (continuousOn_powerKernelXX_cylinder ha hb y hsource htarget q)
    (fun w hw u hu ↦ powerKernelX_hasDerivAt q (a w) (b w) u y
      (denominator_pos_coordinates (htarget u hu) (hsource w hw)))
  refine ⟨hi.1, hi.2.congr_of_eventuallyEq ?_⟩
  exact Filter.mem_of_superset hSx fun u hu ↦
    (kernelPotential_hasDerivAt_x hK hμ hf ha hb hsource q (htarget u hu)).2.deriv

theorem kernelPotential_hasDerivAt_y (q : ℝ) {x y : ℝ} (hxy : x ^ 2 + y ^ 2 < 1) :
    Integrable (fun w ↦ powerKernelX q (b w) (a w) y x * f w) μ ∧
      HasDerivAt (fun u ↦ kernelPotential q a b μ f x u)
        (∫ w, powerKernelX q (b w) (a w) y x * f w ∂μ) y := by
  have h := kernelPotential_hasDerivAt_x hK hμ hf hb ha
    (fun w hw ↦ by simpa only [add_comm] using hsource w hw) q
    (show y ^ 2 + x ^ 2 < 1 by simpa only [add_comm] using hxy)
  have hfun : (fun u ↦ kernelPotential q a b μ f x u) =
      (fun u ↦ kernelPotential q b a μ f u x) :=
    funext fun u ↦ kernelPotential_swap q a b μ f x u
  simpa only [hfun] using h

theorem kernelPotential_hasDerivAt_yy (q : ℝ) {x y : ℝ} (hxy : x ^ 2 + y ^ 2 < 1) :
    Integrable (fun w ↦ powerKernelXX q (b w) (a w) y x * f w) μ ∧
      HasDerivAt (fun u ↦ deriv (fun v ↦ kernelPotential q a b μ f x v) u)
        (∫ w, powerKernelXX q (b w) (a w) y x * f w ∂μ) y := by
  have h := kernelPotential_hasDerivAt_xx hK hμ hf hb ha
    (fun w hw ↦ by simpa only [add_comm] using hsource w hw) q
    (show y ^ 2 + x ^ 2 < 1 by simpa only [add_comm] using hxy)
  have hfun : (fun u ↦ kernelPotential q a b μ f x u) =
      (fun u ↦ kernelPotential q b a μ f u x) :=
    funext fun u ↦ kernelPotential_swap q a b μ f x u
  simpa only [hfun] using h

end Integral

end BergmanWeakType.Weighted
