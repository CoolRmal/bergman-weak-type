/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.RiemannMapping
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.MeanValue

public section

open Set Filter Metric Function
open scoped Topology

namespace BergmanWeakType

/-- An injective function on an open complex neighborhood cannot be locally constant. -/
theorem not_eventually_constant_of_injOn {U : Set ℂ} {f : ℂ → ℂ} {x : ℂ}
    (hU : IsOpen U) (hf : InjOn f U) (hx : x ∈ U) :
    ¬ ∀ᶠ z in 𝓝 x, f z = f x := by
  intro h
  have hsingle : ({x} : Set ℂ) ∈ 𝓝 x := by
    filter_upwards [h, hU.eventually_mem hx] with z hz hzU
    exact hf hzU hx hz
  exact not_isOpen_singleton x <|
    isOpen_singleton_of_finite_mem_nhds x hsingle (finite_singleton x)

/-- The inverse of a holomorphic injection is continuous on its image. -/
theorem continuousAt_inverse_of_differentiableOn {U : Set ℂ} {f g : ℂ → ℂ} {x : ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hg : LeftInvOn g f U)
    (hx : x ∈ U) : ContinuousAt g (f x) := by
  have hopen : 𝓝 (f x) ≤ Filter.map f (𝓝 x) :=
    (hf.analyticAt (hU.mem_nhds hx)).eventually_constant_or_nhds_le_map_nhds.resolve_left
      (not_eventually_constant_of_injOn hU hg.injOn hx)
  change Filter.map g (𝓝 (f x)) ≤ 𝓝 (g (f x))
  rw [hg hx]
  calc
    Filter.map g (𝓝 (f x)) ≤ Filter.map g (Filter.map f (𝓝 x)) := Filter.map_mono hopen
    _ = Filter.map (g ∘ f) (𝓝 x) := Filter.map_map
    _ ≤ 𝓝 x := tendsto_id.congr' <| (hU.eventually_mem hx).mono fun z hz ↦ (hg hz).symm

/-- Critical points of an injective holomorphic function are isolated. -/
theorem eventually_deriv_ne_zero_of_injOn {U : Set ℂ} {f : ℂ → ℂ} {x : ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hx : x ∈ U) :
    ∀ᶠ z in 𝓝[≠] x, deriv f z ≠ 0 := by
  rcases (hf.analyticOnNhd hU).deriv x hx |>.eventually_eq_zero_or_eventually_ne_zero
    with hzero | hne
  · obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_ball.mem_iff.mp <|
      (hzero.and (hU.eventually_mem hx))
    have hsub : ball x r ⊆ U := fun z hz ↦ (hrU hz).2
    have hconst : ∀ᶠ z in 𝓝 x, f z = f x := by
      filter_upwards [ball_mem_nhds x hr] with z hz
      exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball x r).isPreconnected
        (hf.mono hsub) (fun z hz ↦ (hrU hz).1) hz (mem_ball_self hr)
    exact (not_eventually_constant_of_injOn hU hinj hx hconst).elim
  · exact hne

/-- A set-theoretic inverse of a holomorphic bijection between open complex sets is holomorphic.
Continuity follows from the open mapping theorem; isolated possible critical points are removable
singularities of the inverse. -/
theorem differentiableOn_inverse {U V : Set ℂ} {f g : ℂ → ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hf : DifferentiableOn ℂ f U)
    (hinv : InvOn g f U V) (hgmap : MapsTo g V U) : DifferentiableOn ℂ g V := by
  have hcont : ∀ y ∈ V, ContinuousAt g y := by
    intro y hy
    simpa only [hinv.2 hy] using
      continuousAt_inverse_of_differentiableOn hU hf hinv.1 (hgmap hy)
  intro y hy
  apply DifferentiableAt.differentiableWithinAt
  apply AnalyticAt.differentiableAt
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ (hcont y hy)
  have hcrit := eventually_deriv_ne_zero_of_injOn hU hf hinv.1.injOn (hgmap hy)
  rw [eventually_nhdsWithin_iff] at hcrit
  filter_upwards [((hcont y hy).tendsto.eventually hcrit).filter_mono nhdsWithin_le_nhds,
    (hV.eventually_mem hy).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzV hzneq
  have hneq : g z ≠ g y := by
    intro heq
    apply hzneq
    calc z = f (g z) := (hinv.2 hzV).symm
         _ = f (g y) := congrArg f heq
         _ = y := hinv.2 hy
  exact ((hf.differentiableAt (hU.mem_nhds (hgmap hzV))).hasDerivAt.of_local_left_inverse
    (hcont z hzV) (hz hneq) ((hV.eventually_mem hzV).mono fun w hw ↦ hinv.2 hw)).differentiableAt

/-- A holomorphic bijection between open complex sets has no critical points. -/
theorem deriv_ne_zero_of_bijOn {U V : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hf : DifferentiableOn ℂ f U)
    (hbij : BijOn f U V) {x : ℂ} (hx : x ∈ U) : deriv f x ≠ 0 := by
  let g := invFunOn f U
  have hinv : InvOn g f U V := hbij.invOn_invFunOn
  have hgmap : MapsTo g V U := hinv.1.mapsTo hbij.surjOn
  have hg := differentiableOn_inverse hU hV hf hinv hgmap
  have hcomp := (hg.differentiableAt (hV.mem_nhds (hbij.mapsTo hx))).hasDerivAt.comp x
    (hf.differentiableAt (hU.mem_nhds hx)).hasDerivAt
  have hid : HasDerivAt (fun z : ℂ ↦ z) (deriv g (f x) * deriv f x) x :=
    hcomp.congr_of_eventuallyEq ((hU.eventually_mem hx).mono fun z hz ↦ (hinv.1 hz).symm)
  have heq : deriv g (f x) * deriv f x = 1 := hid.unique (hasDerivAt_id x)
  intro hzero
  simp [hzero] at heq

/-- Every proper simply connected open complex domain admits mutually inverse holomorphic maps
to and from the unit disk, with nowhere-vanishing derivatives. -/
theorem exists_biholomorphic_unitBall {U : Set ℂ} (hU : IsOpen U)
    (hconn : IsSimplyConnected U) (hproper : U ≠ univ) :
    ∃ φ ψ : ℂ → ℂ,
      DifferentiableOn ℂ φ (ball 0 1) ∧ DifferentiableOn ℂ ψ U ∧
      BijOn φ (ball 0 1) U ∧ InvOn ψ φ (ball 0 1) U ∧
      (∀ z ∈ ball 0 1, deriv φ z ≠ 0) ∧ (∀ z ∈ U, deriv ψ z ≠ 0) := by
  obtain ⟨x, hx⟩ := hconn.nonempty
  obtain ⟨ψ, hψ, hbij, _⟩ := Complex.exists_bijOn_unitBall_map_eq_zero hU hconn hproper hx
  let φ := invFunOn ψ U
  have hinv : InvOn φ ψ U (ball 0 1) := hbij.invOn_invFunOn
  have hφ := differentiableOn_inverse hU isOpen_ball hψ hinv
    (hinv.1.mapsTo hbij.surjOn)
  have hφbij : BijOn φ (ball 0 1) U := hbij.symm hinv.symm
  exact ⟨φ, ψ, hφ, hψ, hφbij, hinv.symm,
    fun z hz ↦ deriv_ne_zero_of_bijOn isOpen_ball hU hφ hφbij hz,
    fun z hz ↦ deriv_ne_zero_of_bijOn hU isOpen_ball hψ hbij hz⟩

end BergmanWeakType
