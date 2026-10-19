/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Rigidity.DomainGap
public import BergmanWeakType.Rigidity.Perturbation
public import BergmanWeakType.Rigidity.DiskSimilarity

@[expose] public section

noncomputable section

open Set MeasureTheory Metric

namespace BergmanWeakType

/-- Every bounded simply connected nondisk has positive Bergman weak constant strictly larger
than one. No boundary regularity or bounds on conformal derivatives are assumed. -/
theorem one_lt_domainPositiveProjection_constant_of_not_disk {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hbdd : Bornology.IsBounded Ω) (hconn : IsSimplyConnected Ω)
    {K : ℂ → ℂ → ℂ} (hK : IsBergmanKernel Ω K)
    (hnd : ¬∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ Ω = ball c R) :
    1 < weakTypeConstant (area.restrict Ω) (domainPositiveProjection Ω K) := by
  have : IsFiniteMeasure (area.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hbdd.measure_lt_top.ne
  obtain ⟨E, hE, hsub, hEpos, η, hη, hη1, hgap⟩ :=
    exists_domain_core_gap hΩ hbdd hconn hK hnd
  exact Rigidity.weakTypeConstant_gt_one_of_core_gap hΩ.measurableSet hK hE hsub hEpos
    hη hη1 hgap

/-- The value one forces a bounded simply connected planar domain to be a Euclidean disk. -/
theorem exists_disk_of_domainPositiveProjection_constant_eq_one {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hbdd : Bornology.IsBounded Ω) (hconn : IsSimplyConnected Ω)
    {K : ℂ → ℂ → ℂ} (hK : IsBergmanKernel Ω K)
    (hc : weakTypeConstant (area.restrict Ω) (domainPositiveProjection Ω K) = 1) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ Ω = ball c R := by
  by_contra hnd
  have hlt := one_lt_domainPositiveProjection_constant_of_not_disk hΩ hbdd hconn hK hnd
  rw [hc] at hlt
  exact (lt_irrefl 1) hlt

/-- Among bounded simply connected domains, positive weak constant one characterizes disks. -/
theorem positive_constant_eq_one_iff_disk (Ω : Set ℂ) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsSimplyConnected Ω)
    (K : ℂ → ℂ → ℂ) (hK : IsBergmanKernel Ω K) :
    weakTypeConstant (area.restrict Ω) (domainPositiveProjection Ω K) = 1 ↔
      ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ Ω = Metric.ball c R := by
  constructor
  · exact exists_disk_of_domainPositiveProjection_constant_eq_one hopen hbounded hconnected hK
  · rintro ⟨c, R, hR, rfl⟩
    exact weakTypeConstant_domainPositiveProjection_ball_eq_one c hR hK

end BergmanWeakType
