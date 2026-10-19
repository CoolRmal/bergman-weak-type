/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # A uniform relative gap on a compact parameter set

This is the compactness ingredient for converting pointwise cancellation of an integral into
a uniform relative cancellation estimate. It does not establish that cancellation for a kernel.
-/

@[expose] public section

namespace BergmanWeakType

/-- A strict inequality between continuous nonnegative and positive functions on a nonempty
compact set has a uniform relative gap, with the gap lying in the interval `(0, 1]`. -/
theorem exists_uniform_relative_gap {X : Type*} [TopologicalSpace X] {s : Set X}
    {I J : X → ℝ} (hs : IsCompact s) (hne : s.Nonempty)
    (hI : ContinuousOn I s) (hJ : ContinuousOn J s)
    (hI_nonneg : ∀ x ∈ s, 0 ≤ I x) (hJ_pos : ∀ x ∈ s, 0 < J x)
    (hlt : ∀ x ∈ s, I x < J x) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ x ∈ s, I x ≤ (1 - η) * J x := by
  have hquot : ContinuousOn (fun x ↦ I x / J x) s :=
    hI.div hJ (fun x hx ↦ (hJ_pos x hx).ne')
  obtain ⟨a, ha, hmax⟩ := hs.exists_isMaxOn hne hquot
  refine ⟨1 - I a / J a, ?_, ?_, ?_⟩
  · exact sub_pos.mpr ((div_lt_one (hJ_pos a ha)).2 (hlt a ha))
  · have := div_nonneg (hI_nonneg a ha) (hJ_pos a ha).le
    linarith
  · intro x hx
    have hbound := (div_le_iff₀ (hJ_pos x hx)).mp (hmax hx)
    convert hbound using 1
    ring

end BergmanWeakType
