/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Boundary.CapMass

/-! # The explicit boundary lower bound for the complex weighted projection -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Topology

namespace BergmanWeakType

/-- The boundary concentration lower bound uses ordinary integrable complex inputs. -/
theorem boundaryConstant_le_weightedProjection_constant (α : ℝ) (hα : 0 ≤ α) :
    ENNReal.ofReal (boundaryConstant α) ≤
      weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) := by
  have hα' : -1 < α := by linarith
  let := weightedArea_isProbabilityMeasure α hα'
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_rescaled_boundaryCap_real hα)
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with R hR
  have hR' : 0 < R := hR
  dsimp only [Function.comp_def]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hR'.le _)]
  have hm : ENNReal.ofReal ((weightedArea α).real (boundaryCap R)) =
      weightedArea α (boundaryCap R) := ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [hm]
  exact boundaryCap_le_weightedProjection_constant hα' hR'

end BergmanWeakType
