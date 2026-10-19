/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Kernel
public import BergmanWeakType.WeakType

/-! # Comparison of the actual Bergman weak type constants -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

/-- The complex disk projection has no larger weak constant than its positive majorant. -/
theorem projection_constant_le_positiveProjection_constant :
    weakTypeConstant diskArea (fun f z ↦ ‖projection f z‖ₑ) ≤
      weakTypeConstant diskArea positiveProjection := by
  exact weakTypeConstant_mono fun f _ z ↦ enorm_projection_le_positiveProjection f z

/-- Domination compares the complex and positive weighted weak constants. -/
theorem weightedProjection_constant_le_weightedPositiveProjection_constant (α : ℝ) :
    weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) ≤
      weakTypeConstant (weightedArea α) (weightedPositiveProjection α) := by
  exact weakTypeConstant_mono fun f _ z ↦
    enorm_weightedProjection_le_weightedPositiveProjection α f z

/-- The complex weighted weak constant specializes to the disk constant at parameter zero. -/
@[simp]
theorem weightedProjection_constant_zero :
    weakTypeConstant (weightedArea 0) (fun f z ↦ ‖weightedProjection 0 f z‖ₑ) =
      weakTypeConstant diskArea (fun f z ↦ ‖projection f z‖ₑ) := by
  simp

/-- The positive weighted weak constant specializes to the disk constant at parameter zero. -/
@[simp]
theorem weightedPositiveProjection_constant_zero :
    weakTypeConstant (weightedArea 0) (weightedPositiveProjection 0) =
      weakTypeConstant diskArea positiveProjection := by
  simp only [weightedArea_zero]
  congr 1
  funext f
  exact weightedPositiveProjection_zero f

end BergmanWeakType
