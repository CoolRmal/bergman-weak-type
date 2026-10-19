/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Boundary.Concentration

/-! # Weak bounds for the limiting boundary kernel column -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Topology

namespace BergmanWeakType

def boundaryCap (R : ℝ) : Set ℂ := disk ∩ Metric.ball 1 R

theorem measurableSet_boundaryCap (R : ℝ) : MeasurableSet (boundaryCap R) :=
  measurableSet_disk.inter Metric.isOpen_ball.measurableSet

theorem kernel_denominator_le_on_boundaryCap {R t : ℝ} (ht1 : t < 1)
    {z : ℂ} (hz : z ∈ boundaryCap R) : ‖1 - z * star (t : ℂ)‖ ≤ R + 1 - t := by
  have hz1 : ‖z‖ ≤ 1 := ((mem_disk_iff z).mp hz.1).le
  have hzR : ‖1 - z‖ < R := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz.2
  have heq : 1 - z * star (t : ℂ) = (1 - z) + (1 - (t : ℂ)) * z := by
    simp only [Complex.star_def, Complex.conj_ofReal]
    ring
  rw [heq]
  calc
    _ ≤ ‖1 - z‖ + ‖(1 - (t : ℂ)) * z‖ := norm_add_le _ _
    _ = ‖1 - z‖ + (1 - t) * ‖z‖ := by
      rw [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht1)]
    _ ≤ R + 1 - t := by nlinarith

theorem boundaryCap_interior_column_le_weakBound {α R t : ℝ} {C : ℝ≥0∞}
    (hα : -1 < α)
    (hC : IsWeakTypeBound (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) C)
    (hR : 0 < R) (ht : 0 ≤ t) (ht1 : t < 1) :
    ENNReal.ofReal ((R + 1 - t) ^ (-(α + 2))) * weightedArea α (boundaryCap R) ≤ C := by
  have ha : (t : ℂ) ∈ disk := by
    simp only [mem_disk_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
    exact ht1
  apply column_le_weakBound hα hC ha Set.inter_subset_left
  · intro z hz
    rw [norm_weightedKernel]
    apply Real.rpow_le_rpow_of_nonpos
      ((sub_pos.mpr ((mem_disk_iff z).mp hz.1)).trans_le
        (kernel_denominator_norm_lower z ha))
      (kernel_denominator_le_on_boundaryCap ht1 hz) (by linarith)
  · exact Real.rpow_pos_of_pos (by linarith) _

/-- Boundary point sources are used only as limits of interior, integrable inputs. -/
theorem boundaryCap_le_weakBound {α R : ℝ} {C : ℝ≥0∞} (hα : -1 < α)
    (hC : IsWeakTypeBound (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) C)
    (hR : 0 < R) :
    ENNReal.ofReal (R ^ (-(α + 2))) * weightedArea α (boundaryCap R) ≤ C := by
  let := weightedArea_isProbabilityMeasure α hα
  have hp : Filter.Tendsto (fun t : ℝ ↦ (R + 1 - t) ^ (-(α + 2)))
      (𝓝[<] 1) (𝓝 (R ^ (-(α + 2)))) := by
    have hc : ContinuousAt (fun t : ℝ ↦ (R + 1 - t) ^ (-(α + 2))) 1 :=
      (continuous_const.sub continuous_id).continuousAt.rpow_const
        (Or.inl (by change R + 1 - 1 ≠ 0; linarith))
    simpa only [add_sub_cancel_right] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := (ENNReal.continuous_mul_const (measure_ne_top (weightedArea α) (boundaryCap R)))
    |>.continuousAt.tendsto.comp (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hp)
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ht
  exact boundaryCap_interior_column_le_weakBound hα hC hR ht.1.le ht.2

theorem boundaryCap_le_weightedProjection_constant {α R : ℝ} (hα : -1 < α)
    (hR : 0 < R) :
    ENNReal.ofReal (R ^ (-(α + 2))) * weightedArea α (boundaryCap R) ≤
      weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) := by
  apply le_sInf
  exact fun C hC ↦ boundaryCap_le_weakBound hα hC hR

end BergmanWeakType
