/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Integrating the derivative estimate for a moving truncation

These lemmas pass from compact interior intervals to the full unit interval. They do not assume
boundary values for the auxiliary truncation function.
-/

@[expose] public section

open MeasureTheory Set

namespace BergmanWeakType

/-- A uniform bound on all interior interval integrals extends to the full unit interval. -/
theorem integral_le_of_inner_integral_le {A : ℝ → ℝ} {M : ℝ}
    (hA : IntegrableOn A (Icc 0 1))
    (hinner : ∀ a b : ℝ, 0 < a → a < b → b < 1 → (∫ y in a..b, A y) ≤ M) :
    (∫ y in (0 : ℝ)..1, A y) ≤ M := by
  have hbnd : ∀ b ∈ Ioo (0 : ℝ) 1, (∫ y in (0 : ℝ)..b, A y) ≤ M := by
    intro b hb
    have hAb : IntegrableOn A (uIcc 0 b) := by
      rw [uIcc_of_le hb.1.le]
      exact hA.mono_set (Icc_subset_Icc le_rfl hb.2.le)
    apply le_on_closure (s := Ioo (0 : ℝ) b)
      (f := fun a ↦ ∫ y in a..b, A y) (g := fun _ ↦ M)
      (fun a ha ↦ hinner a b ha.1 ha.2 hb.2)
    · simpa only [closure_Ioo hb.1.ne, uIcc_of_le hb.1.le] using
        intervalIntegral.continuousOn_primitive_interval_left hAb
    · exact continuousOn_const
    · simp [closure_Ioo hb.1.ne, hb.1.le]
  apply le_on_closure (f := fun b ↦ ∫ y in (0 : ℝ)..b, A y) (g := fun _ ↦ M) hbnd
  · have hAu : IntegrableOn A (uIcc 0 1) := by simpa using hA
    simpa using intervalIntegral.continuousOn_primitive_interval hAu
  · exact continuousOn_const
  · simp

/-- An interior derivative domination gives the moving-truncation integral bound. -/
theorem integral_le_of_interior_deriv_domination {A G G' : ℝ → ℝ} {M : ℝ}
    (hA : IntegrableOn A (Icc 0 1))
    (hderiv : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt G (G' y) y)
    (hdom : ∀ y ∈ Ioo (0 : ℝ) 1, A y ≤ G' y)
    (hzero : ∀ y ∈ Ioo (0 : ℝ) 1, 0 ≤ G y)
    (hbound : ∀ y ∈ Ioo (0 : ℝ) 1, G y ≤ M) :
    (∫ y in (0 : ℝ)..1, A y) ≤ M := by
  apply integral_le_of_inner_integral_le hA
  intro a b ha hab hb
  have hsubset : Icc a b ⊆ Ioo (0 : ℝ) 1 := fun y hy ↦
    ⟨ha.trans_le hy.1, hy.2.trans_lt hb⟩
  have hcont : ContinuousOn G (Icc a b) := fun y hy ↦
    (hderiv y (hsubset hy)).continuousAt.continuousWithinAt
  have hi := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab.le hcont
    (fun y hy ↦ (hderiv y (hsubset (Ioo_subset_Icc_self hy))).hasDerivWithinAt)
    (hA.mono_set (Icc_subset_Icc ha.le hb.le))
    (fun y hy ↦ hdom y (hsubset (Ioo_subset_Icc_self hy)))
  have hGa := hzero a ⟨ha, hab.trans hb⟩
  have hGb := hbound b ⟨ha.trans hab, hb⟩
  linarith

/-- Integrating a positive finite difference leaves only its two endpoint strips. -/
theorem integral_le_of_shift_domination {A G : ℝ → ℝ} {M a b h : ℝ}
    (ha : 0 < a) (hab : a < b) (hh : 0 < h) (hbh : b + h < 1)
    (hA : IntegrableOn A (Icc 0 1)) (hG : IntegrableOn G (Icc 0 1))
    (hzero : ∀ y ∈ Ioo (0 : ℝ) 1, 0 ≤ G y)
    (hbound : ∀ y ∈ Ioo (0 : ℝ) 1, G y ≤ M)
    (hshift : ∀ y ∈ Icc a b, h * A (y + h) ≤ G (y + h) - G y) :
    (∫ y in a + h..b + h, A y) ≤ M := by
  have hI {F : ℝ → ℝ} (hF : IntegrableOn F (Icc 0 1)) {u v : ℝ}
      (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) : IntervalIntegrable F volume u v :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le huv).mpr
      (hF.mono_set (Icc_subset_Icc hu hv))
  have habG := hI hG ha.le hab.le (by linarith)
  have hahG := hI hG ha.le (by linarith : a ≤ a + h) (by linarith)
  have hshG := hI hG (by linarith : 0 ≤ a + h) (by linarith : a + h ≤ b + h) hbh.le
  have hbhG := hI hG (by linarith : 0 ≤ b) (by linarith : b ≤ b + h) hbh.le
  have hshA := hI hA (by linarith : 0 ≤ a + h) (by linarith : a + h ≤ b + h) hbh.le
  have hAc : IntervalIntegrable (fun y ↦ A (y + h)) volume a b :=
    (IntervalIntegrable.comp_add_right_iff).mpr hshA
  have hGc : IntervalIntegrable (fun y ↦ G (y + h)) volume a b :=
    (IntervalIntegrable.comp_add_right_iff).mpr hshG
  have hi := intervalIntegral.integral_mono_on hab.le (hAc.const_mul h)
    (hGc.sub habG) hshift
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hGc habG,
    intervalIntegral.integral_comp_add_right, intervalIntegral.integral_comp_add_right,
    intervalIntegral.integral_interval_sub_interval_comm' hshG habG hahG.symm] at hi
  have hlo : 0 ≤ ∫ y in a..a + h, G y :=
    intervalIntegral.integral_nonneg (by linarith) fun y hy ↦
      hzero y ⟨ha.trans_le hy.1, by linarith [hy.2]⟩
  have hhi : (∫ y in b..b + h, G y) ≤ h * M := by
    calc
      _ ≤ ∫ _y in b..b + h, M :=
        intervalIntegral.integral_mono_on (by linarith) hbhG intervalIntegrable_const
          fun y hy ↦ hbound y ⟨by linarith [hy.1], hy.2.trans_lt hbh⟩
      _ = h * M := by simp
  exact (mul_le_mul_iff_of_pos_left hh).mp (by linarith)

/-- A bounded nonnegative function whose finite differences dominate `A` controls its integral.
No differentiability of the bounding function is needed. -/
theorem integral_le_of_finite_difference_domination {A G : ℝ → ℝ} {M : ℝ}
    (hA : IntegrableOn A (Icc 0 1)) (hG : IntegrableOn G (Icc 0 1))
    (hzero : ∀ y ∈ Ioo (0 : ℝ) 1, 0 ≤ G y)
    (hbound : ∀ y ∈ Ioo (0 : ℝ) 1, G y ≤ M)
    (hshift : ∀ y h : ℝ, 0 < y → 0 < h → y + h < 1 →
      h * A (y + h) ≤ G (y + h) - G y) :
    (∫ y in (0 : ℝ)..1, A y) ≤ M := by
  apply integral_le_of_inner_integral_le hA
  intro a b ha hab hb
  have hprim : ContinuousOn (fun y ↦ ∫ t in (0 : ℝ)..y, A t) (Icc 0 1) := by
    have hAu : IntegrableOn A (uIcc 0 1) := by simpa using hA
    simpa using intervalIntegral.continuousOn_primitive_interval hAu
  have hcont : ContinuousOn (fun h ↦ ∫ y in a + h..b + h, A y) (Icc 0 (1 - b)) := by
    have hleft := hprim.comp (continuous_const.add continuous_id).continuousOn
      (show MapsTo (fun h ↦ a + h) (Icc 0 (1 - b)) (Icc 0 1) by
        intro h hh; constructor <;> linarith [hh.1, hh.2])
    have hright := hprim.comp (continuous_const.add continuous_id).continuousOn
      (show MapsTo (fun h ↦ b + h) (Icc 0 (1 - b)) (Icc 0 1) by
        intro h hh; constructor <;> linarith [hh.1, hh.2])
    apply (hright.sub hleft).congr
    intro h hh
    have hi {u : ℝ} (hu : u ∈ Icc 0 1) : IntervalIntegrable A volume 0 u :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hu.1).mpr
        (hA.mono_set (Icc_subset_Icc le_rfl hu.2))
    exact (intervalIntegral.integral_interval_sub_left
      (hi ⟨by linarith [hh.1], by linarith [hh.2]⟩)
      (hi ⟨by linarith [hh.1], by linarith [hh.2]⟩)).symm
  have hi : ∀ h ∈ Ioo (0 : ℝ) (1 - b), (∫ y in a + h..b + h, A y) ≤ M := by
    intro h hh
    apply integral_le_of_shift_domination ha hab hh.1 (by linarith [hh.2])
      hA hG hzero hbound
    intro y hy
    exact hshift y h (ha.trans_le hy.1) hh.1 (by linarith [hy.2, hh.2])
  have hz := le_on_closure hi
    (by simpa only [closure_Ioo (by linarith : (0 : ℝ) ≠ 1 - b)] using hcont)
    continuousOn_const
    (show (0 : ℝ) ∈ closure (Ioo (0 : ℝ) (1 - b)) by
      rw [closure_Ioo (by linarith : (0 : ℝ) ≠ 1 - b)]
      exact ⟨le_rfl, by linarith⟩)
  simpa using hz

end BergmanWeakType
