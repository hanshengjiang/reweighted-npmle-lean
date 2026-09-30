import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Scalar inequalities for Gamma concentration

These are the two elementary logarithmic estimates used in Lemma 9.1 of the manuscript.
-/

open Set

namespace ReweightedNPMLE

theorem sub_log_one_add_ge_sq_div_four {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    t - Real.log (1 + t) ≥ t ^ 2 / 4 := by
  let f : ℝ → ℝ := fun x ↦ x - Real.log (1 + x) - x ^ 2 / 4
  have hfderiv : ∀ x : ℝ, -1 < x →
      HasDerivAt f (x * (1 - x) / (2 * (1 + x))) x := by
    intro x hx
    have hne : 1 + x ≠ 0 := by linarith
    have hlog := ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).log hne
    convert (hasDerivAt_id x).sub hlog |>.sub
      (((hasDerivAt_id x).pow 2).div_const 4) using 1 <;>
      simp only [Pi.add_apply, Pi.one_apply, id_eq] <;>
      field_simp <;> ring
  have hmono : MonotoneOn f (Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
    · intro x hx
      exact (hfderiv x (by linarith [hx.1])).continuousAt.continuousWithinAt
    · intro x hx
      exact (hfderiv x (by
        rw [interior_Icc] at hx
        linarith [hx.1])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hfderiv x (by
        rw [interior_Icc] at hx
        linarith [hx.1])).deriv]
      rw [interior_Icc] at hx
      have hx₀ : 0 ≤ x := hx.1.le
      have hx₁ : x ≤ 1 := hx.2.le.trans ht₁
      positivity
  have h := hmono (left_mem_Icc.mpr ht₀) (right_mem_Icc.mpr ht₀) ht₀
  dsimp [f] at h
  norm_num at h
  linarith

theorem neg_sub_log_one_sub_ge_sq_div_two {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    -t - Real.log (1 - t) ≥ t ^ 2 / 2 := by
  let f : ℝ → ℝ := fun x ↦ -x - Real.log (1 - x) - x ^ 2 / 2
  have hfderiv : ∀ x : ℝ, x < 1 → HasDerivAt f (x ^ 2 / (1 - x)) x := by
    intro x hx
    have hne : 1 - x ≠ 0 := by linarith
    have hinner := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    have hlog := hinner.log hne
    convert (hasDerivAt_id x).neg.sub hlog |>.sub
      (((hasDerivAt_id x).pow 2).div_const 2) using 1 <;>
      simp only [Pi.sub_apply, Pi.one_apply, id_eq] <;>
      field_simp <;> ring
  have hmono : MonotoneOn f (Icc 0 t) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
    · intro x hx
      exact (hfderiv x (hx.2.trans_lt ht₁)).continuousAt.continuousWithinAt
    · intro x hx
      exact (hfderiv x (by
        rw [interior_Icc] at hx
        exact hx.2.trans ht₁)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hfderiv x (by
        rw [interior_Icc] at hx
        exact hx.2.trans ht₁)).deriv]
      rw [interior_Icc] at hx
      exact div_nonneg (sq_nonneg x) (by linarith [hx.2, ht₁])
  have h := hmono (left_mem_Icc.mpr ht₀) (right_mem_Icc.mpr ht₀) ht₀
  dsimp [f] at h
  norm_num at h
  linarith

end ReweightedNPMLE
