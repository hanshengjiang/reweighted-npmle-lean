import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Radial localization inequalities

Scalar and coordinatewise estimates used by the radial-localization part of the
effective-dimension theorem.
-/

open scoped BigOperators
open Set

namespace ReweightedNPMLE

/-- The quadratic completion at the heart of Lemma 7.4. -/
theorem radial_quadratic_bound {x A E τ : ℝ}
    (h : x ^ 2 ≤ 6 * (A * x + E + τ)) :
    x ^ 2 ≤ 36 * A ^ 2 + 12 * E + 12 * τ := by
  nlinarith [sq_nonneg (x - 6 * A)]

/-- A direct logarithm bound from the convergent Taylor series. -/
theorem abs_log_one_add_le {u : ℝ} (hu : |u| < 1) :
    |Real.log (1 + u)| ≤ |u| / (1 - |u|) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -u) (by simpa) 0
  simpa using h

/-- On the localization ball, the squared log displacement is at most twice the squared one. -/
theorem log_one_add_sq_le_two_sq {u : ℝ} (hu : |u| ≤ 1 / 16) :
    Real.log (1 + u) ^ 2 ≤ 2 * u ^ 2 := by
  have hu1 : |u| < 1 := lt_of_le_of_lt hu (by norm_num)
  have hden : 0 < 1 - |u| := sub_pos.mpr hu1
  have hlog := abs_log_one_add_le hu1
  have hratio : |u| / (1 - |u|) ≤ (16 / 15 : ℝ) * |u| := by
    rw [div_le_iff₀ hden]
    nlinarith [abs_nonneg u]
  have habs : |Real.log (1 + u)| ≤ (16 / 15 : ℝ) * |u| := hlog.trans hratio
  calc
    Real.log (1 + u) ^ 2 = |Real.log (1 + u)| ^ 2 := (sq_abs _).symm
    _ ≤ ((16 / 15 : ℝ) * |u|) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 habs
    _ ≤ 2 * u ^ 2 := by
      rw [mul_pow, sq_abs]
      nlinarith [sq_nonneg u]

theorem sum_log_one_add_sq_le_two_sum_sq {n : ℕ} (u : Fin n → ℝ)
    (hu : ∀ i, |u i| ≤ 1 / 16) :
    ∑ i, Real.log (1 + u i) ^ 2 ≤ 2 * ∑ i, u i ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦ log_one_add_sq_le_two_sq (hu i)

/-- The upper Taylor bound used to force a near-optimal point into the localization ball. -/
theorem log_one_add_le_sub_sq_third {u : ℝ} (hu : |u| ≤ 1 / 4) :
    Real.log (1 + u) ≤ u - u ^ 2 / 3 := by
  have hu1 : |u| < 1 := lt_of_le_of_lt hu (by norm_num)
  have hden : 0 < 1 - |u| := sub_pos.mpr hu1
  have hseries := Real.abs_log_sub_add_sum_range_le (x := -u) (by simpa) 3
  have hupper := (le_abs_self
    ((∑ i ∈ Finset.range 3, (-u) ^ (i + 1) / (i + 1)) + Real.log (1 - (-u)))).trans
      hseries
  norm_num [Finset.sum_range_succ] at hupper
  have hu_sq : |u| ^ 2 ≤ (1 / 4 : ℝ) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg u) (by norm_num)).2 hu
  have hrem : |u| ^ 4 / (1 - |u|) ≤ u ^ 2 / 12 := by
    rw [div_le_iff₀ hden]
    rw [show |u| ^ 4 = u ^ 2 * |u| ^ 2 by
      calc
        |u| ^ 4 = |u| ^ 2 * |u| ^ 2 := by ring
        _ = u ^ 2 * |u| ^ 2 := by rw [sq_abs]]
    nlinarith [sq_nonneg u, abs_nonneg u]
  have hcubic : u ^ 3 / 3 ≤ u ^ 2 / 12 := by
    have hu_upper : u ≤ 1 / 4 := (le_abs_self u).trans hu
    nlinarith [sq_nonneg u]
  rw [show (-u) ^ 3 = -(u ^ 3) by ring] at hupper
  linarith

/-- The lower logarithm bound used in the Gamma change-of-variables
argument.  The paper only needs the smaller radius `1/8`. -/
theorem log_one_add_ge_sub_sq {u : ℝ} (hu : |u| ≤ 1 / 8) :
    u - u ^ 2 ≤ Real.log (1 + u) := by
  let f : ℝ → ℝ := fun x ↦ Real.log (1 + x) - x + x ^ 2
  have hfderiv : ∀ x : ℝ, -1 < x →
      HasDerivAt f (x * (1 + 2 * x) / (1 + x)) x := by
    intro x hx
    have hne : 1 + x ≠ 0 := by linarith
    have hlog := ((hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)).log hne
    convert (hlog.sub (hasDerivAt_id x)).add ((hasDerivAt_id x).pow 2) using 1 <;>
      simp only [Pi.add_apply, Pi.one_apply, id_eq] <;> field_simp <;> ring
  by_cases hu0 : 0 ≤ u
  · have hmono : MonotoneOn f (Set.Icc 0 u) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
      · intro x hx
        exact (hfderiv x (by linarith [hx.1])).continuousAt.continuousWithinAt
      · intro x hx
        exact (hfderiv x (by rw [interior_Icc] at hx; linarith [hx.1]))
          |>.differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hfderiv x (by rw [interior_Icc] at hx; linarith [hx.1])).deriv]
        rw [interior_Icc] at hx
        have hxupper : x ≤ 1 / 8 := hx.2.le.trans ((le_abs_self u).trans hu)
        exact div_nonneg (mul_nonneg hx.1.le (by linarith [hx.1])) (by linarith [hx.1])
    have h := hmono (left_mem_Icc.mpr hu0) (right_mem_Icc.mpr hu0) hu0
    dsimp [f] at h
    norm_num at h
    linarith
  · have hule : u ≤ 0 := le_of_not_ge hu0
    have hanti : AntitoneOn f (Set.Icc u 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc u 0)
      · intro x hx
        have hulower : -(1 / 8 : ℝ) ≤ u := by
          have := neg_le_of_abs_le hu
          norm_num at this ⊢
          exact this
        exact (hfderiv x (by linarith [hx.1])).continuousAt.continuousWithinAt
      · intro x hx
        have hulower : -(1 / 8 : ℝ) ≤ u := by
          have := neg_le_of_abs_le hu
          norm_num at this ⊢
          exact this
        exact (hfderiv x (by rw [interior_Icc] at hx; linarith [hx.1]))
          |>.differentiableAt.differentiableWithinAt
      · intro x hx
        rw [(hfderiv x (by
          have hulower : -(1 / 8 : ℝ) ≤ u := by
            have := neg_le_of_abs_le hu
            norm_num at this ⊢
            exact this
          rw [interior_Icc] at hx
          linarith [hx.1])).deriv]
        rw [interior_Icc] at hx
        have hulower : -(1 / 8 : ℝ) ≤ u := by
          have := neg_le_of_abs_le hu
          norm_num at this ⊢
          exact this
        have hxden : 0 < 1 + x := by linarith [hx.1]
        have hlin : 0 ≤ 1 + 2 * x := by linarith [hx.1]
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hx.2.le hlin) hxden.le
    have h := hanti (left_mem_Icc.mpr hule) (right_mem_Icc.mpr hule) hule
    dsimp [f] at h
    norm_num at h
    linarith

end ReweightedNPMLE
