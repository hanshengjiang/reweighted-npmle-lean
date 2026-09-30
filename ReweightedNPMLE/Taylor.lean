import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Tactic

/-!
# Quantitative exponential approximation

Exact Taylor and factorial bounds used in Proposition 4.1 and Lemma 8.1 of the manuscript.
-/

namespace ReweightedNPMLE

open Finset Set

private lemma taylorWithinEval_exp_zero (m : ℕ) {t : ℝ} (ht : t ≠ 0) :
    taylorWithinEval Real.exp m (uIcc 0 t) 0 t =
      ∑ ell ∈ range (m + 1), t ^ ell / ell.factorial := by
  rw [taylor_within_apply]
  apply sum_congr rfl
  intro ell _
  have hu : UniqueDiffOn ℝ (uIcc 0 t) := uniqueDiffOn_Icc (by grind)
  rw [iteratedDerivWithin_eq_iteratedDeriv hu Real.contDiff_exp.contDiffAt left_mem_uIcc]
  have hderiv : iteratedDeriv ell Real.exp 0 = 1 := by
    have h := congrFun (iteratedDeriv_exp_const_mul ell 1) 0
    simpa using h
  rw [hderiv]
  simp only [sub_zero, smul_eq_mul, mul_one, div_eq_mul_inv]
  ring

/-- Uniform Lagrange remainder bound for the exponential series on `[-T,T]`. -/
theorem real_exp_taylor_remainder_bound (m : ℕ) {t T : ℝ}
    (hT : 0 ≤ T) (ht : |t| ≤ T) :
    |Real.exp t - ∑ ell ∈ range (m + 1), t ^ ell / ell.factorial| ≤
      Real.exp T * T ^ (m + 1) / (m + 1).factorial := by
  by_cases ht0 : t = 0
  · subst t
    simp [sum_range_succ']
    positivity
  obtain ⟨ξ, hξ, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (x := t) (x₀ := 0) (Ne.symm ht0)
      (Real.contDiff_exp.contDiffOn : ContDiffOn ℝ (m + 1) Real.exp (uIcc 0 t))
  rw [taylorWithinEval_exp_zero m ht0] at hrem
  have hderiv : iteratedDeriv (m + 1) Real.exp ξ = Real.exp ξ := by
    have h := congrFun (iteratedDeriv_exp_const_mul (m + 1) 1) ξ
    simpa using h
  rw [hrem, hderiv]
  have hξ_abs : |ξ| ≤ |t| := by
    simpa using abs_sub_left_of_mem_uIcc ⟨hξ.1.le, hξ.2.le⟩
  have hξT : ξ ≤ T := le_trans (le_abs_self ξ) (hξ_abs.trans ht)
  simp only [sub_zero, abs_div, abs_mul, abs_pow, Real.abs_exp, Nat.abs_cast]
  gcongr

/-- The elementary Stirling consequence `Tⁿ/n! ≤ (eT/n)ⁿ`, for `n=m+1`. -/
theorem pow_div_factorial_le_exp_mul_div_pow (m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    T ^ (m + 1) / (m + 1).factorial ≤
      (Real.exp 1 * T / (m + 1)) ^ (m + 1) := by
  let n : ℕ := m + 1
  have hn : 0 < n := by dsimp [n]; omega
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * n) := by
    rw [Real.one_le_sqrt]
    have hpi : 1 ≤ Real.pi := by nlinarith [Real.one_le_pi_div_two]
    have hn_one : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [mul_le_mul hpi hn_one zero_le_one (by positivity : 0 ≤ Real.pi)]
  have hfactorial : ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
    calc
      ((n : ℝ) / Real.exp 1) ^ n = 1 * ((n : ℝ) / Real.exp 1) ^ n := by rw [one_mul]
      _ ≤ Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n :=
        mul_le_mul_of_nonneg_right hsqrt (by positivity)
      _ ≤ (n.factorial : ℝ) := Stirling.le_factorial_stirling n
  have hcancel : (Real.exp 1 * T / (n : ℝ)) * ((n : ℝ) / Real.exp 1) = T := by
    field_simp
  have hmain : T ^ n / (n.factorial : ℝ) ≤
      (Real.exp 1 * T / (n : ℝ)) ^ n := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < n.factorial)]
    calc
      T ^ n = ((Real.exp 1 * T / (n : ℝ)) * ((n : ℝ) / Real.exp 1)) ^ n := by
        rw [hcancel]
      _ = (Real.exp 1 * T / (n : ℝ)) ^ n * ((n : ℝ) / Real.exp 1) ^ n := by
        rw [mul_pow]
      _ ≤ (Real.exp 1 * T / (n : ℝ)) ^ n * (n.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left hfactorial (by positivity)
  simpa [n, Nat.cast_add, Nat.cast_one] using hmain

end ReweightedNPMLE
