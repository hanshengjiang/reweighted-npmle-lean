import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Symmetric Dirichlet moment algebra

This file formalizes the deterministic algebra which turns the standard
symmetric Dirichlet coordinate covariances into the mean, variance, and total
variation formulas in Proposition 2.1 of the paper.
-/

open scoped BigOperators

namespace ReweightedNPMLE

/-- Ordinary empirical average of a finite vector. -/
noncomputable def empiricalMean {n : ℕ} (h : Fin n → ℝ) : ℝ :=
  (∑ i, h i) / n

/-- Ordinary empirical second moment. -/
noncomputable def empiricalSecondMoment {n : ℕ} (h : Fin n → ℝ) : ℝ :=
  (∑ i, (h i) ^ 2) / n

/-- Covariance matrix of a symmetric `Dirichlet(α,…,α)` vector. -/
noncomputable def symmetricDirichletCovariance (n : ℕ) (α : ℝ)
    (i j : Fin n) : ℝ :=
  ((if i = j then (n : ℝ) else 0) - 1) /
    ((n : ℝ) ^ 2 * ((n : ℝ) * α + 1))

/-- The common diagonal variance of a symmetric Dirichlet coordinate. -/
theorem symmetricDirichletCovariance_diag {n : ℕ} (α : ℝ) (i : Fin n) :
    symmetricDirichletCovariance n α i i =
      ((n : ℝ) - 1) / ((n : ℝ) ^ 2 * ((n : ℝ) * α + 1)) := by
  simp [symmetricDirichletCovariance]

/-- The common off-diagonal covariance of symmetric Dirichlet coordinates. -/
theorem symmetricDirichletCovariance_offdiag {n : ℕ} (α : ℝ) {i j : Fin n}
    (hij : i ≠ j) :
    symmetricDirichletCovariance n α i j =
      -1 / ((n : ℝ) ^ 2 * ((n : ℝ) * α + 1)) := by
  simp [symmetricDirichletCovariance, hij]

private theorem dirichlet_covariance_numerator {n : ℕ} (h : Fin n → ℝ) :
    ∑ i, ∑ j, h i * h j * ((if i = j then (n : ℝ) else 0) - 1) =
      (n : ℝ) * ∑ i, (h i) ^ 2 - (∑ i, h i) ^ 2 := by
  classical
  simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
  have hdiag : (∑ i, ∑ j, h i * h j * (if i = j then (n : ℝ) else 0)) =
      (n : ℝ) * ∑ i, (h i) ^ 2 := by
    simp only [mul_ite, mul_zero]
    simp [pow_two]
    rw [← Finset.sum_mul]
    ring
  have hall : (∑ i, ∑ j, h i * h j) = (∑ i, h i) ^ 2 := by
    rw [← Fintype.sum_mul_sum]
    ring
  rw [hdiag, hall]

/--
The variance of a Dirichlet-weighted empirical average is the empirical
variance divided by `nα+1`.
-/
theorem symmetricDirichlet_linear_variance {n : ℕ} (hn : 0 < n) (α : ℝ)
    (hα : 0 < α) (h : Fin n → ℝ) :
    ∑ i, ∑ j, h i * h j * symmetricDirichletCovariance n α i j =
      (empiricalSecondMoment h - (empiricalMean h) ^ 2) /
        ((n : ℝ) * α + 1) := by
  classical
  simp_rw [symmetricDirichletCovariance, ← mul_div_assoc]
  simp_rw [← Finset.sum_div]
  rw [dirichlet_covariance_numerator]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hden : (n : ℝ) * α + 1 ≠ 0 := by positivity
  simp only [empiricalSecondMoment, empiricalMean]
  field_simp

/-- The symmetric Dirichlet covariance annihilates the all-one direction. -/
theorem symmetricDirichlet_covariance_row_sum {n : ℕ} (hn : 0 < n) (α : ℝ)
    (hα : 0 < α) (i : Fin n) :
    ∑ j, symmetricDirichletCovariance n α i j = 0 := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hden : (n : ℝ) * α + 1 ≠ 0 := by positivity
  simp only [symmetricDirichletCovariance, ← Finset.sum_div]
  field_simp
  simp

/-- Finite `ℓ1–ℓ2` inequality used in the total-variation estimate. -/
theorem half_l1_le_half_sqrt_card_mul_l2sq {n : ℕ} (x : Fin n → ℝ) :
    (1 / 2 : ℝ) * ∑ i, |x i| ≤
      (1 / 2 : ℝ) * Real.sqrt ((n : ℝ) * ∑ i, (x i) ^ 2) := by
  have hsquares := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun i ↦ |x i|)
  simp only [Finset.card_univ, Fintype.card_fin, sq_abs] at hsquares
  have hsum : 0 ≤ ∑ i, |x i| := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hright : 0 ≤ (n : ℝ) * ∑ i, (x i) ^ 2 := by positivity
  have hsqrt : ∑ i, |x i| ≤ Real.sqrt ((n : ℝ) * ∑ i, (x i) ^ 2) := by
    exact (Real.le_sqrt hsum hright).2 hsquares
  nlinarith

end ReweightedNPMLE
