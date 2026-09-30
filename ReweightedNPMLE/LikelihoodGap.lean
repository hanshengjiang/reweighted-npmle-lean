import ReweightedNPMLE.Weights
import ReweightedNPMLE.Localization
import Mathlib.Tactic

/-!
# Deterministic likelihood-gap identities

These lemmas isolate the exact algebra behind the paper's statements that a weighted optimum
is an ordinary near-optimum when the weights are close to one.
-/

open scoped BigOperators

namespace ReweightedNPMLE

/-- The all-one weight vector. -/
def oneWeights (n : ℕ) : Fin n → ℝ := fun _ ↦ 1

@[simp] theorem weightedLogLikelihood_oneWeights {n : ℕ} (v : Fin n → ℝ) :
    weightedLogLikelihood (oneWeights n) v = ∑ i, Real.log (v i) := by
  simp [weightedLogLikelihood, oneWeights]

/-- Exact decomposition of weighted and ordinary likelihood differences. -/
theorem weighted_difference_decomposition {n : ℕ} (w v₀ v : Fin n → ℝ) :
    weightedLogLikelihood w v₀ - weightedLogLikelihood w v =
      (weightedLogLikelihood (oneWeights n) v₀ -
        weightedLogLikelihood (oneWeights n) v) +
      ∑ i, (w i - 1) * (Real.log (v₀ i) - Real.log (v i)) := by
  classical
  calc
    weightedLogLikelihood w v₀ - weightedLogLikelihood w v =
        ∑ i, (w i * Real.log (v₀ i) - w i * Real.log (v i)) := by
          simp [weightedLogLikelihood, Finset.sum_sub_distrib]
    _ = ∑ i, ((Real.log (v₀ i) - Real.log (v i)) +
        (w i - 1) * (Real.log (v₀ i) - Real.log (v i))) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (∑ i, (Real.log (v₀ i) - Real.log (v i))) +
        ∑ i, (w i - 1) * (Real.log (v₀ i) - Real.log (v i)) := by
          rw [Finset.sum_add_distrib]
    _ = (weightedLogLikelihood (oneWeights n) v₀ -
        weightedLogLikelihood (oneWeights n) v) +
        ∑ i, (w i - 1) * (Real.log (v₀ i) - Real.log (v i)) := by
          simp [weightedLogLikelihood, oneWeights, Finset.sum_sub_distrib]

/-- Ordinary optimality makes the ordinary likelihood loss nonnegative. -/
theorem ordinary_likelihood_gap_nonneg {n : ℕ} {C : Set (Fin n → ℝ)}
    {v₀ v : Fin n → ℝ}
    (hv₀ : IsMaxOn C (weightedLogLikelihood (oneWeights n)) v₀) (hv : v ∈ C) :
    0 ≤ weightedLogLikelihood (oneWeights n) v₀ -
      weightedLogLikelihood (oneWeights n) v := by
  exact sub_nonneg.mpr (hv₀.2 v hv)

/--
If `v` is within `τ` of maximizing the weighted criterion relative to `v₀`, its ordinary
likelihood loss is bounded by the perturbation pairing plus `τ`.
-/
theorem ordinary_gap_le_perturbation_pairing {n : ℕ}
    (w v₀ v : Fin n → ℝ) {τ : ℝ}
    (hweighted : weightedLogLikelihood w v₀ ≤ weightedLogLikelihood w v + τ) :
    weightedLogLikelihood (oneWeights n) v₀ -
        weightedLogLikelihood (oneWeights n) v ≤
      ∑ i, (w i - 1) * (Real.log (v i) - Real.log (v₀ i)) + τ := by
  have hdecomp := weighted_difference_decomposition w v₀ v
  have hdiff : weightedLogLikelihood w v₀ - weightedLogLikelihood w v ≤ τ := by
    linarith
  rw [hdecomp] at hdiff
  have hpair :
      -∑ i, (w i - 1) * (Real.log (v₀ i) - Real.log (v i)) =
        ∑ i, (w i - 1) * (Real.log (v i) - Real.log (v₀ i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← hpair]
  linarith

/-- The exact-optimizer specialization of `ordinary_gap_le_perturbation_pairing`. -/
theorem ordinary_gap_le_perturbation_pairing_exact {n : ℕ}
    (w v₀ v : Fin n → ℝ)
    (hweighted : weightedLogLikelihood w v₀ ≤ weightedLogLikelihood w v) :
    weightedLogLikelihood (oneWeights n) v₀ -
        weightedLogLikelihood (oneWeights n) v ≤
      ∑ i, (w i - 1) * (Real.log (v i) - Real.log (v₀ i)) := by
  simpa using ordinary_gap_le_perturbation_pairing w v₀ v (τ := (0 : ℝ))
    (by simpa using hweighted)

/-- An `ℓ∞–ℓ¹` upper bound for the perturbation pairing. -/
theorem abs_perturbation_pairing_le {n : ℕ} (w v₀ v : Fin n → ℝ) (M : ℝ)
    (hw : ∀ i, |w i - 1| ≤ M) :
    |∑ i, (w i - 1) * (Real.log (v i) - Real.log (v₀ i))| ≤
      M * ∑ i, |Real.log (v i) - Real.log (v₀ i)| := by
  calc
    |∑ i, (w i - 1) * (Real.log (v i) - Real.log (v₀ i))| ≤
        ∑ i, |(w i - 1) * (Real.log (v i) - Real.log (v₀ i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |w i - 1| * |Real.log (v i) - Real.log (v₀ i)| := by
      simp only [abs_mul]
    _ ≤ ∑ i, M * |Real.log (v i) - Real.log (v₀ i)| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hw i) (abs_nonneg _)
    _ = M * ∑ i, |Real.log (v i) - Real.log (v₀ i)| := by
      rw [Finset.mul_sum]

/-- Euclidean Cauchy--Schwarz bound for the perturbation pairing. -/
theorem perturbation_pairing_sq_le {n : ℕ} (w v₀ v : Fin n → ℝ) :
    (∑ i, (w i - 1) * (Real.log (v i) - Real.log (v₀ i))) ^ 2 ≤
      (∑ i, (w i - 1) ^ 2) *
        ∑ i, (Real.log (v i) - Real.log (v₀ i)) ^ 2 := by
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i ↦ w i - 1) (fun i ↦ Real.log (v i) - Real.log (v₀ i))

/-- An ordinary optimum and a weighted optimum satisfy the exact squared
gap-versus-log-displacement estimate obtained from Cauchy--Schwarz. -/
theorem ordinary_gap_sq_le_weight_deviation_sq_mul_logratio_sq
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (w v₀ v : Fin n → ℝ)
    (hv₀ : IsMaxOn C (weightedLogLikelihood (oneWeights n)) v₀)
    (hv : v ∈ C)
    (hweighted : weightedLogLikelihood w v₀ ≤ weightedLogLikelihood w v) :
    (weightedLogLikelihood (oneWeights n) v₀ -
        weightedLogLikelihood (oneWeights n) v) ^ 2 ≤
      (∑ i, (w i - 1) ^ 2) *
        ∑ i, (Real.log (v i) - Real.log (v₀ i)) ^ 2 := by
  let gap := weightedLogLikelihood (oneWeights n) v₀ -
    weightedLogLikelihood (oneWeights n) v
  let pair := ∑ i, (w i - 1) * (Real.log (v i) - Real.log (v₀ i))
  have hgap : 0 ≤ gap := ordinary_likelihood_gap_nonneg hv₀ hv
  have hle : gap ≤ pair :=
    ordinary_gap_le_perturbation_pairing_exact w v₀ v hweighted
  have hpair : 0 ≤ pair := hgap.trans hle
  exact ((sq_le_sq₀ hgap hpair).2 hle).trans
    (perturbation_pairing_sq_le w v₀ v)

/-- If the ordinary likelihood gap has quadratic curvature `c` in the log
fitted-value displacement, weighted optimality converts the preceding bound
into an explicit stability estimate. -/
theorem logratio_sq_le_weight_deviation_sq_of_quadratic_gap
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (w v₀ v : Fin n → ℝ) {c : ℝ} (hc : 0 < c)
    (hv₀ : IsMaxOn C (weightedLogLikelihood (oneWeights n)) v₀)
    (hv : v ∈ C)
    (hweighted : weightedLogLikelihood w v₀ ≤ weightedLogLikelihood w v)
    (hcurv : c * (∑ i, (Real.log (v i) - Real.log (v₀ i)) ^ 2) ≤
      weightedLogLikelihood (oneWeights n) v₀ -
        weightedLogLikelihood (oneWeights n) v) :
    ∑ i, (Real.log (v i) - Real.log (v₀ i)) ^ 2 ≤
      (∑ i, (w i - 1) ^ 2) / c ^ 2 := by
  let T := ∑ i, (Real.log (v i) - Real.log (v₀ i)) ^ 2
  let A := ∑ i, (w i - 1) ^ 2
  let gap := weightedLogLikelihood (oneWeights n) v₀ -
    weightedLogLikelihood (oneWeights n) v
  have hT : 0 ≤ T := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hgap : 0 ≤ gap := ordinary_likelihood_gap_nonneg hv₀ hv
  have hgapSq : gap ^ 2 ≤ A * T :=
    ordinary_gap_sq_le_weight_deviation_sq_mul_logratio_sq
      w v₀ v hv₀ hv hweighted
  change T ≤ A / c ^ 2
  by_cases hT0 : T = 0
  · rw [hT0]
    positivity
  · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
    have hct : 0 ≤ c * T := mul_nonneg hc.le hT
    have hctSq : (c * T) ^ 2 ≤ gap ^ 2 := (sq_le_sq₀ hct hgap).2 hcurv
    have hmul : T * (c ^ 2 * T) ≤ T * A := by
      nlinarith [hctSq.trans hgapSq]
    have hmain : c ^ 2 * T ≤ A :=
      le_of_mul_le_mul_left hmul hTpos
    rw [le_div_iff₀ (sq_pos_of_pos hc)]
    nlinarith

/-- Local strong concavity of ordinary log likelihood.  The first-order
condition is expressed as `sum (v/v₀-1) ≤ 0`; on the radius `1/16`, the
ordinary likelihood loss controls one sixth of the squared log displacement. -/
theorem one_six_logratio_sq_le_ordinary_gap
    {n : ℕ} (v₀ v : Fin n → ℝ)
    (hv₀pos : ∀ i, 0 < v₀ i) (hvpos : ∀ i, 0 < v i)
    (hfirst : ∑ i, (v i / v₀ i - 1) ≤ 0)
    (hlocal : ∀ i, |v i / v₀ i - 1| ≤ 1 / 16) :
    (1 / 6 : ℝ) *
        ∑ i, (Real.log (v i) - Real.log (v₀ i)) ^ 2 ≤
      weightedLogLikelihood (oneWeights n) v₀ -
        weightedLogLikelihood (oneWeights n) v := by
  let u : Fin n → ℝ := fun i ↦ v i / v₀ i - 1
  have hlogeq (i : Fin n) :
      Real.log (v i) - Real.log (v₀ i) = Real.log (1 + u i) := by
    rw [show 1 + u i = v i / v₀ i by dsimp [u]; ring,
      Real.log_div (hvpos i).ne' (hv₀pos i).ne']
  have hfirst' : ∑ i, u i ≤ 0 := by simpa [u] using hfirst
  have hlogUpper :
      ∑ i, Real.log (1 + u i) ≤ -(1 / 3 : ℝ) * ∑ i, (u i) ^ 2 := by
    calc
      ∑ i, Real.log (1 + u i) ≤ ∑ i, (u i - (u i) ^ 2 / 3) := by
        apply Finset.sum_le_sum
        intro i _
        apply log_one_add_le_sub_sq_third
        exact (hlocal i).trans (by norm_num)
      _ = (∑ i, u i) - (1 / 3 : ℝ) * ∑ i, (u i) ^ 2 := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
        apply congrArg₂ (· - ·) rfl
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ -(1 / 3 : ℝ) * ∑ i, (u i) ^ 2 := by
        linarith
  have hlogSq :
      ∑ i, Real.log (1 + u i) ^ 2 ≤ 2 * ∑ i, (u i) ^ 2 :=
    sum_log_one_add_sq_le_two_sum_sq u (fun i ↦ by
      simpa [u] using hlocal i)
  have hcurv :
      (1 / 6 : ℝ) * ∑ i, Real.log (1 + u i) ^ 2 ≤
        -∑ i, Real.log (1 + u i) := by
    nlinarith
  calc
    (1 / 6 : ℝ) * ∑ i, (Real.log (v i) - Real.log (v₀ i)) ^ 2 =
        (1 / 6 : ℝ) * ∑ i, Real.log (1 + u i) ^ 2 := by
          apply congrArg ((1 / 6 : ℝ) * ·)
          apply Finset.sum_congr rfl
          intro i _
          rw [hlogeq]
    _ ≤ -∑ i, Real.log (1 + u i) := hcurv
    _ = weightedLogLikelihood (oneWeights n) v₀ -
        weightedLogLikelihood (oneWeights n) v := by
          simp only [weightedLogLikelihood_oneWeights]
          rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [← hlogeq]
          ring

/-- Concrete local stability bound: squared log displacement is at most 36
times the squared Euclidean weight perturbation. -/
theorem local_logratio_sq_le_thirtysix_weight_deviation_sq
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (w v₀ v : Fin n → ℝ)
    (hv₀ : IsMaxOn C (weightedLogLikelihood (oneWeights n)) v₀)
    (hv : v ∈ C)
    (hweighted : weightedLogLikelihood w v₀ ≤ weightedLogLikelihood w v)
    (hv₀pos : ∀ i, 0 < v₀ i) (hvpos : ∀ i, 0 < v i)
    (hfirst : ∑ i, (v i / v₀ i - 1) ≤ 0)
    (hlocal : ∀ i, |v i / v₀ i - 1| ≤ 1 / 16) :
    ∑ i, (Real.log (v i) - Real.log (v₀ i)) ^ 2 ≤
      36 * ∑ i, (w i - 1) ^ 2 := by
  have h := logratio_sq_le_weight_deviation_sq_of_quadratic_gap
    w v₀ v (c := (1 / 6 : ℝ)) (by norm_num) hv₀ hv hweighted
    (one_six_logratio_sq_le_ordinary_gap v₀ v hv₀pos hvpos hfirst hlocal)
  calc
    ∑ i, (Real.log (v i) - Real.log (v₀ i)) ^ 2 ≤
        (∑ i, (w i - 1) ^ 2) / (1 / 6 : ℝ) ^ 2 := h
    _ = 36 * ∑ i, (w i - 1) ^ 2 := by ring

/-- On the same local event, the ordinary likelihood loss is at most six
times the squared Euclidean weight perturbation. -/
theorem local_ordinary_gap_le_six_weight_deviation_sq
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (w v₀ v : Fin n → ℝ)
    (hv₀ : IsMaxOn C (weightedLogLikelihood (oneWeights n)) v₀)
    (hv : v ∈ C)
    (hweighted : weightedLogLikelihood w v₀ ≤ weightedLogLikelihood w v)
    (hv₀pos : ∀ i, 0 < v₀ i) (hvpos : ∀ i, 0 < v i)
    (hfirst : ∑ i, (v i / v₀ i - 1) ≤ 0)
    (hlocal : ∀ i, |v i / v₀ i - 1| ≤ 1 / 16) :
    weightedLogLikelihood (oneWeights n) v₀ -
        weightedLogLikelihood (oneWeights n) v ≤
      6 * ∑ i, (w i - 1) ^ 2 := by
  let gap := weightedLogLikelihood (oneWeights n) v₀ -
    weightedLogLikelihood (oneWeights n) v
  let A := ∑ i, (w i - 1) ^ 2
  let T := ∑ i, (Real.log (v i) - Real.log (v₀ i)) ^ 2
  have hgap : 0 ≤ gap := ordinary_likelihood_gap_nonneg hv₀ hv
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hgapSq : gap ^ 2 ≤ A * T :=
    ordinary_gap_sq_le_weight_deviation_sq_mul_logratio_sq
      w v₀ v hv₀ hv hweighted
  have hT : T ≤ 36 * A :=
    local_logratio_sq_le_thirtysix_weight_deviation_sq
      w v₀ v hv₀ hv hweighted hv₀pos hvpos hfirst hlocal
  change gap ≤ 6 * A
  nlinarith [mul_le_mul_of_nonneg_left hT hA, sq_nonneg (gap - 6 * A)]

end ReweightedNPMLE
