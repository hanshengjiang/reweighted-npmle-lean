import Mathlib.MeasureTheory.Function.L2Space
import ReweightedNPMLE.DirichletDistribution

/-!
# Distribution-level Dirichlet formulas

This module connects the deterministic covariance algebra to expectations
under the normalized-Gamma construction.  The first result isolates the only
remaining analytic moment calculation: once the common diagonal second
moment is known, simplex support and exchangeability force the full standard
Dirichlet covariance matrix.
 -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ReweightedNPMLE

/-- The standard Dirichlet diagonal variance, together with exchangeability
and the simplex identity already proved for the normalized-Gamma law, forces
the complete covariance formula. -/
theorem symmetricDirichletActualCovariance_eq_of_diag
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    (hdiag : ∀ i : Fin n,
      symmetricDirichletActualCovariance n α i i =
        ((n : ℝ) - 1) / ((n : ℝ) ^ 2 * ((n : ℝ) * α + 1))) :
    ∀ i j : Fin n,
      symmetricDirichletActualCovariance n α i j =
        symmetricDirichletCovariance n α i j := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [hdiag, symmetricDirichletCovariance_diag]
  · rw [symmetricDirichletCovariance_offdiag α hij]
    have hnlt : 1 < n := by
      simpa using (Fintype.one_lt_card_iff.mpr ⟨i, j, hij⟩)
    have hrel :=
      symmetricDirichletActualCovariance_diag_add_offdiag hn hα hij
    rw [hdiag i] at hrel
    have hnltR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hnlt
    have hnsub : (0 : ℝ) < (n : ℝ) - 1 := by
      linarith
    have hden : (0 : ℝ) < (n : ℝ) ^ 2 * ((n : ℝ) * α + 1) := by
      positivity
    field_simp [hden.ne'] at hrel ⊢
    nlinarith

/-- Expanding a centered Dirichlet-weighted linear statistic under the
integral gives the quadratic form of the actual covariance matrix. -/
theorem integral_symmetricDirichlet_centered_linear_sq
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    (h : Fin n → ℝ) :
    ∫ p : Fin n → ℝ,
        (∑ i, h i * (p i - 1 / n)) ^ 2
          ∂symmetricDirichletMeasure n α =
      ∑ i, ∑ j, h i * h j *
        symmetricDirichletActualCovariance n α i j := by
  have hterm (i j : Fin n) : Integrable
      (fun p : Fin n → ℝ ↦
        h i * h j * ((p i - 1 / n) * (p j - 1 / n)))
      (symmetricDirichletMeasure n α) := by
    exact (integrable_centered_coord_mul_symmetricDirichletMeasure
      hn hα i j).const_mul (h i * h j)
  calc
    (∫ p : Fin n → ℝ, (∑ i, h i * (p i - 1 / n)) ^ 2
        ∂symmetricDirichletMeasure n α) =
        ∫ p : Fin n → ℝ,
          ∑ i, ∑ j,
            h i * h j * ((p i - 1 / n) * (p j - 1 / n))
          ∂symmetricDirichletMeasure n α := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p ↦ by
        change (∑ i, h i * (p i - 1 / n)) ^ 2 =
          ∑ i, ∑ j, h i * h j * ((p i - 1 / n) * (p j - 1 / n))
        rw [pow_two, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = ∑ i, ∑ j,
        ∫ p : Fin n → ℝ,
          h i * h j * ((p i - 1 / n) * (p j - 1 / n))
          ∂symmetricDirichletMeasure n α := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum Finset.univ]
        intro j _
        exact hterm i j
      · intro i _
        exact integrable_finset_sum Finset.univ fun j _ ↦ hterm i j
    _ = ∑ i, ∑ j, h i * h j *
        symmetricDirichletActualCovariance n α i j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul]
      rfl

/-- Assuming the exact covariance identification, the variance of every
Dirichlet-weighted empirical statistic is exactly the empirical variance
divided by `nα+1`, as stated in the paper. -/
theorem symmetricDirichlet_weighted_empirical_variance_of_covariance_eq
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    (hcov : ∀ i j : Fin n,
      symmetricDirichletActualCovariance n α i j =
        symmetricDirichletCovariance n α i j)
    (h : Fin n → ℝ) :
    ∫ p : Fin n → ℝ,
        ((∑ i, p i * h i) - empiricalMean h) ^ 2
          ∂symmetricDirichletMeasure n α =
      (empiricalSecondMoment h - (empiricalMean h) ^ 2) /
        ((n : ℝ) * α + 1) := by
  have hpoint (p : Fin n → ℝ) :
      (∑ i, p i * h i) - empiricalMean h =
        ∑ i, h i * (p i - 1 / n) := by
    simp only [empiricalMean]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_div]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  calc
    (∫ p : Fin n → ℝ,
        ((∑ i, p i * h i) - empiricalMean h) ^ 2
          ∂symmetricDirichletMeasure n α) =
        ∫ p : Fin n → ℝ,
          (∑ i, h i * (p i - 1 / n)) ^ 2
          ∂symmetricDirichletMeasure n α := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p ↦ by
        change ((∑ i, p i * h i) - empiricalMean h) ^ 2 =
          (∑ i, h i * (p i - 1 / n)) ^ 2
        rw [hpoint]
    _ = ∑ i, ∑ j, h i * h j *
        symmetricDirichletActualCovariance n α i j :=
      integral_symmetricDirichlet_centered_linear_sq hn hα h
    _ = ∑ i, ∑ j, h i * h j *
        symmetricDirichletCovariance n α i j := by
      simp_rw [hcov]
    _ = (empiricalSecondMoment h - (empiricalMean h) ^ 2) /
        ((n : ℝ) * α + 1) :=
      symmetricDirichlet_linear_variance hn α hα h

/-- Cauchy--Schwarz in expectation on a probability space. -/
theorem integral_abs_le_sqrt_integral_sq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : MemLp X 2 μ) :
    ∫ ω, |X ω| ∂μ ≤ Real.sqrt (∫ ω, (X ω) ^ 2 ∂μ) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) Real.HolderConjugate.two_two
    (f := fun ω ↦ |X ω|) (g := fun _ω ↦ (1 : ℝ))
    (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
    (Filter.Eventually.of_forall fun _ ↦ zero_le_one)
    (by simpa [Real.norm_eq_abs] using hX.norm)
    (memLp_const (μ := μ) (1 : ℝ))
  simpa [Real.sqrt_eq_rpow, Real.rpow_two] using h

/-- The finite-simplex total-variation deviation used in the paper. -/
noncomputable def symmetricDirichletTVDeviation {n : ℕ}
    (p : Fin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, |p i - 1 / n|

/-- A centered coordinate of the normalized-Gamma Dirichlet vector belongs
to `L²`; simplex support supplies the uniform bound. -/
theorem memLp_centered_coord_symmetricDirichletMeasure
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (i : Fin n) :
    MemLp (fun p : Fin n → ℝ ↦ p i - 1 / n) 2
      (symmetricDirichletMeasure n α) := by
  letI : IsProbabilityMeasure (symmetricDirichletMeasure n α) :=
    symmetricDirichletMeasure_isProbability n hα
  apply MemLp.of_bound
      ((measurable_pi_apply i).sub measurable_const).aestronglyMeasurable 1
  filter_upwards [symmetricDirichletMeasure_ae_mem_finiteSimplex hn hα] with p hp
  have hpi0 : 0 ≤ p i := hp.1 i
  have hpile : p i ≤ 1 := by
    have hi := Finset.single_le_sum (fun k _ ↦ hp.1 k) (Finset.mem_univ i)
    simpa [hp.2] using hi
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv0 : 0 ≤ (1 / (n : ℝ)) := by positivity
  have hinv1 : (1 / (n : ℝ)) ≤ 1 := by
    exact (div_le_one (by positivity)).2 hnreal
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- Conditional on the exact covariance formula, the expected simplex
total-variation deviation has the manuscript's sharp square-root bound. -/
theorem symmetricDirichlet_expected_tv_le_of_covariance_eq
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α)
    (hcov : ∀ i j : Fin n,
      symmetricDirichletActualCovariance n α i j =
        symmetricDirichletCovariance n α i j) :
    ∫ p : Fin n → ℝ, symmetricDirichletTVDeviation p
        ∂symmetricDirichletMeasure n α ≤
      (1 / 2 : ℝ) * Real.sqrt (((n : ℝ) - 1) / ((n : ℝ) * α + 1)) := by
  letI : IsProbabilityMeasure (symmetricDirichletMeasure n α) :=
    symmetricDirichletMeasure_isProbability n hα
  let V : ℝ := ((n : ℝ) - 1) /
    ((n : ℝ) ^ 2 * ((n : ℝ) * α + 1))
  let R : ℝ := ((n : ℝ) - 1) / ((n : ℝ) * α + 1)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnrealOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (0 : ℝ) < (n : ℝ) * α + 1 := by positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hVR : (n : ℝ) ^ 2 * V = R := by
    dsimp [V, R]
    field_simp
  have hsecond (i : Fin n) :
      ∫ p : Fin n → ℝ, (p i - 1 / n) ^ 2
          ∂symmetricDirichletMeasure n α = V := by
    simp_rw [pow_two]
    change symmetricDirichletActualCovariance n α i i = V
    rw [hcov, symmetricDirichletCovariance_diag]
  have habs (i : Fin n) :
      ∫ p : Fin n → ℝ, |p i - 1 / n|
          ∂symmetricDirichletMeasure n α ≤ Real.sqrt V := by
    have hcs := integral_abs_le_sqrt_integral_sq
      (symmetricDirichletMeasure n α) (fun p : Fin n → ℝ ↦ p i - 1 / n)
      (memLp_centered_coord_symmetricDirichletMeasure hn hα i)
    rwa [hsecond] at hcs
  have hsqrtScale : (n : ℝ) * Real.sqrt V ≤ Real.sqrt R := by
    have hsV : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV
    have hsR : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR
    have hsV0 := Real.sqrt_nonneg V
    have hsR0 := Real.sqrt_nonneg R
    nlinarith
  have hintAbs (i : Fin n) : Integrable
      (fun p : Fin n → ℝ ↦ |p i - 1 / n|)
      (symmetricDirichletMeasure n α) := by
    have hmem := memLp_centered_coord_symmetricDirichletMeasure hn hα i
    have hint := hmem.norm.integrable (by norm_num)
    apply hint.congr
    exact Filter.Eventually.of_forall fun p ↦ by
      change ‖p i - 1 / (n : ℝ)‖ = |p i - 1 / (n : ℝ)|
      exact Real.norm_eq_abs _
  calc
    (∫ p : Fin n → ℝ, symmetricDirichletTVDeviation p
        ∂symmetricDirichletMeasure n α) =
        (1 / 2 : ℝ) * ∑ i,
          ∫ p : Fin n → ℝ, |p i - 1 / n|
            ∂symmetricDirichletMeasure n α := by
      simp_rw [symmetricDirichletTVDeviation]
      rw [integral_const_mul,
        integral_finsetSum Finset.univ (fun i _ ↦ hintAbs i)]
    _ ≤ (1 / 2 : ℝ) * ∑ _i : Fin n, Real.sqrt V := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ ↦ habs i) (by norm_num)
    _ = (1 / 2 : ℝ) * ((n : ℝ) * Real.sqrt V) := by simp
    _ ≤ (1 / 2 : ℝ) * Real.sqrt R := by gcongr
    _ = (1 / 2 : ℝ) * Real.sqrt (((n : ℝ) - 1) /
        ((n : ℝ) * α + 1)) := by rfl

end ReweightedNPMLE
