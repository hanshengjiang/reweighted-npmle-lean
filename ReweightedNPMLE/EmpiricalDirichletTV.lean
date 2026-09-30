import ReweightedNPMLE.DirichletSecondMoment
import ReweightedNPMLE.ProbabilityOptimizerFiber
import Mathlib.Tactic

/-! # Total variation after merging repeated observations

For a finite empirical measure, total variation distance is half the sum of
absolute mass differences over the distinct observations. Unlike the indexed
weight deviation, this expression merges repeated sample points. Its expected
value satisfies the paper bound for every fixed dataset, without injectivity.
-/

open Set MeasureTheory
open scoped BigOperators

namespace ReweightedNPMLE

noncomputable def empiricalObservationSet {X : Type*} {n : ℕ} (x : Fin n → X) : Finset X := by
  classical
  exact Finset.univ.image x

noncomputable def empiricalDirichletTV {X : Type*} {n : ℕ}
    (x : Fin n → X) (p : Fin n → ℝ) : ℝ := by
  classical
  exact (1 / 2 : ℝ) * ∑ y ∈ empiricalObservationSet x,
    |∑ i, if x i = y then p i - 1 / n else 0|

theorem finiteProbabilityMeasure_real_apply {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] {n : ℕ} (x : Fin n → X) (p : Fin n → ℝ)
    (hp : p ∈ finiteSimplex n) (B : Set X) (hB : MeasurableSet B)
    [DecidablePred (· ∈ B)] :
    (finiteProbabilityMeasure x p hp : Measure X).real B =
      ∑ i, if x i ∈ B then p i else 0 := by
  classical
  change (∑ i, ENNReal.ofReal (p i) • Measure.dirac (x i)).real B = _
  rw [measureReal_def, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply' _ hB, smul_eq_mul]
  rw [ENNReal.toReal_sum (by intro i _; by_cases hi : x i ∈ B <;> simp [hi])]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i ∈ B <;> simp [hi, hp.1 i]

/-- The grouped expression is the half-`L¹` total variation of the actual
two finite empirical probability laws: the summands are their singleton
mass differences at every distinct observation. -/
theorem empiricalDirichletTV_eq_half_sum_actual_atom_mass_differences
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X] {n : ℕ}
    (x : Fin n → X) (hn : 0 < n) (p : Fin n → ℝ) (hp : p ∈ finiteSimplex n) :
    ∃ hUniform : (fun _ : Fin n ↦ 1 / (n : ℝ)) ∈ finiteSimplex n,
      empiricalDirichletTV x p = (1 / 2 : ℝ) * ∑ y ∈ empiricalObservationSet x,
        |(finiteProbabilityMeasure x p hp : Measure X).real {y} -
          (finiteProbabilityMeasure x (fun _ ↦ 1 / (n : ℝ)) hUniform : Measure X).real {y}| := by
  classical
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hUniform : (fun _ : Fin n ↦ 1 / (n : ℝ)) ∈ finiteSimplex n := by
    constructor
    · intro _
      positivity
    · simp [hnreal.ne']
  refine ⟨hUniform, ?_⟩
  unfold empiricalDirichletTV
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  rw [finiteProbabilityMeasure_real_apply x p hp _ (measurableSet_singleton y),
    finiteProbabilityMeasure_real_apply x (fun _ ↦ 1 / (n : ℝ)) hUniform _ (measurableSet_singleton y),
    ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i = y <;> simp [hi]

theorem empiricalDirichletTV_le_indexed {X : Type*} {n : ℕ}
    (x : Fin n → X) (p : Fin n → ℝ) :
    empiricalDirichletTV x p ≤ symmetricDirichletTVDeviation p := by
  classical
  unfold empiricalDirichletTV empiricalObservationSet symmetricDirichletTVDeviation
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ ∑ y ∈ Finset.univ.image x, ∑ i, |if x i = y then p i - 1 / n else 0| :=
      Finset.sum_le_sum (fun _ _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i, |p i - 1 / n| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      simp only [abs_ite, abs_zero]
      simp [eq_comm]

theorem empiricalDirichletTV_nonneg {X : Type*} {n : ℕ}
    (x : Fin n → X) (p : Fin n → ℝ) : 0 ≤ empiricalDirichletTV x p := by
  unfold empiricalDirichletTV
  positivity

theorem integrable_empiricalDirichletTV {X : Type*} {n : ℕ}
    (x : Fin n → X) {α : ℝ} (hα : 0 < α) :
    Integrable (empiricalDirichletTV x) (symmetricDirichletMeasure n α) := by
  classical
  letI : IsProbabilityMeasure (symmetricDirichletMeasure n α) :=
    symmetricDirichletMeasure_isProbability n hα
  unfold empiricalDirichletTV
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro y _
  apply Integrable.abs
  apply integrable_finsetSum
  intro i _
  by_cases hi : x i = y
  · simpa only [if_pos hi] using
      (integrable_coord_symmetricDirichletMeasure hα i).sub (integrable_const (1 / (n : ℝ)))
  · simpa only [if_neg hi] using (integrable_const (0 : ℝ) :
      Integrable (fun _ : Fin n → ℝ ↦ (0 : ℝ)) (symmetricDirichletMeasure n α))

/-- The conditional expected TV bound in `prop:dirichlet` holds even when
observations repeat. The distinct-point atom masses, rather than indexed
weights, define the empirical-measure deviation on the left. -/
theorem empiricalDirichlet_expected_tv_le {X : Type*} {n : ℕ}
    (x : Fin n → X) (hn : 0 < n) {α : ℝ} (hα : 0 < α) :
    (∫ p, empiricalDirichletTV x p ∂symmetricDirichletMeasure n α) ≤
      (1 / 2 : ℝ) * Real.sqrt (((n : ℝ) - 1) / ((n : ℝ) * α + 1)) := by
  letI : IsProbabilityMeasure (symmetricDirichletMeasure n α) :=
    symmetricDirichletMeasure_isProbability n hα
  apply le_trans _ (symmetricDirichlet_expected_tv_le hn hα)
  apply integral_mono (integrable_empiricalDirichletTV x hα) _
    (empiricalDirichletTV_le_indexed x)
  unfold symmetricDirichletTVDeviation
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro i _
  exact ((integrable_coord_symmetricDirichletMeasure hα i).sub (integrable_const _)).abs

end ReweightedNPMLE
