import ReweightedNPMLE.ProbabilityOptimizerFiber

/-! # The global numerical optimality residual

The residual in the numerical section is the supremum of the normalized
likelihood contact functional minus one. At every genuine full-measure
optimizer it is nonpositive. This is not a solver-convergence assumption.
-/

open Set
open MeasureTheory
open scoped BigOperators

namespace ReweightedNPMLE

noncomputable def numericalKKTResidual {Θ : Type*} {n : ℕ}
    (A : Θ → Fin n → ℝ) (w v : Fin n → ℝ) : ℝ :=
  sSup (range (fun θ ↦ likelihoodContactFunctional w v (A θ) - 1))

theorem numericalKKTResidual_eq_paper_formula {Θ : Type*} {n : ℕ}
    [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (w v : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) :
    numericalKKTResidual A w v =
      sSup (range (fun θ ↦
        (1 / ∑ i, w i) * (∑ i, w i * (A θ i / v i)) - 1)) := by
  have hpoint (θ : Θ) : likelihoodContactFunctional w v (A θ) =
      (1 / total w) * ∑ i, w i * (A θ i / v i) := by
    rw [likelihoodContactFunctional_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(hv i).ne', (total_pos hw).ne']
  simp only [numericalKKTResidual, hpoint, total]

theorem numericalKKTResidual_nonpos_of_fitted_optimizer
    {Θ : Type*} [Nonempty Θ] {n : ℕ} [Nonempty (Fin n)]
    (A : Θ → Fin n → ℝ) {C : Set (Fin n → ℝ)}
    (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n) (hAC : range A ⊆ C)
    (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v) :
    numericalKKTResidual A w v ≤ 0 := by
  apply csSup_le (range_nonempty _)
  rintro y ⟨θ, rfl⟩
  have h := likelihoodContactFunctional_le_one_of_isMaxOn
    hC hCpos w v (A θ) hw hvmax (hAC (mem_range_self θ))
  linarith

theorem numericalKKTResidual_nonpos_of_full_optimizer
    {Θ : Type*} [Nonempty Θ] [TopologicalSpace Θ] [CompactSpace Θ]
    [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ)
    (hA : Continuous A) (hApos : ∀ θ i, 0 < A θ i)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (μ : ProbabilityMeasure Θ)
    (hμ : IsMaxOn univ (fun ν : ProbabilityMeasure Θ ↦
      weightedLogLikelihood w (probabilityMixtureValue A ν)) μ) :
    numericalKKTResidual A w (probabilityMixtureValue A μ) ≤ 0 := by
  have hCpos : convexHull ℝ (range A) ⊆ positiveVectors n := by
    apply convexHull_min _ (convex_positiveVectors n)
    rintro a ⟨θ, rfl⟩ i
    exact hApos θ i
  have hvmax : IsMaxOn (convexHull ℝ (range A)) (weightedLogLikelihood w)
      (probabilityMixtureValue A μ) := by
    refine ⟨probabilityMixtureValue_mem_convexHull A hA μ, ?_⟩
    intro v hv
    obtain ⟨ν, hν⟩ := probabilityMixtureFiber_nonempty_of_mem_convexHull A hA v hv
    simpa only [show probabilityMixtureValue A ν = v from hν] using hμ.2 ν (mem_univ ν)
  exact numericalKKTResidual_nonpos_of_fitted_optimizer A
    (convex_convexHull ℝ (range A)) hCpos (subset_convexHull ℝ (range A))
    w (probabilityMixtureValue A μ) hw hvmax

end ReweightedNPMLE
