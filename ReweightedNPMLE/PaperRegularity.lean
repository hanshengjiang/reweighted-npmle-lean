import ReweightedNPMLE.FullSupportSensitivity
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic

/-! # Continuously differentiable value and local Lipschitz fitted maps

These interfaces complete the regularity assertions on the entire positive
orthant. They apply to the actual unique fitted-vector selection, not to an
assumed smooth optimizer rule.
-/

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace ReweightedNPMLE

/-- Convexity in `lem:regularity` for the actual canonical optimized value,
not a separately hypothesized optimizer rule. The assertion holds globally. -/
theorem canonical_fitted_value_convexOn_univ
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hCcompact : IsCompact C)
    (hCnonempty : C.Nonempty) (hCpos : C ⊆ positiveVectors n) :
    ConvexOn ℝ univ
      (fittedOptimalValue (fittedValueSelection C hCcompact hCnonempty hCpos)) := by
  exact fittedOptimalValue_convexOn_univ _
    (fun w ↦ fittedValueSelection_isMax C hCcompact hCnonempty hCpos w)

theorem canonical_fitted_maps_locally_lipschitz
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty) (hCpos : C ⊆ positiveVectors n)
    {w : Fin n → ℝ} (hw : w ∈ positiveVectors n) :
    ∃ (s : Set (Fin n → ℝ)) (Kv Kz : ℝ≥0), s ∈ nhds w ∧
      LipschitzOnWith Kv (fittedValueSelection C hCcompact hCnonempty hCpos) s ∧
      LipschitzOnWith Kz (fittedLogSelection C hCcompact hCnonempty hCpos) s := by
  obtain ⟨c, B, hc, hB, hbound⟩ := exists_uniform_positive_coordinate_bounds hCcompact hCpos
  obtain ⟨a, ha, s, hs, hwa⟩ := exists_local_positive_weight_lower_bound w hw
  let v := fittedValueSelection C hCcompact hCnonempty hCpos
  have hvc : ∀ u ∈ s, ∀ i, c ≤ v u i := fun u _ i ↦
    (hbound _ (fittedValueSelection_isMax C hCcompact hCnonempty hCpos u).1 i).1
  have hvB : ∀ u ∈ s, ∀ i, v u i ≤ B := fun u _ i ↦
    (hbound _ (fittedValueSelection_isMax C hCcompact hCnonempty hCpos u).1 i).2
  have hmax : ∀ u ∈ s, IsMaxOn C (weightedLogLikelihood u) (v u) := fun u _ ↦
    fittedValueSelection_isMax C hCcompact hCnonempty hCpos u
  exact ⟨s, ⟨(n : ℝ) * B ^ 2 / (a * c), by positivity⟩,
    ⟨((n : ℝ) * B ^ 2 / (a * c)) / c, by positivity⟩, hs,
    fittedValue_lipschitzOn hC hCpos v ha hc hB hwa hvc hvB hmax,
    fittedLog_lipschitzOn hC hCpos v ha hc hB hwa hvc hvB hmax⟩

theorem continuous_fittedLogLinearFunctional {n : ℕ} :
    Continuous (fittedLogLinearFunctional (n := n)) := by
  unfold fittedLogLinearFunctional
  apply continuous_finsetSum
  intro i _
  exact (continuous_apply i).smul continuous_const

theorem canonical_fitted_value_contDiffOn_one
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty) (hCpos : C ⊆ positiveVectors n) :
    ContDiffOn ℝ 1
      (fittedOptimalValue (fittedValueSelection C hCcompact hCnonempty hCpos))
      (positiveVectors n) := by
  apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
    (n := (0 : WithTop ℕ∞)) (isOpen_positiveVectors n).uniqueDiffOn).mpr
  refine ⟨by simp, (fun w ↦ fittedLogLinearFunctional
    (fittedLogSelection C hCcompact hCnonempty hCpos w)), ?_, ?_⟩
  · rw [contDiffOn_zero]
    exact continuous_fittedLogLinearFunctional.comp_continuousOn
      (canonicalFittedLog_continuousOn C hC hCcompact hCnonempty hCpos)
  · intro w hw
    exact (canonicalFittedOptimalValue_hasFDerivAt_of_positive_weights
      C hC hCcompact hCnonempty hCpos w hw).hasFDerivWithinAt

/-- The compact, nonempty, intrinsically convex full-law optimizer fiber in
`lem:regularity` and `lem:extreme`. Its fitted vector agrees for every
optimizing law, with no finite-support assumption on that law. -/
theorem paper_full_optimizer_fiber_geometry
    {Θ : Type*} [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ]
    [MeasurableSpace Θ] [BorelSpace Θ] {n : ℕ} [Nonempty (Fin n)]
    (A : Θ → Fin n → ℝ) (hA : Continuous A) (hApos : ∀ θ i, 0 < A θ i) :
    let C := convexHull ℝ (range A)
    let v := fittedValueSelection C (positive_kernel_hull_properties A hA hApos).1
      (positive_kernel_hull_properties A hA hApos).2.1
      (positive_kernel_hull_properties A hA hApos).2.2
    ∀ w ∈ positiveVectors n, (probabilityMixtureFiber A (v w)).Nonempty ∧
      IsCompact (probabilityMixtureFiber A (v w)) ∧
      (∀ (a b : ℝ≥0) (hab : a + b = 1) (μ ν : ProbabilityMeasure Θ),
        μ ∈ probabilityMixtureFiber A (v w) → ν ∈ probabilityMixtureFiber A (v w) →
        probabilityConvexCombination a b hab μ ν ∈ probabilityMixtureFiber A (v w)) ∧
      ∀ μ : ProbabilityMeasure Θ,
        IsMaxOn univ (fun ν : ProbabilityMeasure Θ ↦
          weightedLogLikelihood w (probabilityMixtureValue A ν)) μ ↔
            μ ∈ probabilityMixtureFiber A (v w) := by
  dsimp only
  intro w hw
  have hmax := fittedValueSelection_isMax (convexHull ℝ (range A))
    (positive_kernel_hull_properties A hA hApos).1
    (positive_kernel_hull_properties A hA hApos).2.1
    (positive_kernel_hull_properties A hA hApos).2.2 w
  refine ⟨probabilityMixtureFiber_nonempty_of_mem_convexHull A hA _ hmax.1,
    isCompact_probabilityMixtureFiber A hA _, ?_, ?_⟩
  · intro a b hab μ ν hμ hν
    exact probabilityMixtureFiber_convexCombination A hA _ a b hab μ ν hμ hν
  · intro μ
    exact probability_optimizer_iff_mem_fiber A hA rfl
      (positive_kernel_hull_properties A hA hApos).2.2 w _ hw hmax μ

end ReweightedNPMLE
