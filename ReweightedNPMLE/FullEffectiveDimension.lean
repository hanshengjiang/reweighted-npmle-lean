import ReweightedNPMLE.MeasureExtremeSupport
import ReweightedNPMLE.EffectiveSparsification
import Mathlib.Tactic

/-!
# Effective-dimension sparsification for the full optimizer fiber

This is the abstract paper theorem for a continuous positive dictionary on a
nonempty compact metric space. Its support statistic ranges over all extreme
probability-measure optimizers. All near-optimal-fit conclusions hold on the
same measurable event, with explicit universal constants.
-/

open Set MeasureTheory
open scoped BigOperators Topology

namespace ReweightedNPMLE

theorem positive_kernel_hull_properties {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [Nonempty Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (hApos : ∀ θ i, 0 < A θ i) :
    IsCompact (convexHull ℝ (range A)) ∧ (convexHull ℝ (range A)).Nonempty ∧
      convexHull ℝ (range A) ⊆ positiveVectors n := by
  refine ⟨isCompact_convexHull_of_isCompact (isCompact_range hA),
    (range_nonempty A).mono (subset_convexHull ℝ _), ?_⟩
  apply convexHull_min _ (convex_positiveVectors n)
  rintro v ⟨θ, rfl⟩
  exact hApos θ

/-- The full-measure form of the paper's effective-dimension theorem. The
constants are `C = 10000000` and `c = 1/3072`; no regularity, moment estimate,
or finiteness of extreme supports is assumed. -/
theorem effective_dimension_full_support
    {Θ : Type*} [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ]
    [MeasurableSpace Θ] [BorelSpace Θ]
    {n r : ℕ} [Nonempty (Fin n)] {α q η : ℝ}
    (hq : 1 ≤ q) (hη : 0 ≤ η)
    (hscale : 10000000 * ((r : ℝ) + effectiveQ n q) ≤ α)
    (hwidthScale : η * Real.sqrt (α * (n : ℝ) * effectiveQ n q) ≤ 1)
    (A : Θ → Fin n → ℝ) (hA : Continuous A) (hApos : ∀ θ i, 0 < A θ i)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hrank : Module.finrank ℝ V ≤ r)
    (hwidth : ∀ u ∈ relativeFittedSet (convexHull ℝ (range A))
      (fittedValueSelection (convexHull ℝ (range A))
        (positive_kernel_hull_properties A hA hApos).1
        (positive_kernel_hull_properties A hA hApos).2.1
        (positive_kernel_hull_properties A hA hApos).2.2 1),
      ‖WithLp.toLp 2 u - V.starProjection (WithLp.toLp 2 u)‖ ≤ η) :
    let C := convexHull ℝ (range A)
    let vhat := fittedValueSelection C (positive_kernel_hull_properties A hA hApos).1
      (positive_kernel_hull_properties A hA hApos).2.1
      (positive_kernel_hull_properties A hA hApos).2.2
    let v₀ := vhat 1
    Measurable (maximumExtremeSupport A vhat) ∧
      ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
        (gammaProductMeasure n α α).real Gᶜ ≤ 3 * Real.exp (-q) ∧
        ∀ w ∈ G, (∀ i, |w i - 1| ≤ 2 * Real.sqrt (effectiveQ n q / α)) ∧
          w ∈ positiveVectors n ∧
          (maximumExtremeSupport A vhat w : ℝ) ≤ 10000000 * ((r : ℝ) + q) ∧
          (0 < maximumExtremeSupport A vhat w ∧ maximumExtremeSupport A vhat w ≤ n ∧
            ∃ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A (vhat w) μ ∧
              (μ : Measure Θ).support.ncard = maximumExtremeSupport A vhat w) ∧
          (∀ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A (vhat w) μ →
            (μ : Measure Θ).support.Finite ∧
              ((μ : Measure Θ).support.ncard : ℝ) ≤ 10000000 * ((r : ℝ) + q)) ∧
          0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 (vhat w) ∧
          weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 (vhat w) ≤
            10000000 * ((r : ℝ) + q) / α ∧
          (∑ i, (fittedLogRatio v₀ (vhat w) i) ^ 2) ≤ 10000000 * ((r : ℝ) + q) / α ∧
          ∀ (τ : ℝ), 0 ≤ τ → τ < 1 / 3072 → ∀ v ∈ C,
            weightedLogLikelihood w (vhat w) - τ ≤ weightedLogLikelihood w v →
            0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ∧
            weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ≤
              10000000 * (((r : ℝ) + q) / α + τ) ∧
            (∑ i, (fittedLogRatio v₀ v i) ^ 2) ≤
              10000000 * (((r : ℝ) + q) / α + τ) := by
  dsimp only
  let C := convexHull ℝ (range A)
  have hC := convex_convexHull ℝ (range A)
  let hb := positive_kernel_hull_properties A hA hApos
  let vhat := fittedValueSelection C hb.1 hb.2.1 hb.2.2
  have hAC : range A ⊆ C := subset_convexHull ℝ _
  have hvmax : ∀ w ∈ positiveVectors n, IsMaxOn C (weightedLogLikelihood w) (vhat w) :=
    fun w _ ↦ fittedValueSelection_isMax C hb.1 hb.2.1 hb.2.2 w
  refine ⟨measurable_maximumExtremeSupport A hA hC hb.2.2 hAC vhat hvmax
    (canonicalFittedValue_continuousOn C hC hb.1 hb.2.1 hb.2.2), ?_⟩
  obtain ⟨G, hGmeas, hGprob, hG⟩ := effective_dimension_finite_support hq hη hscale
    hwidthScale C hC hb.1 hb.2.1 hb.2.2 (range A) (isCompact_range hA).isClosed
    hAC Subset.rfl V hrank hwidth
  refine ⟨G, hGmeas, hGprob, ?_⟩
  intro w hw
  obtain ⟨hcoord, hwpos, hs, hnonneg, hloss, hlog, hnear⟩ := hG w hw
  have heq := maximumExtremeSupport_eq_maximumIndependentSupport A hA hC hb.2.2
    hAC vhat hvmax w
  have hsfull : (maximumExtremeSupport A vhat w : ℝ) ≤ 10000000 * ((r : ℝ) + q) := by
    simpa only [heq] using hs
  refine ⟨hcoord, hwpos, hsfull,
    canonical_maximumExtremeSupport_attained A hA C hC hb.1 hb.2.1 hb.2.2 hAC
      Subset.rfl w hwpos, ?_, hnonneg, hloss, hlog, hnear⟩
  intro μ hext
  have hμ := full_extreme_optimizer_support_le_maximum A hA hC hb.2.2 hAC vhat hvmax
    w hwpos μ hext
  exact ⟨hμ.1, (Nat.cast_le.mpr hμ.2).trans hsfull⟩

end ReweightedNPMLE
