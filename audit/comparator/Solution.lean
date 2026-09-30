import ReweightedNPMLE.GaussianMainTheorem

/-!
Solution adapter for the Comparator audit. The expected statement is written
out explicitly, then proved only by applying the unchanged production theorem.
This module does not import Challenge.lean.
-/

open Set Filter MeasureTheory ProbabilityTheory ReweightedNPMLE
open scoped Topology BigOperators ENNReal

namespace ComparatorAudit

theorem main
    {d : ℕ} (hd : 0 < d) (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S b : ℝ} (hS : 0 ≤ S) (hb : 0 < b) (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ Gstar : ProbabilityMeasure K,
      ∃ G : Set (GaussianDataWeight d n), MeasurableSet G ∧
        (gaussianDataWeightMeasure Gstar n (gaussianPaperBalancedShape d n)).real Gᶜ ≤
          C * (n : ℝ) ^ (-b) ∧
        ∀ p ∈ G, (∀ i, |p.2 i - 1| ≤ C / Real.sqrt (gaussianPaperAugmentedDimension d n)) ∧
          p.2 ∈ positiveVectors n ∧ ∃ μ : ProbabilityMeasure K,
            gaussianProbabilityOptimizerSet (fun a : K ↦ (a : Point d)) p = {μ} ∧
            (μ : Measure K).support.Finite ∧ ((μ : Measure K).support.ncard : ℝ) ≤
              C * gaussianPaperAugmentedDimension d n ∧
            (∀ μ₀ ∈ gaussianProbabilityOptimizerSet (fun a : K ↦ (a : Point d)) (p.1, 1),
              0 ≤ gaussianOrdinaryLikelihoodGap (fun a : K ↦ (a : Point d)) (p, (μ, μ₀)) ∧
              gaussianOrdinaryLikelihoodGap (fun a : K ↦ (a : Point d)) (p, (μ, μ₀)) ≤ C / Real.log n ∧
              gaussianSquaredLogRatioGap (fun a : K ↦ (a : Point d)) (p, (μ, μ₀)) ≤ C / Real.log n) ∧
            hellingerSq volume (compactGaussianMixtureDensity μ) (compactGaussianMixtureDensity Gstar) ≤
              C * gaussianPaperRiskScale d n := by
  exact gaussian_exact_regularization_main hd K hKcompact hKnonempty hS hb hKbound

end ComparatorAudit
