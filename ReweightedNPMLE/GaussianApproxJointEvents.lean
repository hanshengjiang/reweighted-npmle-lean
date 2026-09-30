import ReweightedNPMLE.GaussianJointConsistency
import Mathlib.Tactic

/-! # Borel simultaneous approximate-fit failures

The comparison relation includes a weighted optimizer, an ordinary optimizer,
and an arbitrary attainable approximate mixing law. Closedness and compact
law projection prove joint measurability of the universal fit conclusions.
-/

open Set MeasureTheory
open scoped Topology

namespace ReweightedNPMLE

def gaussianApproxComparisonGraph {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (τ : ℝ) :
    Set (GaussianDataWeight d n × ((ProbabilityMeasure Θ × ProbabilityMeasure Θ) × ProbabilityMeasure Θ)) :=
  {p | (p.1, p.2.1) ∈ gaussianOptimizerComparisonGraph θ ∧
    gaussianProbabilityLogLikelihood θ (p.1, p.2.1.1) - τ ≤
      gaussianProbabilityLogLikelihood θ (p.1, p.2.2)}

theorem isClosed_gaussianApproxComparisonGraph {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) (τ : ℝ) :
    IsClosed (gaussianApproxComparisonGraph (n := n) θ τ) := by
  have hmap : Continuous (fun p : GaussianDataWeight d n ×
      ((ProbabilityMeasure Θ × ProbabilityMeasure Θ) × ProbabilityMeasure Θ) ↦ (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hmapw : Continuous (fun p : GaussianDataWeight d n ×
      ((ProbabilityMeasure Θ × ProbabilityMeasure Θ) × ProbabilityMeasure Θ) ↦ (p.1, p.2.1.1)) :=
    continuous_fst.prodMk (continuous_fst.comp (continuous_fst.comp continuous_snd))
  have hmapv : Continuous (fun p : GaussianDataWeight d n ×
      ((ProbabilityMeasure Θ × ProbabilityMeasure Θ) × ProbabilityMeasure Θ) ↦ (p.1, p.2.2)) :=
    continuous_fst.prodMk (continuous_snd.comp continuous_snd)
  have hU := continuous_gaussianProbabilityLogLikelihood (n := n) θ hθ
  exact ((isClosed_gaussianOptimizerComparisonGraph θ hθ).preimage hmap).inter
    (isClosed_le ((hU.comp hmapw).sub continuous_const) (hU.comp hmapv))

def gaussianApproxFitFailure {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (τ t : ℝ) : Set (GaussianDataWeight d n) :=
  {p | ∃ μ : ((ProbabilityMeasure Θ × ProbabilityMeasure Θ) × ProbabilityMeasure Θ),
    (p, μ) ∈ gaussianApproxComparisonGraph θ τ ∧
      t < gaussianOrdinaryLikelihoodGap θ (p, (μ.2, μ.1.2))} ∪
  {p | ∃ μ : ((ProbabilityMeasure Θ × ProbabilityMeasure Θ) × ProbabilityMeasure Θ),
    (p, μ) ∈ gaussianApproxComparisonGraph θ τ ∧
      t < gaussianSquaredLogRatioGap θ (p, (μ.2, μ.1.2))}

theorem measurableSet_gaussianApproxFitFailure {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) (τ t : ℝ) :
    MeasurableSet (gaussianApproxFitFailure (n := n) θ τ t) := by
  letI : MetricSpace (ProbabilityMeasure Θ) := TopologicalSpace.metrizableSpaceMetric _
  have hmap : Continuous (fun p : GaussianDataWeight d n ×
      ((ProbabilityMeasure Θ × ProbabilityMeasure Θ) × ProbabilityMeasure Θ) ↦
      (p.1, (p.2.2, p.2.1.2))) :=
    continuous_fst.prodMk ((continuous_snd.comp continuous_snd).prodMk
      (continuous_snd.comp (continuous_fst.comp continuous_snd)))
  have hgraph := isClosed_gaussianApproxComparisonGraph (n := n) θ hθ τ
  have hgap := measurableSet_exists_closed_relation_strict_gap _ hgraph
    (fun p ↦ gaussianOrdinaryLikelihoodGap θ (p.1, (p.2.2, p.2.1.2)) - t)
    (((continuous_gaussianOrdinaryLikelihoodGap θ hθ).comp hmap).sub continuous_const)
  have hlog := measurableSet_exists_closed_relation_strict_gap _ hgraph
    (fun p ↦ gaussianSquaredLogRatioGap θ (p.1, (p.2.2, p.2.1.2)) - t)
    (((continuous_gaussianSquaredLogRatioGap θ hθ).comp hmap).sub continuous_const)
  exact (hgap.congr (by ext p; simp only [mem_setOf_eq, sub_pos])).union
    (hlog.congr (by ext p; simp only [mem_setOf_eq, sub_pos]))

theorem gaussian_approx_fit_bounds_of_notMem_failure {Θ : Type*}
    [MeasurableSpace Θ] {d n : ℕ} (θ : Θ → Point d)
    (p : GaussianDataWeight d n) (τ t : ℝ)
    (hgood : p ∉ gaussianApproxFitFailure θ τ t)
    (μw μ₀ ν : ProbabilityMeasure Θ)
    (hμw : μw ∈ gaussianProbabilityOptimizerSet θ p)
    (hμ₀ : μ₀ ∈ gaussianProbabilityOptimizerSet θ (p.1, 1))
    (hnear : gaussianProbabilityLogLikelihood θ (p, μw) - τ ≤
      gaussianProbabilityLogLikelihood θ (p, ν)) :
    0 ≤ gaussianOrdinaryLikelihoodGap θ (p, (ν, μ₀)) ∧
      gaussianOrdinaryLikelihoodGap θ (p, (ν, μ₀)) ≤ t ∧
      gaussianSquaredLogRatioGap θ (p, (ν, μ₀)) ≤ t := by
  have hgraph : (p, ((μw, μ₀), ν)) ∈ gaussianApproxComparisonGraph θ τ := ⟨⟨hμw, hμ₀⟩, hnear⟩
  have hgap : gaussianOrdinaryLikelihoodGap θ (p, (ν, μ₀)) ≤ t :=
    le_of_not_gt (fun h ↦ hgood (Or.inl ⟨((μw, μ₀), ν), hgraph, h⟩))
  have hlog : gaussianSquaredLogRatioGap θ (p, (ν, μ₀)) ≤ t :=
    le_of_not_gt (fun h ↦ hgood (Or.inr ⟨((μw, μ₀), ν), hgraph, h⟩))
  exact ⟨sub_nonneg.mpr (hμ₀.2 ν (mem_univ _)), hgap, hlog⟩

end ReweightedNPMLE
