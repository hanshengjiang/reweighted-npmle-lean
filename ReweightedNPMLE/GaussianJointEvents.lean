import ReweightedNPMLE.ParameterizedProbabilityIntegral
import ReweightedNPMLE.SmallSupportProbability
import Mathlib.Tactic

/-!
# Joint Borel events for Gaussian optimizer laws

All events concern the full probability-law optimizer space. Compact law
projection proves measurability of nonuniqueness, support failure, and
ordinary likelihood and fitted-log failures jointly in data and weights.
-/

open Set MeasureTheory
open scoped Topology BigOperators

namespace ReweightedNPMLE

abbrev GaussianDataWeight (d n : ℕ) := (Fin n → Point d) × (Fin n → ℝ)

noncomputable def gaussianProbabilityLogLikelihood {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (p : GaussianDataWeight d n × ProbabilityMeasure Θ) : ℝ :=
  weightedLogLikelihood p.1.2
    (probabilityMixtureValue (fun a i ↦ gaussianKernel d (p.1.1 i) (θ a)) p.2)

def gaussianProbabilityOptimizerSet {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (p : GaussianDataWeight d n) : Set (ProbabilityMeasure Θ) :=
  {μ | IsMaxOn univ (fun ν ↦ gaussianProbabilityLogLikelihood θ (p, ν)) μ}

theorem continuous_gaussianProbabilityLogLikelihood {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) :
    Continuous (gaussianProbabilityLogLikelihood (n := n) θ) :=
  continuous_gaussian_probabilityLogLikelihood_joint θ hθ

theorem measurableSet_gaussian_optimizer_nonunique {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) :
    MeasurableSet {p : GaussianDataWeight d n | ∃ μ ν : ProbabilityMeasure Θ,
      μ ∈ gaussianProbabilityOptimizerSet θ p ∧ ν ∈ gaussianProbabilityOptimizerSet θ p ∧ μ ≠ ν} := by
  letI : MetricSpace (ProbabilityMeasure Θ) := TopologicalSpace.metrizableSpaceMetric _
  exact measurableSet_compactOptimizer_nonunique _ (continuous_gaussianProbabilityLogLikelihood θ hθ)

theorem measurableSet_gaussian_optimizer_support_failure {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) {R : ℝ} (hR : 0 ≤ R) :
    MeasurableSet {p : GaussianDataWeight d n | ∃ μ : ProbabilityMeasure Θ,
      μ ∈ gaussianProbabilityOptimizerSet θ p ∧
        ¬((μ : Measure Θ).support.Finite ∧ ((μ : Measure Θ).support.ncard : ℝ) ≤ R)} := by
  letI : MetricSpace (ProbabilityMeasure Θ) := TopologicalSpace.metrizableSpaceMetric _
  have heq : {p : GaussianDataWeight d n | ∃ μ : ProbabilityMeasure Θ,
      μ ∈ gaussianProbabilityOptimizerSet θ p ∧
        ¬((μ : Measure Θ).support.Finite ∧ ((μ : Measure Θ).support.ncard : ℝ) ≤ R)} =
      {p | ∃ μ : ProbabilityMeasure Θ, (p, μ) ∈ compactOptimizerGraph
        (gaussianProbabilityLogLikelihood θ) ∧ μ ∉ smallSupportProbabilityLaws Θ (Nat.floor R)} := by
    ext p
    simp only [mem_setOf_eq, mem_smallSupportProbabilityLaws_iff, Nat.le_floor_iff hR]
    rfl
  rw [heq]
  exact measurableSet_exists_compactOptimizer_outside_closed _
    (continuous_gaussianProbabilityLogLikelihood θ hθ) _ (isClosed_smallSupportProbabilityLaws _)

def gaussianOptimizerComparisonGraph {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) :
    Set (GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ)) :=
  {p | p.2.1 ∈ gaussianProbabilityOptimizerSet θ p.1 ∧
    p.2.2 ∈ gaussianProbabilityOptimizerSet θ (p.1.1, 1)}

theorem isClosed_gaussianOptimizerComparisonGraph {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) :
    IsClosed (gaussianOptimizerComparisonGraph (n := n) θ) := by
  have hgraph := isClosed_compactOptimizerGraph _ (continuous_gaussianProbabilityLogLikelihood (n := n) θ hθ)
  have hmap₁ : Continuous (fun p : GaussianDataWeight d n ×
      (ProbabilityMeasure Θ × ProbabilityMeasure Θ) ↦ (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  have hmap₀ : Continuous (fun p : GaussianDataWeight d n ×
      (ProbabilityMeasure Θ × ProbabilityMeasure Θ) ↦ ((p.1.1, (1 : Fin n → ℝ)), p.2.2)) :=
    ((continuous_fst.comp continuous_fst).prodMk continuous_const).prodMk
      (continuous_snd.comp continuous_snd)
  exact (hgraph.preimage hmap₁).inter (hgraph.preimage hmap₀)

noncomputable def gaussianOrdinaryLikelihoodGap {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d)
    (p : GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ)) : ℝ :=
  gaussianProbabilityLogLikelihood θ ((p.1.1, 1), p.2.2) -
    gaussianProbabilityLogLikelihood θ ((p.1.1, 1), p.2.1)

theorem continuous_gaussianOrdinaryLikelihoodGap {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) :
    Continuous (gaussianOrdinaryLikelihoodGap (n := n) θ) := by
  have hU := continuous_gaussianProbabilityLogLikelihood (n := n) θ hθ
  have hmap₀ : Continuous (fun p : GaussianDataWeight d n ×
      (ProbabilityMeasure Θ × ProbabilityMeasure Θ) ↦ ((p.1.1, (1 : Fin n → ℝ)), p.2.2)) :=
    ((continuous_fst.comp continuous_fst).prodMk continuous_const).prodMk
      (continuous_snd.comp continuous_snd)
  have hmap₁ : Continuous (fun p : GaussianDataWeight d n ×
      (ProbabilityMeasure Θ × ProbabilityMeasure Θ) ↦ ((p.1.1, (1 : Fin n → ℝ)), p.2.1)) :=
    ((continuous_fst.comp continuous_fst).prodMk continuous_const).prodMk
      (continuous_fst.comp continuous_snd)
  exact (hU.comp hmap₀).sub (hU.comp hmap₁)

theorem measurableSet_gaussian_optimizer_likelihood_failure {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) (t : ℝ) :
    MeasurableSet {p : GaussianDataWeight d n | ∃ μ : ProbabilityMeasure Θ × ProbabilityMeasure Θ,
      (p, μ) ∈ gaussianOptimizerComparisonGraph θ ∧ t < gaussianOrdinaryLikelihoodGap θ (p, μ)} := by
  exact measurableSet_exists_closed_relation_strict_gap _
    (isClosed_gaussianOptimizerComparisonGraph θ hθ) (fun p ↦ gaussianOrdinaryLikelihoodGap θ p - t)
    ((continuous_gaussianOrdinaryLikelihoodGap θ hθ).sub continuous_const) |>.congr
      (by ext p; simp only [mem_setOf_eq, sub_pos])

noncomputable def gaussianSquaredLogRatioGap {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d)
    (p : GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ)) : ℝ :=
  ∑ i, (Real.log
    (probabilityMixtureValue (fun a j ↦ gaussianKernel d (p.1.1 j) (θ a)) p.2.1 i /
     probabilityMixtureValue (fun a j ↦ gaussianKernel d (p.1.1 j) (θ a)) p.2.2 i)) ^ 2

theorem continuous_gaussianSquaredLogRatioGap {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) :
    Continuous (gaussianSquaredLogRatioGap (n := n) θ) := by
  let F := fun p : GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ) ↦
    probabilityMixtureValue (fun a j ↦ gaussianKernel d (p.1.1 j) (θ a)) p.2.1
  let F₀ := fun p : GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ) ↦
    probabilityMixtureValue (fun a j ↦ gaussianKernel d (p.1.1 j) (θ a)) p.2.2
  have hm := continuous_gaussian_probabilityMixtureValue_joint (n := n) θ hθ
  have hmap : Continuous (fun p : GaussianDataWeight d n ×
      (ProbabilityMeasure Θ × ProbabilityMeasure Θ) ↦ (p.1.1, p.2.1)) :=
    (continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd)
  have hmap₀ : Continuous (fun p : GaussianDataWeight d n ×
      (ProbabilityMeasure Θ × ProbabilityMeasure Θ) ↦ (p.1.1, p.2.2)) :=
    (continuous_fst.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd)
  have hF : Continuous F := hm.comp hmap
  have hF₀ : Continuous F₀ := hm.comp hmap₀
  change Continuous (fun p ↦ ∑ i, (Real.log (F p i / F₀ p i)) ^ 2)
  apply continuous_finsetSum
  intro i _
  have hfi := (continuous_apply i).comp hF
  have hf₀i := (continuous_apply i).comp hF₀
  have hpos (p : GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ)) :
      0 < F p i := gaussian_probabilityMixtureValue_pos p.1.1 θ hθ p.2.1 i
  have hpos₀ (p : GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ)) :
      0 < F₀ p i := gaussian_probabilityMixtureValue_pos p.1.1 θ hθ p.2.2 i
  exact ((hfi.div hf₀i (fun p ↦ (hpos₀ p).ne')).log
    (fun p ↦ (div_pos (hpos p) (hpos₀ p)).ne')).pow 2

theorem measurableSet_gaussian_optimizer_log_fit_failure {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) (t : ℝ) :
    MeasurableSet {p : GaussianDataWeight d n | ∃ μ : ProbabilityMeasure Θ × ProbabilityMeasure Θ,
      (p, μ) ∈ gaussianOptimizerComparisonGraph θ ∧ t < gaussianSquaredLogRatioGap θ (p, μ)} := by
  exact measurableSet_exists_closed_relation_strict_gap _
    (isClosed_gaussianOptimizerComparisonGraph θ hθ) (fun p ↦ gaussianSquaredLogRatioGap θ p - t)
    ((continuous_gaussianSquaredLogRatioGap θ hθ).sub continuous_const) |>.congr
      (by ext p; simp only [mem_setOf_eq, sub_pos])

noncomputable def gaussianStructuralFailure {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (R t a : ℝ) : Set (GaussianDataWeight d n) :=
  {p | ¬((∀ i, |p.2 i - 1| ≤ a) ∧ p.2 ∈ positiveVectors n)} ∪
  {p | ∃ μ ν : ProbabilityMeasure Θ, μ ∈ gaussianProbabilityOptimizerSet θ p ∧
    ν ∈ gaussianProbabilityOptimizerSet θ p ∧ μ ≠ ν} ∪
  {p | ∃ μ : ProbabilityMeasure Θ, μ ∈ gaussianProbabilityOptimizerSet θ p ∧
    ¬((μ : Measure Θ).support.Finite ∧ ((μ : Measure Θ).support.ncard : ℝ) ≤ R)} ∪
  {p | ∃ μ : ProbabilityMeasure Θ × ProbabilityMeasure Θ,
    (p, μ) ∈ gaussianOptimizerComparisonGraph θ ∧ t < gaussianOrdinaryLikelihoodGap θ (p, μ)} ∪
  {p | ∃ μ : ProbabilityMeasure Θ × ProbabilityMeasure Θ,
    (p, μ) ∈ gaussianOptimizerComparisonGraph θ ∧ t < gaussianSquaredLogRatioGap θ (p, μ)}

theorem measurableSet_gaussianStructuralFailure {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) {R : ℝ} (hR : 0 ≤ R) (t a : ℝ) :
    MeasurableSet (gaussianStructuralFailure (n := n) θ R t a) := by
  have hcoord : MeasurableSet {p : GaussianDataWeight d n | ∀ i, |p.2 i - 1| ≤ a} := by
    have heq : {p : GaussianDataWeight d n | ∀ i, |p.2 i - 1| ≤ a} =
        ⋂ i : Fin n, {p : GaussianDataWeight d n | |p.2 i - 1| ≤ a} := by ext p; simp
    rw [heq]
    apply MeasurableSet.iInter
    intro i
    have hi : Continuous (fun p : GaussianDataWeight d n ↦ |p.2 i - 1|) :=
      continuous_abs.comp (((continuous_apply i).comp continuous_snd).sub continuous_const)
    exact measurableSet_le hi.measurable measurable_const
  have hpos : MeasurableSet {p : GaussianDataWeight d n | p.2 ∈ positiveVectors n} := by
    have heq : {p : GaussianDataWeight d n | p.2 ∈ positiveVectors n} =
        ⋂ i : Fin n, {p : GaussianDataWeight d n | 0 < p.2 i} := by ext p; simp [positiveVectors]
    rw [heq]
    exact MeasurableSet.iInter (fun i ↦ measurableSet_lt measurable_const
      ((measurable_pi_apply i).comp measurable_snd))
  have hbadcoord : MeasurableSet {p : GaussianDataWeight d n |
      ¬((∀ i, |p.2 i - 1| ≤ a) ∧ p.2 ∈ positiveVectors n)} := (hcoord.inter hpos).compl
  exact (((hbadcoord.union (measurableSet_gaussian_optimizer_nonunique θ hθ)).union
    (measurableSet_gaussian_optimizer_support_failure θ hθ hR)).union
      (measurableSet_gaussian_optimizer_likelihood_failure θ hθ t)).union
        (measurableSet_gaussian_optimizer_log_fit_failure θ hθ t)

theorem notMem_gaussianStructuralFailure_of_unique_optimizer {Θ : Type*}
    [TopologicalSpace Θ] [MeasurableSpace Θ] {d n : ℕ}
    (θ : Θ → Point d) (x : Fin n → Point d) (w : Fin n → ℝ) (R t a : ℝ)
    (hcoord : ∀ i, |w i - 1| ≤ a) (hw : w ∈ positiveVectors n)
    (μ : ProbabilityMeasure Θ) (hunique : gaussianProbabilityOptimizerSet θ (x, w) = {μ})
    (hfinite : (μ : Measure Θ).support.Finite) (hcard : ((μ : Measure Θ).support.ncard : ℝ) ≤ R)
    (hcompare : ∀ μ₀ ∈ gaussianProbabilityOptimizerSet θ (x, 1),
      gaussianOrdinaryLikelihoodGap θ ((x, w), (μ, μ₀)) ≤ t ∧
      gaussianSquaredLogRatioGap θ ((x, w), (μ, μ₀)) ≤ t) :
    (x, w) ∉ gaussianStructuralFailure θ R t a := by
  intro hbad
  simp only [gaussianStructuralFailure, mem_union, mem_setOf_eq] at hbad
  rcases hbad with (((hweight | hnonunique) | hsupport) | hgap) | hlog
  · exact hweight ⟨hcoord, hw⟩
  · obtain ⟨μ₁, μ₂, hμ₁, hμ₂, hneq⟩ := hnonunique
    rw [hunique, mem_singleton_iff] at hμ₁ hμ₂
    exact hneq (hμ₁.trans hμ₂.symm)
  · obtain ⟨ν, hν, hfail⟩ := hsupport
    rw [hunique, mem_singleton_iff] at hν
    subst ν
    exact hfail ⟨hfinite, hcard⟩
  · obtain ⟨⟨ν, μ₀⟩, hν, hfail⟩ := hgap
    have hgraph : ν ∈ gaussianProbabilityOptimizerSet θ (x, w) ∧
        μ₀ ∈ gaussianProbabilityOptimizerSet θ (x, 1) := hν
    rw [hunique, mem_singleton_iff] at hgraph
    obtain ⟨rfl, hμ₀⟩ := hgraph
    exact (not_lt_of_ge (hcompare μ₀ hμ₀).1) hfail
  · obtain ⟨⟨ν, μ₀⟩, hν, hfail⟩ := hlog
    have hgraph : ν ∈ gaussianProbabilityOptimizerSet θ (x, w) ∧
        μ₀ ∈ gaussianProbabilityOptimizerSet θ (x, 1) := hν
    rw [hunique, mem_singleton_iff] at hgraph
    obtain ⟨rfl, hμ₀⟩ := hgraph
    exact (not_lt_of_ge (hcompare μ₀ hμ₀).2) hfail

end ReweightedNPMLE
