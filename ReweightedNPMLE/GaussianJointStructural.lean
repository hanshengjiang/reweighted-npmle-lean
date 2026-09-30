import ReweightedNPMLE.GaussianExactRegularization
import ReweightedNPMLE.GaussianJointEvents
import ReweightedNPMLE.ConditionalProductBound
import Mathlib.Tactic

/-!
# Joint data-and-weight structural probability

The conditional structural conclusion controls sections of one Borel joint
failure event. This makes the integrated theorem independent of any choice
of conditional good sets.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

namespace ReweightedNPMLE

theorem gaussian_balanced_structural_sections {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b)
    (θ : Θ → Point d) (hθ : Continuous θ) (hθinj : Function.Injective θ)
    (hθbound : ∀ a, ‖θ a‖ ≤ S) :
    ∀ᶠ n : ℕ in atTop,
      ∃ X : Set (Fin n → Point d), MeasurableSet X ∧ volume Xᶜ = 0 ∧
      ∀ x ∈ X, (∀ i, ‖x i‖ ≤ gaussianPaperSampleRadius d S b n) →
      (gammaProductMeasure n (gaussianPaperBalancedShape d n)
        (gaussianPaperBalancedShape d n)).real
        (Prod.mk x ⁻¹' gaussianStructuralFailure θ
          (gaussianPaperSupportConstant d 40 b * gaussianPaperAugmentedDimension d n)
          (gaussianPaperSupportConstant d 40 b / Real.log n)
          ((2 * Real.sqrt (b + 4)) / Real.sqrt (gaussianPaperAugmentedDimension d n))) ≤
        3 * (n : ℝ) ^ (-(b + 2)) := by
  filter_upwards [gaussian_exact_regularization_conditional_balanced d hS hb θ hθ hθinj hθbound,
    eventually_gaussianPaperBalanced_conditions d hS hb] with n hcond hscale
  obtain ⟨X, hX, hnull, hcond⟩ := hcond
  refine ⟨X, hX, hnull, ?_⟩
  intro x hx hrad
  obtain ⟨G, hG, hGprob, hgood⟩ := hcond x hx hrad
  let α := gaussianPaperBalancedShape d n
  let Q := gammaProductMeasure n α α
  letI : IsProbabilityMeasure Q := by
    dsimp [Q, gammaProductMeasure]
    letI : IsProbabilityMeasure (gammaMeasure α α) :=
      isProbabilityMeasure_gammaMeasure hscale.2.1 hscale.2.1
    infer_instance
  apply le_trans (measureReal_mono (μ := Q) (s₂ := Gᶜ) ?_) hGprob
  intro w hw
  by_contra hwG
  have hwG' : w ∈ G := not_not.mp hwG
  obtain ⟨hcoord, hwpos, μ, hunique, hfinite, hcard, hcompare⟩ := hgood w hwG'
  exact notMem_gaussianStructuralFailure_of_unique_optimizer θ x w _ _ _ hcoord hwpos
    μ hunique hfinite hcard (fun μ₀ hμ₀ ↦ ⟨(hcompare μ₀ hμ₀).2.1, (hcompare μ₀ hμ₀).2.2⟩) hw

/-- Integrating a Gaussian balanced structural event under any absolutely
continuous data law. Only its sample-radius failure remains on the right. -/
theorem gaussian_balanced_joint_structural_bound {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b)
    (θ : Θ → Point d) (hθ : Continuous θ) (hθinj : Function.Injective θ)
    (hθbound : ∀ a, ‖θ a‖ ≤ S) :
    ∀ᶠ n : ℕ in atTop, ∀ P : Measure (Fin n → Point d), IsProbabilityMeasure P → P ≪ volume →
      (P.prod (gammaProductMeasure n (gaussianPaperBalancedShape d n)
        (gaussianPaperBalancedShape d n))).real
        (gaussianStructuralFailure θ
          (gaussianPaperSupportConstant d 40 b * gaussianPaperAugmentedDimension d n)
          (gaussianPaperSupportConstant d 40 b / Real.log n)
          ((2 * Real.sqrt (b + 4)) / Real.sqrt (gaussianPaperAugmentedDimension d n))) ≤
      P.real {x | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖} +
        3 * (n : ℝ) ^ (-(b + 2)) := by
  filter_upwards [gaussian_balanced_structural_sections d hS hb θ hθ hθinj hθbound,
    eventually_gaussianPaperBalanced_conditions d hS hb,
    eventually_gaussianPaperAugmentedDimension_pos d] with n hsections hscale hd
  intro P hP hPac
  letI : IsProbabilityMeasure P := hP
  let α := gaussianPaperBalancedShape d n
  let Q := gammaProductMeasure n α α
  letI : IsProbabilityMeasure Q := by
    dsimp [Q, gammaProductMeasure]
    letI : IsProbabilityMeasure (gammaMeasure α α) :=
      isProbabilityMeasure_gammaMeasure hscale.2.1 hscale.2.1
    infer_instance
  obtain ⟨X, hX, hnull, hsections⟩ := hsections
  let D := Xᶜ ∪ {x : Fin n → Point d | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖}
  have hrad : MeasurableSet {x : Fin n → Point d | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖} := by
    have heq : {x : Fin n → Point d | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖} =
        ⋃ i : Fin n, {x : Fin n → Point d | gaussianPaperSampleRadius d S b n < ‖x i‖} := by
      ext x
      simp
    rw [heq]
    exact MeasurableSet.iUnion (fun i ↦ measurableSet_lt measurable_const
      ((continuous_apply i).norm.measurable))
  have hD : MeasurableSet D := hX.compl.union hrad
  have hXzero : P.real Xᶜ = 0 := by simp only [measureReal_def, hPac hnull, ENNReal.toReal_zero]
  have hDprob : P.real D ≤
      P.real {x | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖} := by
    exact (measureReal_union_le _ _).trans (by rw [hXzero, zero_add])
  have hR : 0 ≤ gaussianPaperSupportConstant d 40 b * gaussianPaperAugmentedDimension d n := by
    unfold gaussianPaperSupportConstant
    positivity
  let E : Set (GaussianDataWeight d n) := gaussianStructuralFailure θ
    (gaussianPaperSupportConstant d 40 b * gaussianPaperAugmentedDimension d n)
    (gaussianPaperSupportConstant d 40 b / Real.log n)
    ((2 * Real.sqrt (b + 4)) / Real.sqrt (gaussianPaperAugmentedDimension d n))
  have hE : MeasurableSet E := measurableSet_gaussianStructuralFailure θ hθ hR _ _
  have hsec : ∀ x ∉ D, Q.real (Prod.mk x ⁻¹' E) ≤ 3 * (n : ℝ) ^ (-(b + 2)) := by
    intro x hx
    have hxX : x ∈ X := by
      by_contra hn
      exact hx (Or.inl hn)
    have hxrad : ∀ i, ‖x i‖ ≤ gaussianPaperSampleRadius d S b n := by
      intro i
      by_contra h
      exact hx (Or.inr ⟨i, lt_of_not_ge h⟩)
    exact hsections x hxX hxrad
  have hbound := measureReal_prod_le_of_uniform_section_bound P Q E hE D hD
    (show 0 ≤ 3 * (n : ℝ) ^ (-(b + 2)) by positivity) hsec
  exact hbound.trans (by linarith)

theorem gaussian_structural_conclusions_of_notMem_failure {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} [Nonempty (Fin n)] (θ : Θ → Point d) (hθ : Continuous θ)
    (x : Fin n → Point d) (w : Fin n → ℝ) (R t a : ℝ)
    (hgood : (x, w) ∉ gaussianStructuralFailure θ R t a) :
    (∀ i, |w i - 1| ≤ a) ∧ w ∈ positiveVectors n ∧
    ∃ μ : ProbabilityMeasure Θ, gaussianProbabilityOptimizerSet θ (x, w) = {μ} ∧
      (μ : Measure Θ).support.Finite ∧ ((μ : Measure Θ).support.ncard : ℝ) ≤ R ∧
      ∀ μ₀ ∈ gaussianProbabilityOptimizerSet θ (x, 1),
        0 ≤ gaussianOrdinaryLikelihoodGap θ ((x, w), (μ, μ₀)) ∧
        gaussianOrdinaryLikelihoodGap θ ((x, w), (μ, μ₀)) ≤ t ∧
        gaussianSquaredLogRatioGap θ ((x, w), (μ, μ₀)) ≤ t := by
  classical
  simp only [gaussianStructuralFailure, mem_union, mem_setOf_eq, not_or] at hgood
  obtain ⟨⟨⟨⟨hweight, hnonunique⟩, hsupport⟩, hgap⟩, hlog⟩ := hgood
  have hw := not_not.mp hweight
  let A := fun a ↦ gaussianScoreFeature x (θ a)
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hfit := gaussianCanonicalFit_isMax x θ hθ w
  obtain ⟨μ, hμ⟩ := probabilityMixtureFiber_nonempty_of_mem_convexHull A hA
    (gaussianCanonicalFit x θ hθ w) hfit.1
  have hopt : μ ∈ gaussianProbabilityOptimizerSet θ (x, w) :=
    (gaussian_probability_optimizer_iff_score_fiber x θ hθ w _ hw.2 hfit μ).mpr hμ
  have huniq : ∀ ν ∈ gaussianProbabilityOptimizerSet θ (x, w), ν = μ := by
    intro ν hν
    by_contra hne
    exact hnonunique ⟨ν, μ, hν, hopt, hne⟩
  have hμsupport : (μ : Measure Θ).support.Finite ∧ ((μ : Measure Θ).support.ncard : ℝ) ≤ R := by
    by_contra hbad
    exact hsupport ⟨μ, hopt, hbad⟩
  refine ⟨hw.1, hw.2, μ, ?_, hμsupport.1, hμsupport.2, ?_⟩
  · ext ν
    constructor
    · exact fun hν ↦ mem_singleton_iff.mpr (huniq ν hν)
    · intro hν
      rw [mem_singleton_iff] at hν
      exact hν ▸ hopt
  · intro μ₀ hμ₀
    have hcomparison : ((x, w), (μ, μ₀)) ∈ gaussianOptimizerComparisonGraph θ := ⟨hopt, hμ₀⟩
    have hgaple : gaussianOrdinaryLikelihoodGap θ ((x, w), (μ, μ₀)) ≤ t := by
      by_contra hbad
      exact hgap ⟨(μ, μ₀), hcomparison, lt_of_not_ge hbad⟩
    have hlogle : gaussianSquaredLogRatioGap θ ((x, w), (μ, μ₀)) ≤ t := by
      by_contra hbad
      exact hlog ⟨(μ, μ₀), hcomparison, lt_of_not_ge hbad⟩
    have hmax := hμ₀.2 μ (mem_univ μ)
    exact ⟨sub_nonneg.mpr hmax, hgaple, hlogle⟩

/-- A total ordinary likelihood gap at most one implies the exact uniform
near-MLE premise, against every comparison law. -/
theorem gaussian_optimizer_nearMLE_of_likelihood_bound {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} [Nonempty (Fin n)] (θ : Θ → Point d) (hθ : Continuous θ)
    (x : Fin n → Point d) (w : Fin n → ℝ) (μ : ProbabilityMeasure Θ) {t : ℝ} (ht : t ≤ 1)
    (hbound : ∀ μ₀ ∈ gaussianProbabilityOptimizerSet θ (x, 1),
      gaussianOrdinaryLikelihoodGap θ ((x, w), (μ, μ₀)) ≤ t) :
    ∀ ν : ProbabilityMeasure Θ,
      gaussianProbabilityLogLikelihood θ ((x, 1), ν) - 1 ≤
        gaussianProbabilityLogLikelihood θ ((x, 1), μ) := by
  let A := fun a ↦ gaussianScoreFeature x (θ a)
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hfit := gaussianCanonicalFit_isMax x θ hθ 1
  obtain ⟨μ₀, hμ₀⟩ := probabilityMixtureFiber_nonempty_of_mem_convexHull A hA
    (gaussianCanonicalFit x θ hθ 1) hfit.1
  have hμ₀opt : μ₀ ∈ gaussianProbabilityOptimizerSet θ (x, 1) :=
    (gaussian_probability_optimizer_iff_score_fiber x θ hθ 1 _ (fun _ ↦ by norm_num) hfit μ₀).mpr hμ₀
  intro ν
  have hmax := hμ₀opt.2 ν (mem_univ ν)
  have hgap := (hbound μ₀ hμ₀opt).trans ht
  change gaussianProbabilityLogLikelihood θ ((x, 1), μ₀) -
    gaussianProbabilityLogLikelihood θ ((x, 1), μ) ≤ 1 at hgap
  dsimp only at hmax
  linarith

end ReweightedNPMLE
