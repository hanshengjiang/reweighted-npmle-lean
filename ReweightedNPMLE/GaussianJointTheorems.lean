import ReweightedNPMLE.GaussianJointStructural
import ReweightedNPMLE.GaussianSampling
import Mathlib.Tactic

/-!
# Exact regularization on one joint probability event

The experiment is the independent product of the actual iid Gaussian-mixture
sample law and the Gamma weight law. A measurable hull of the uniform near-MLE
risk exception suffices: no measurable choice of an optimizing mixing law is
assumed.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

namespace ReweightedNPMLE

noncomputable def gaussianDataWeightMeasure {d : ℕ} {K : Set (Point d)}
    (Gstar : ProbabilityMeasure K) (n : ℕ) (α : ℝ) : Measure (GaussianDataWeight d n) :=
  (compactGaussianSampleMeasure Gstar n).prod (gammaProductMeasure n α α)

theorem gaussianProbabilityLogLikelihood_one {d n : ℕ} {K : Set (Point d)}
    (x : Fin n → Point d) (G : ProbabilityMeasure K) :
    gaussianProbabilityLogLikelihood (fun a : K ↦ (a : Point d)) ((x, 1), G) =
      ∑ i, Real.log (compactGaussianMixtureDensity G (x i)) := by
  simp [gaussianProbabilityLogLikelihood, weightedLogLikelihood, probabilityMixtureValue,
    compactGaussianMixtureDensity, gaussianMixture]

/-- A Borel data event simultaneously controls every near-MLE probability law.
Its failure estimate is uniform in the true law. -/
theorem compactGaussianMixture_measurable_uniform_nearMLE_event
    {d : ℕ} (hd : 0 < d) (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    ∀ᶠ n : ℕ in atTop, ∀ Gstar : ProbabilityMeasure K,
      ∃ N : Set (Fin n → Point d), MeasurableSet N ∧
        (compactGaussianSampleMeasure Gstar n).real N ≤
          (2 * (d : ℝ) + 1) * (n : ℝ) ^ (-(b + 2)) ∧
        ∀ x ∉ N, ∀ G : ProbabilityMeasure K,
          (∑ i, Real.log (compactGaussianMixtureDensity Gstar (x i))) - 1 ≤
              ∑ i, Real.log (compactGaussianMixtureDensity G (x i)) →
          hellingerSq volume (compactGaussianMixtureDensity G)
              (compactGaussianMixtureDensity Gstar) ≤
            gaussianPaperRateConstant d b * gaussianPaperLogScale n ^ d * Real.log n / n := by
  filter_upwards [compactGaussianMixture_uniform_nearMLE_paper_rate hd K hKcompact
    hKnonempty hS hb hKbound] with n htail
  intro Gstar
  let P := compactGaussianSampleMeasure Gstar n
  let E : Set (Fin n → Point d) := {x | ∃ G : ProbabilityMeasure K,
    (∑ i, Real.log (compactGaussianMixtureDensity Gstar (x i))) - 1 ≤
      ∑ i, Real.log (compactGaussianMixtureDensity G (x i)) ∧
    gaussianPaperRateConstant d b * gaussianPaperLogScale n ^ d * Real.log n / n <
      hellingerSq volume (compactGaussianMixtureDensity G) (compactGaussianMixtureDensity Gstar)}
  refine ⟨toMeasurable P E, measurableSet_toMeasurable _ _, ?_, ?_⟩
  · change (P (toMeasurable P E)).toReal ≤ _
    rw [measure_toMeasurable]
    exact htail Gstar
  · intro x hx G hnear
    exact le_of_not_gt (fun hbad ↦ hx (subset_toMeasurable P E ⟨G, hnear, hbad⟩))

/-- Main joint theorem with explicit, separate constants. All four paper
conclusions hold on the same Borel event, uniformly over the true mixing law. -/
theorem gaussian_exact_regularization_joint_balanced_explicit
    {d : ℕ} (hd : 0 < d) (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    ∀ᶠ n : ℕ in atTop, ∀ Gstar : ProbabilityMeasure K,
      ∃ G : Set (GaussianDataWeight d n), MeasurableSet G ∧
        (gaussianDataWeightMeasure Gstar n (gaussianPaperBalancedShape d n)).real Gᶜ ≤
          (4 * (d : ℝ) + 5) * (n : ℝ) ^ (-(b + 2)) ∧
        ∀ p ∈ G,
          (∀ i, |p.2 i - 1| ≤ (2 * Real.sqrt (b + 4)) /
            Real.sqrt (gaussianPaperAugmentedDimension d n)) ∧ p.2 ∈ positiveVectors n ∧
          ∃ μ : ProbabilityMeasure K,
            gaussianProbabilityOptimizerSet (fun a : K ↦ (a : Point d)) p = {μ} ∧
            (μ : Measure K).support.Finite ∧ ((μ : Measure K).support.ncard : ℝ) ≤
              gaussianPaperSupportConstant d 40 b * gaussianPaperAugmentedDimension d n ∧
            (∀ μ₀ ∈ gaussianProbabilityOptimizerSet (fun a : K ↦ (a : Point d)) (p.1, 1),
              0 ≤ gaussianOrdinaryLikelihoodGap (fun a : K ↦ (a : Point d)) (p, (μ, μ₀)) ∧
              gaussianOrdinaryLikelihoodGap (fun a : K ↦ (a : Point d)) (p, (μ, μ₀)) ≤
                gaussianPaperSupportConstant d 40 b / Real.log n ∧
              gaussianSquaredLogRatioGap (fun a : K ↦ (a : Point d)) (p, (μ, μ₀)) ≤
                gaussianPaperSupportConstant d 40 b / Real.log n) ∧
            hellingerSq volume (compactGaussianMixtureDensity μ)
              (compactGaussianMixtureDensity Gstar) ≤
                gaussianPaperRateConstant d b * gaussianPaperLogScale n ^ d * Real.log n / n := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  letI : Nonempty K := hKnonempty.to_subtype
  let θ := fun a : K ↦ (a : Point d)
  have hθ : Continuous θ := continuous_subtype_val
  have hθbound : ∀ a : K, ‖θ a‖ ≤ S := fun a ↦ hKbound a.val a.property
  filter_upwards [gaussian_balanced_joint_structural_bound d hS hb θ hθ
      Subtype.val_injective hθbound,
    compactGaussianMixture_measurable_uniform_nearMLE_event hd K hKcompact hKnonempty hS hb hKbound,
    eventually_gaussianPaperBalanced_conditions d hS hb,
    eventually_gaussianPaperAugmentedDimension_pos d,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (gaussianPaperSupportConstant d 40 b), eventually_ge_atTop (1 : ℕ)]
    with n hstruct hrisk hscale hdim hlog hlogB hn
  intro Gstar
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  let P := compactGaussianSampleMeasure Gstar n
  let α := gaussianPaperBalancedShape d n
  let Q := gammaProductMeasure n α α
  letI : IsProbabilityMeasure Q := by
    dsimp [Q, gammaProductMeasure]
    letI : IsProbabilityMeasure (gammaMeasure α α) :=
      isProbabilityMeasure_gammaMeasure hscale.2.1 hscale.2.1
    infer_instance
  let E : Set (GaussianDataWeight d n) := gaussianStructuralFailure θ
    (gaussianPaperSupportConstant d 40 b * gaussianPaperAugmentedDimension d n)
    (gaussianPaperSupportConstant d 40 b / Real.log n)
    ((2 * Real.sqrt (b + 4)) / Real.sqrt (gaussianPaperAugmentedDimension d n))
  have hE : MeasurableSet E := measurableSet_gaussianStructuralFailure θ hθ
    (by unfold gaussianPaperSupportConstant; positivity) _ _
  have hEprob : (P.prod Q).real E ≤ (2 * (d : ℝ) + 4) * (n : ℝ) ^ (-(b + 2)) := by
    have h := hstruct P inferInstance (compactGaussianSampleMeasure_absolutelyContinuous Gstar n)
    have hrad := compactGaussianSampleMeasure_paper_radius_tail Gstar hS hb hKbound hlog hn
    exact h.trans (by linarith)
  obtain ⟨N, hN, hNprob, hNgood⟩ := hrisk Gstar
  refine ⟨(E ∪ (N ×ˢ univ))ᶜ, (hE.union (hN.prod MeasurableSet.univ)).compl, ?_, ?_⟩
  · simp only [compl_compl]
    have hNprod : (P.prod Q).real (N ×ˢ univ) = P.real N := by simp
    have h := measureReal_union_le (μ := P.prod Q) E (N ×ˢ univ)
    rw [hNprod] at h
    exact h.trans (by linarith)
  · intro p hp
    have hpE : p ∉ E := fun h ↦ hp (Or.inl h)
    have hpN : p.1 ∉ N := fun h ↦ hp (Or.inr ⟨h, mem_univ _⟩)
    obtain ⟨hcoord, hpos, μ, huniq, hfinite, hcard, hcompare⟩ :=
      gaussian_structural_conclusions_of_notMem_failure θ hθ p.1 p.2 _ _ _ hpE
    refine ⟨hcoord, hpos, μ, huniq, hfinite, hcard, hcompare, ?_⟩
    have ht : gaussianPaperSupportConstant d 40 b / Real.log n ≤ 1 :=
      (div_le_one hlog).mpr hlogB
    have hnear := gaussian_optimizer_nearMLE_of_likelihood_bound θ hθ p.1 p.2 μ ht
      (fun μ₀ hμ₀ ↦ (hcompare μ₀ hμ₀).2.1) Gstar
    rw [gaussianProbabilityLogLikelihood_one, gaussianProbabilityLogLikelihood_one] at hnear
    exact hNgood p.1 hpN μ hnear

end ReweightedNPMLE
