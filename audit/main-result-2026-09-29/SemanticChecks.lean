import ReweightedNPMLE.GaussianSupportRefinements
open Set Filter MeasureTheory ProbabilityTheory ReweightedNPMLE
open scoped Topology BigOperators ENNReal

-- Verify that the joint law really is a probability measure when its shape is positive.
example {d : ℕ} {K : Set (Point d)} (Gstar : ProbabilityMeasure K)
    (n : ℕ) {α : ℝ} (hα : 0 < α) :
    IsProbabilityMeasure (gaussianDataWeightMeasure Gstar n α) := by
  letI : IsProbabilityMeasure (gammaMeasure α α) := isProbabilityMeasure_gammaMeasure hα hα
  dsimp [gaussianDataWeightMeasure, gammaProductMeasure]
  infer_instance

-- Verify ordinary-NPMLE existence from the same proved ingredients used in the main proof.
example {d n : ℕ} [Nonempty (Fin n)] {K : Set (Point d)}
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty) (x : Fin n → Point d) :
    (gaussianProbabilityOptimizerSet (fun a : K ↦ (a : Point d)) (x, 1)).Nonempty := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  letI : Nonempty K := hKnonempty.to_subtype
  let θ := fun a : K ↦ (a : Point d)
  have hθ : Continuous θ := continuous_subtype_val
  let A := fun a ↦ gaussianScoreFeature x (θ a)
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hfit := gaussianCanonicalFit_isMax x θ hθ 1
  obtain ⟨μ₀, hμ₀⟩ := probabilityMixtureFiber_nonempty_of_mem_convexHull A hA
    (gaussianCanonicalFit x θ hθ 1) hfit.1
  exact ⟨μ₀, (gaussian_probability_optimizer_iff_score_fiber x θ hθ 1 _
    (fun _ ↦ by norm_num) hfit μ₀).mpr hμ₀⟩

#check @gaussian_main_support_dimension_refinements
#print axioms gaussian_main_support_dimension_refinements
#print axioms compactGaussianMixture_uniform_nearMLE_paper_rate
#print axioms gaussian_evaluation_independence_ae
#print axioms full_extreme_optimizer_support_finite_card_le
#print axioms canonical_maximumIndependentSupport_gamma_tail
