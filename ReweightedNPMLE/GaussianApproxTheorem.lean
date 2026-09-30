import ReweightedNPMLE.GaussianApproxRegularization
import Mathlib.Tactic

/-! # Statistical robustness to numerical optimization

This theorem controls every attainable approximate law simultaneously on one
Borel joint experiment event. It makes no sparsity claim for approximate laws.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

namespace ReweightedNPMLE

/-- Corollary `cor:approx`, with the fixed sufficiently small tolerance
constant `c₀ = 1/6144`. No approximate optimizer is assumed to be atomic. -/
theorem gaussian_approximate_optimizer_joint_robustness
    {d : ℕ} (hd : 0 < d) (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S b : ℝ} (hS : 0 ≤ S) (hb : 0 < b) (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ Gstar : ProbabilityMeasure K,
      ∃ G : Set (GaussianDataWeight d n), MeasurableSet G ∧
        (gaussianDataWeightMeasure Gstar n (gaussianPaperBalancedShape d n)).real Gᶜ ≤
          C * (n : ℝ) ^ (-b) ∧
        ∀ p ∈ G, ∀ μw ∈ gaussianProbabilityOptimizerSet (fun a : K ↦ (a : Point d)) p,
          ∀ ν : ProbabilityMeasure K,
            gaussianProbabilityLogLikelihood (fun a : K ↦ (a : Point d)) (p, μw) -
              gaussianPaperApproxTolerance n ≤
                gaussianProbabilityLogLikelihood (fun a : K ↦ (a : Point d)) (p, ν) →
            (∀ μ₀ ∈ gaussianProbabilityOptimizerSet (fun a : K ↦ (a : Point d)) (p.1, 1),
              0 ≤ gaussianOrdinaryLikelihoodGap (fun a : K ↦ (a : Point d)) (p, (ν, μ₀)) ∧
              gaussianOrdinaryLikelihoodGap (fun a : K ↦ (a : Point d)) (p, (ν, μ₀)) ≤ C / Real.log n ∧
              gaussianSquaredLogRatioGap (fun a : K ↦ (a : Point d)) (p, (ν, μ₀)) ≤ C / Real.log n) ∧
            hellingerSq volume (compactGaussianMixtureDensity ν) (compactGaussianMixtureDensity Gstar) ≤
              C * gaussianPaperRiskScale d n := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  letI : Nonempty K := hKnonempty.to_subtype
  let θ := fun a : K ↦ (a : Point d)
  have hθ : Continuous θ := continuous_subtype_val
  have hθbound : ∀ a : K, ‖θ a‖ ≤ S := fun a ↦ hKbound a.val a.property
  let B := gaussianPaperApproxConstant d b
  let R := gaussianPaperRateConstant d b
  let F := 4 * (d : ℝ) + 5
  let C := 1 + B + R + F
  have hB : 0 ≤ B := by dsimp [B, gaussianPaperApproxConstant, gaussianPaperSupportConstant]; positivity
  have hR : 0 ≤ R := by dsimp [R, gaussianPaperRateConstant, gaussianPaperEntropyConstant]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  have hRC : R ≤ C := by dsimp [C]; linarith
  have hFC : F ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  filter_upwards [gaussian_approx_regularization_conditional_balanced d hS hb.le θ hθ hθbound,
    compactGaussianMixture_measurable_uniform_nearMLE_event hd K hKcompact hKnonempty hS hb.le hKbound,
    eventually_gaussianPaperBalanced_conditions d hS hb.le,
    eventually_gaussianPaperLogScale_nonneg_le_log,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop B,
    eventually_ge_atTop (1 : ℕ)] with n hcond hrisk hscale hlogscale hlog hlogB hn
  intro Gstar
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  let P := compactGaussianSampleMeasure Gstar n
  let α := gaussianPaperBalancedShape d n
  let Q := gammaProductMeasure n α α
  letI : IsProbabilityMeasure Q := by
    dsimp [Q, gammaProductMeasure]
    letI : IsProbabilityMeasure (gammaMeasure α α) := isProbabilityMeasure_gammaMeasure hscale.2.1 hscale.2.1
    infer_instance
  let E : Set (GaussianDataWeight d n) := gaussianApproxFitFailure θ
    (gaussianPaperApproxTolerance n) (B / Real.log n)
  have hE : MeasurableSet E := measurableSet_gaussianApproxFitFailure θ hθ _ _
  let D : Set (Fin n → Point d) := {x | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖}
  have hD : MeasurableSet D := by
    have heq : D = ⋃ i : Fin n, {x : Fin n → Point d | gaussianPaperSampleRadius d S b n < ‖x i‖} := by
      ext x
      simp [D]
    rw [heq]
    exact MeasurableSet.iUnion (fun i ↦ measurableSet_lt measurable_const ((continuous_apply i).norm.measurable))
  have hDprob : P.real D ≤ (2 * (d : ℝ) + 1) * (n : ℝ) ^ (-(b + 2)) :=
    compactGaussianSampleMeasure_paper_radius_tail Gstar hS hb.le hKbound hlog hn
  have hsections : ∀ x ∉ D, Q.real (Prod.mk x ⁻¹' E) ≤ 3 * (n : ℝ) ^ (-(b + 2)) := by
    intro x hx
    have hxrad : ∀ i, ‖x i‖ ≤ gaussianPaperSampleRadius d S b n := by
      intro i
      by_contra h
      exact hx ⟨i, lt_of_not_ge h⟩
    obtain ⟨H, hH, hHprob, hgood⟩ := hcond x hxrad
    apply le_trans (measureReal_mono (μ := Q) (s₂ := Hᶜ) ?_) hHprob
    intro w hw
    by_contra hwH
    obtain ⟨hpos, hfit⟩ := hgood w (not_not.mp hwH)
    simp only [E, gaussianApproxFitFailure, mem_preimage, mem_union, mem_setOf_eq] at hw
    rcases hw with hgap | hlogfit
    · obtain ⟨⟨⟨μw, μ₀⟩, ν⟩, hg, hbad⟩ := hgap
      exact (not_lt_of_ge (hfit μw hg.1.1 μ₀ hg.1.2 ν hg.2).2.1) hbad
    · obtain ⟨⟨⟨μw, μ₀⟩, ν⟩, hg, hbad⟩ := hlogfit
      exact (not_lt_of_ge (hfit μw hg.1.1 μ₀ hg.1.2 ν hg.2).2.2) hbad
  have hEprob : (P.prod Q).real E ≤ (2 * (d : ℝ) + 4) * (n : ℝ) ^ (-(b + 2)) := by
    have h := measureReal_prod_le_of_uniform_section_bound P Q E hE D hD
      (show 0 ≤ 3 * (n : ℝ) ^ (-(b + 2)) by positivity) hsections
    exact h.trans (by linarith)
  obtain ⟨N, hN, hNprob, hNgood⟩ := hrisk Gstar
  refine ⟨(E ∪ (N ×ˢ univ))ᶜ, (hE.union (hN.prod MeasurableSet.univ)).compl, ?_, ?_⟩
  · simp only [compl_compl]
    have hNprod : (P.prod Q).real (N ×ˢ univ) = P.real N := by simp
    have h := measureReal_union_le (μ := P.prod Q) E (N ×ˢ univ)
    rw [hNprod] at h
    have htotal : (P.prod Q).real (E ∪ (N ×ˢ univ)) ≤ F * (n : ℝ) ^ (-(b + 2)) := by linarith
    have hpow : (n : ℝ) ^ (-(b + 2)) ≤ (n : ℝ) ^ (-b) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
    exact htotal.trans (mul_le_mul hFC hpow (by positivity) hC.le)
  · intro p hp μw hμw ν hnear
    have hpE : p ∉ E := fun h ↦ hp (Or.inl h)
    have hpN : p.1 ∉ N := fun h ↦ hp (Or.inr ⟨h, mem_univ _⟩)
    have hcompare : ∀ μ₀ ∈ gaussianProbabilityOptimizerSet θ (p.1, 1),
        0 ≤ gaussianOrdinaryLikelihoodGap θ (p, (ν, μ₀)) ∧
          gaussianOrdinaryLikelihoodGap θ (p, (ν, μ₀)) ≤ B / Real.log n ∧
          gaussianSquaredLogRatioGap θ (p, (ν, μ₀)) ≤ B / Real.log n :=
      fun μ₀ hμ₀ ↦ gaussian_approx_fit_bounds_of_notMem_failure θ p _ _ hpE μw μ₀ ν hμw hμ₀ hnear
    refine ⟨?_, ?_⟩
    · intro μ₀ hμ₀
      obtain ⟨h0, h1, h2⟩ := hcompare μ₀ hμ₀
      have hdiv := div_le_div_of_nonneg_right hBC hlog.le
      exact ⟨h0, h1.trans hdiv, h2.trans hdiv⟩
    · have ht : B / Real.log n ≤ 1 := (div_le_one hlog).mpr hlogB
      have hnearν := gaussian_optimizer_nearMLE_of_likelihood_bound θ hθ p.1 p.2 ν ht
        (fun μ₀ hμ₀ ↦ (hcompare μ₀ hμ₀).2.1) Gstar
      rw [gaussianProbabilityLogLikelihood_one, gaussianProbabilityLogLikelihood_one] at hnearν
      have hris := hNgood p.1 hpN ν hnearν
      have hris' : hellingerSq volume (compactGaussianMixtureDensity ν) (compactGaussianMixtureDensity Gstar) ≤
          R * gaussianPaperRiskScale d n := by
        simpa only [R, gaussianPaperRiskScale, mul_assoc, mul_div_assoc] using hris
      have hs : 0 ≤ gaussianPaperRiskScale d n :=
        div_nonneg (mul_nonneg (pow_nonneg hlogscale.1 d) hlog.le) (Nat.cast_nonneg _)
      exact hris'.trans (mul_le_mul_of_nonneg_right hRC hs)

end ReweightedNPMLE
