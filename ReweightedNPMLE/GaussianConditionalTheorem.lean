import ReweightedNPMLE.GaussianApproxRegularization
import Mathlib.Tactic

/-! # Conditional Gaussian sparsity for every deterministic dataset

No genericity or sampling assumption is used. The support statistic concerns
extreme laws, while all exact optimizers have the same controlled fitted values.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

namespace ReweightedNPMLE

theorem maximumExtremeSupport_coordinate_scale {Θ : Type*}
    [TopologicalSpace Θ] [MeasurableSpace Θ] {n : ℕ}
    (A : Θ → Fin n → ℝ) (c : Fin n → ℝ) (hc : ∀ i, c i ≠ 0)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ)) (w : Fin n → ℝ) :
    maximumExtremeSupport (fun a i ↦ c i * A a i) (fun q ↦ c * vhat q) w =
      maximumExtremeSupport A vhat w := by
  unfold maximumExtremeSupport
  congr 1
  ext k
  simp only [fullExtremeSupportEvent, mem_setOf_eq,
    isExtremeProbabilityMixture_coordinate_scale A c (vhat w) hc]

noncomputable def gaussianMaximumExtremeSupport {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) (x : Fin n → Point d)
    (w : Fin n → ℝ) : ℕ :=
  maximumExtremeSupport (fun a i ↦ gaussianKernel d (x i) (θ a))
    (fun q i ↦ gaussianDensity d (x i) * gaussianCanonicalFit x θ hθ q i) w

theorem gaussianMaximumExtremeSupport_eq_score {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ) (x : Fin n → Point d)
    (w : Fin n → ℝ) :
    gaussianMaximumExtremeSupport θ hθ x w =
      maximumExtremeSupport (fun a ↦ gaussianScoreFeature x (θ a))
        (gaussianCanonicalFit x θ hθ) w := by
  have hkernel : (fun a i ↦ gaussianKernel d (x i) (θ a)) =
      (fun a i ↦ gaussianDensity d (x i) * gaussianScoreFeature x (θ a) i) := by
    funext a i
    exact gaussianKernel_eq_density_mul_exp_score (x i) (θ a)
  unfold gaussianMaximumExtremeSupport
  rw [hkernel]
  exact maximumExtremeSupport_coordinate_scale _ _
    (fun i ↦ (gaussianDensity_pos d (x i)).ne') _ w

theorem gaussianPaperSampleRadius_ge_sqrt_log {d n : ℕ} (hd : 0 < d)
    {S b C₀ : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) (hlog : 0 ≤ Real.log (n : ℝ)) :
    C₀ * Real.sqrt (Real.log (n : ℝ)) ≤
      gaussianPaperSampleRadius d S (b + C₀ ^ 2 + 4) n := by
  have hdcast : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hdsqrt : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.le_sqrt_of_sq_le (by norm_num; omega)
  have hsq : (C₀ * Real.sqrt (Real.log (n : ℝ))) ^ 2 ≤
      2 * gaussianPaperRadiusExponent (b + C₀ ^ 2 + 4) n := by
    unfold gaussianPaperRadiusExponent
    nlinarith [Real.sq_sqrt hlog, sq_nonneg C₀]
  have hroot := Real.le_sqrt_of_sq_le hsq
  unfold gaussianPaperSampleRadius
  nlinarith [Real.sqrt_nonneg (2 * gaussianPaperRadiusExponent (b + C₀ ^ 2 + 4) n)]

/-- Corollary `cor:conditional`: all datasets of radius `C₀ sqrt(log n)`
are allowed, not merely a conull generic subset. -/
theorem gaussian_conditional_structural_and_likelihood_bounds {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d : ℕ} (hd : 0 < d) {S b C₀ : ℝ} (hS : 0 ≤ S) (hb : 0 < b)
    (θ : Θ → Point d) (hθ : Continuous θ) (hθbound : ∀ a, ‖θ a‖ ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → Point d,
      (∀ i, ‖x i‖ ≤ C₀ * Real.sqrt (Real.log (n : ℝ))) →
      ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
        (gammaProductMeasure n (gaussianPaperBalancedShape d n)
          (gaussianPaperBalancedShape d n)).real Gᶜ ≤ C * (n : ℝ) ^ (-b) ∧
        ∀ w ∈ G, w ∈ positiveVectors n ∧
          (gaussianMaximumExtremeSupport θ hθ x w : ℝ) ≤ C * gaussianPaperAugmentedDimension d n ∧
          (∀ i, |w i - 1| ≤ C / Real.sqrt (gaussianPaperAugmentedDimension d n)) ∧
          ∀ μw ∈ gaussianProbabilityOptimizerSet θ (x, w),
            ∀ μ₀ ∈ gaussianProbabilityOptimizerSet θ (x, 1),
              0 ≤ gaussianOrdinaryLikelihoodGap θ ((x, w), (μw, μ₀)) ∧
              gaussianOrdinaryLikelihoodGap θ ((x, w), (μw, μ₀)) ≤ C / Real.log n ∧
              gaussianSquaredLogRatioGap θ ((x, w), (μw, μ₀)) ≤ C / Real.log n := by
  let b' := b + C₀ ^ 2 + 4
  have hb' : 0 ≤ b' := by dsimp [b']; positivity
  let B := gaussianPaperSupportConstant d 40 b'
  let D := gaussianPaperApproxConstant d b'
  let W := 2 * Real.sqrt (b' + 4)
  let C := 1 + B + D + W + 6
  have hB : 0 ≤ B := by dsimp [B, gaussianPaperSupportConstant]; positivity
  have hD : 0 ≤ D := by dsimp [D, gaussianPaperApproxConstant]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  have hDC : D ≤ C := by dsimp [C]; linarith
  have hWC : W ≤ C := by dsimp [C]; linarith
  have h6C : 6 ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  filter_upwards [gaussian_approx_regularization_conditional_balanced d hS hb' θ hθ hθbound,
    eventually_gaussianPaperBalanced_conditions d hS hb',
    eventually_gaussianPaper_rank_tail_le d (show (0 : ℝ) < 40 by norm_num) hb',
    eventually_gaussianPaperBalanced_weight_bound d hb',
    eventually_gaussianPaperAugmentedDimension_pos d,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
    eventually_ge_atTop (1 : ℕ)] with n happrox hc hrank hweight hdim hlog hn
  intro x hx
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  have hxrad : ∀ i, ‖x i‖ ≤ gaussianPaperSampleRadius d S b' n :=
    fun i ↦ (hx i).trans (gaussianPaperSampleRadius_ge_sqrt_log hd hS hb.le hlog.le)
  obtain ⟨G₁, hG₁, hG₁prob, hG₁good⟩ := happrox x hxrad
  have hT : 0 ≤ gaussianPaperSampleRadius d S b' n := by dsimp [gaussianPaperSampleRadius]; positivity
  obtain ⟨G₂, hG₂, hG₂prob, hG₂good⟩ := gaussian_effective_dimension_full_support
    (gaussianPaperMomentOrder 40 n) hc.1 hT hS x hxrad θ hθ hθbound hc.2.2.1 hc.2.2.2
  let Q := gammaProductMeasure n (gaussianPaperBalancedShape d n) (gaussianPaperBalancedShape d n)
  letI : IsProbabilityMeasure Q := by
    dsimp [Q, gammaProductMeasure]
    letI : IsProbabilityMeasure (gammaMeasure (gaussianPaperBalancedShape d n)
      (gaussianPaperBalancedShape d n)) := isProbabilityMeasure_gammaMeasure hc.2.1 hc.2.1
    infer_instance
  have hsmall : 10000000 * ((gaussianPaperStructuralRank d 40 n : ℝ) +
      gaussianPaperStructuralTail b' n) ≤ B * gaussianPaperAugmentedDimension d n := by
    have h := mul_le_mul_of_nonneg_left hrank (by norm_num : (0 : ℝ) ≤ 10000000)
    simpa only [B, gaussianPaperSupportConstant, mul_assoc] using h
  refine ⟨G₁ ∩ G₂, hG₁.inter hG₂, ?_, ?_⟩
  · rw [compl_inter]
    have h₂ : Q.real G₂ᶜ ≤ 3 * (n : ℝ) ^ (-(b' + 2)) := by
      rw [← gaussianPaperStructural_failure_bound (by omega : 0 < n) b']
      exact hG₂prob
    have htot : Q.real (G₁ᶜ ∪ G₂ᶜ) ≤ 6 * (n : ℝ) ^ (-(b' + 2)) :=
      (measureReal_union_le _ _).trans (by linarith)
    have hpow : (n : ℝ) ^ (-(b' + 2)) ≤ (n : ℝ) ^ (-b) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by dsimp [b']; nlinarith [sq_nonneg C₀])
    exact htot.trans (mul_le_mul h6C hpow (by positivity) hC.le)
  · intro w hw
    obtain ⟨hpos, hfit⟩ := hG₁good w hw.1
    obtain ⟨hcoord, _, hstat, _, _, _, _, _⟩ := hG₂good w hw.2
    change (maximumExtremeSupport (fun a ↦ gaussianScoreFeature x (θ a))
      (gaussianCanonicalFit x θ hθ) w : ℝ) ≤
        10000000 * ((gaussianPaperStructuralRank d 40 n : ℝ) + gaussianPaperStructuralTail b' n) at hstat
    refine ⟨hpos, ?_, ?_, ?_⟩
    · rw [gaussianMaximumExtremeSupport_eq_score]
      exact (hstat.trans hsmall).trans (mul_le_mul_of_nonneg_right hBC hdim.le)
    · intro i
      exact ((hcoord i).trans hweight).trans (div_le_div_of_nonneg_right hWC (Real.sqrt_nonneg _))
    · intro μw hμw μ₀ hμ₀
      have hτ : 0 ≤ gaussianPaperApproxTolerance n := by unfold gaussianPaperApproxTolerance; positivity
      obtain ⟨h0, h1, h2⟩ := hfit μw hμw μ₀ hμ₀ μw (by linarith)
      have hdiv := div_le_div_of_nonneg_right hDC hlog.le
      exact ⟨h0, h1.trans hdiv, h2.trans hdiv⟩

end ReweightedNPMLE
