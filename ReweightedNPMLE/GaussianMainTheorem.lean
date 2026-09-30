import ReweightedNPMLE.GaussianTinyJoint
import Mathlib.Tactic

/-! # Paper-level exact-regularization theorem

One constant controls all four conclusions and the joint failure probability.
The risk scale below is exactly the paper's displayed logarithmic ratio.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

namespace ReweightedNPMLE

noncomputable def gaussianPaperRiskScale (d n : ℕ) : ℝ :=
  gaussianPaperLogScale n ^ d * Real.log n / n

theorem gaussianPaperRiskScale_eq (d n : ℕ) :
    gaussianPaperRiskScale d n = Real.log (n : ℝ) ^ (d + 1) /
      ((n : ℝ) * Real.log (Real.log (n : ℝ)) ^ d) := by
  simp only [gaussianPaperRiskScale, gaussianPaperLogScale, div_pow, pow_succ,
    div_eq_mul_inv, mul_inv_rev]
  ring

noncomputable def gaussianPaperJointConstant (d : ℕ) (b : ℝ) : ℝ :=
  1 + gaussianPaperSupportConstant d 40 b + 2 * Real.sqrt (b + 4) +
    gaussianPaperRateConstant d b + (4 * (d : ℝ) + 5)

theorem gaussianPaperJointConstant_bounds (d : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    0 < gaussianPaperJointConstant d b ∧
    gaussianPaperSupportConstant d 40 b ≤ gaussianPaperJointConstant d b ∧
    2 * Real.sqrt (b + 4) ≤ gaussianPaperJointConstant d b ∧
    gaussianPaperRateConstant d b ≤ gaussianPaperJointConstant d b ∧
    4 * (d : ℝ) + 5 ≤ gaussianPaperJointConstant d b := by
  have hB : 0 ≤ gaussianPaperSupportConstant d 40 b := by
    unfold gaussianPaperSupportConstant
    positivity
  have hW : 0 ≤ 2 * Real.sqrt (b + 4) := by positivity
  have hR : 0 ≤ gaussianPaperRateConstant d b := by
    unfold gaussianPaperRateConstant gaussianPaperEntropyConstant
    positivity
  have hF : 0 < 4 * (d : ℝ) + 5 := by positivity
  unfold gaussianPaperJointConstant
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Theorem `thm:main`: a single joint event gives exact finite sparsity,
uniformly vanishing perturbations, ordinary fit control against every NPMLE,
and the global Hellinger rate. Constants and the sample threshold are uniform
over all true compact mixing laws. -/
theorem gaussian_exact_regularization_main
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
  obtain ⟨hC, hB, hW, hR, hF⟩ := gaussianPaperJointConstant_bounds d hb.le
  refine ⟨gaussianPaperJointConstant d b, hC, ?_⟩
  filter_upwards [gaussian_exact_regularization_joint_balanced_explicit hd K hKcompact hKnonempty
      hS hb.le hKbound, eventually_gaussianPaperAugmentedDimension_pos d,
    eventually_gaussianPaperLogScale_nonneg_le_log,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
    eventually_ge_atTop (1 : ℕ)] with n hmain hdim hscale hlog hn
  intro Gstar
  obtain ⟨G, hG, hGprob, hgood⟩ := hmain Gstar
  refine ⟨G, hG, ?_, ?_⟩
  · have hpow : (n : ℝ) ^ (-(b + 2)) ≤ (n : ℝ) ^ (-b) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
    exact hGprob.trans (mul_le_mul hF hpow (by positivity) hC.le)
  · intro p hp
    obtain ⟨hcoord, hpos, μ, huniq, hfinite, hcard, hcompare, hrisk⟩ := hgood p hp
    refine ⟨fun i ↦ (hcoord i).trans (div_le_div_of_nonneg_right hW (Real.sqrt_nonneg _)),
      hpos, μ, huniq, hfinite, hcard.trans (mul_le_mul_of_nonneg_right hB hdim.le), ?_, ?_⟩
    · intro μ₀ hμ₀
      obtain ⟨h0, h1, h2⟩ := hcompare μ₀ hμ₀
      have hdiv := div_le_div_of_nonneg_right hB hlog.le
      exact ⟨h0, h1.trans hdiv, h2.trans hdiv⟩
    · have hs : 0 ≤ gaussianPaperRiskScale d n := by
        unfold gaussianPaperRiskScale
        exact div_nonneg (mul_nonneg (pow_nonneg hscale.1 d) hlog.le) (Nat.cast_nonneg _)
      have hrisk' : hellingerSq volume (compactGaussianMixtureDensity μ)
          (compactGaussianMixtureDensity Gstar) ≤ gaussianPaperRateConstant d b * gaussianPaperRiskScale d n := by
        simpa only [gaussianPaperRiskScale, mul_div_assoc, mul_assoc] using hrisk
      exact hrisk'.trans (mul_le_mul_of_nonneg_right hR hs)

/-- Corollary `cor:tiny` in the paper's common-constant form. -/
theorem gaussian_exact_regularization_tiny
    {d : ℕ} (hd : 0 < d) (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S b L : ℝ} (hS : 0 ≤ S) (hb : 0 < b) (hL : 0 < L)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ Gstar : ProbabilityMeasure K,
      ∃ G : Set (GaussianDataWeight d n), MeasurableSet G ∧
        (gaussianDataWeightMeasure Gstar n ((n : ℝ) ^ (2 * L + 2))).real Gᶜ ≤
          C * (n : ℝ) ^ (-b) ∧
        ∀ p ∈ G, (∀ i, |p.2 i - 1| ≤ (n : ℝ) ^ (-L)) ∧ p.2 ∈ positiveVectors n ∧
          ∃ μ : ProbabilityMeasure K,
            gaussianProbabilityOptimizerSet (fun a : K ↦ (a : Point d)) p = {μ} ∧
            (μ : Measure K).support.Finite ∧ ((μ : Measure K).support.ncard : ℝ) ≤
              C * gaussianPaperAugmentedDimension d n ∧
            hellingerSq volume (compactGaussianMixtureDensity μ) (compactGaussianMixtureDensity Gstar) ≤
              C * gaussianPaperRiskScale d n := by
  let B := gaussianPaperSupportConstant d (8 * (2 * L + 6)) b
  let R := gaussianPaperRateConstant d b
  let F := 4 * (d : ℝ) + 5
  let C := 1 + B + R + F
  have hB : 0 ≤ B := by dsimp [B, gaussianPaperSupportConstant]; positivity
  have hR : 0 ≤ R := by
    dsimp [R, gaussianPaperRateConstant, gaussianPaperEntropyConstant]
    positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  have hRC : R ≤ C := by dsimp [C]; linarith
  have hFC : F ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  filter_upwards [gaussian_exact_regularization_joint_tiny_explicit hd K hKcompact hKnonempty
      hS hb.le hL hKbound, eventually_gaussianPaperAugmentedDimension_pos d,
    eventually_gaussianPaperLogScale_nonneg_le_log,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
    eventually_ge_atTop (1 : ℕ)] with n hmain hdim hscale hlog hn
  intro Gstar
  obtain ⟨G, hG, hGprob, hgood⟩ := hmain Gstar
  refine ⟨G, hG, ?_, ?_⟩
  · have hpow : (n : ℝ) ^ (-(b + 2)) ≤ (n : ℝ) ^ (-b) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
    exact hGprob.trans (mul_le_mul hFC hpow (by positivity) hC.le)
  · intro p hp
    obtain ⟨hcoord, hpos, μ, huniq, hfinite, hcard, hrisk⟩ := hgood p hp
    refine ⟨hcoord, hpos, μ, huniq, hfinite, hcard.trans
      (mul_le_mul_of_nonneg_right hBC hdim.le), ?_⟩
    have hs : 0 ≤ gaussianPaperRiskScale d n :=
      div_nonneg (mul_nonneg (pow_nonneg hscale.1 d) hlog.le) (Nat.cast_nonneg _)
    have hrisk' : hellingerSq volume (compactGaussianMixtureDensity μ)
        (compactGaussianMixtureDensity Gstar) ≤ R * gaussianPaperRiskScale d n := by
      simpa only [R, gaussianPaperRiskScale, mul_div_assoc, mul_assoc] using hrisk
    exact hrisk'.trans (mul_le_mul_of_nonneg_right hRC hs)

end ReweightedNPMLE
