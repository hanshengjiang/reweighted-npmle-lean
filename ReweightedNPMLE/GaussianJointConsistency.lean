import ReweightedNPMLE.GaussianMainTheorem
import Mathlib.Tactic

/-! # Weak consistency of the reweighted mixing law

Any optimizer rule satisfies weak consistency. Measurability of the rule is
not needed for this outer-probability formulation. At the finitely many
irrelevant small sample sizes with nonpositive balanced shape, the experiment
uses shape one so that every experiment is a genuine probability law.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

namespace ReweightedNPMLE

noncomputable def gaussianBalancedExperimentMeasure {d : ℕ} {K : Set (Point d)}
    (Gstar : ProbabilityMeasure K) (n : ℕ) : Measure (GaussianDataWeight d n) :=
  if 0 < gaussianPaperBalancedShape d n then
    gaussianDataWeightMeasure Gstar n (gaussianPaperBalancedShape d n)
  else gaussianDataWeightMeasure Gstar n 1

instance isProbabilityMeasure_gaussianBalancedExperimentMeasure
    {d : ℕ} {K : Set (Point d)} (Gstar : ProbabilityMeasure K) (n : ℕ) :
    IsProbabilityMeasure (gaussianBalancedExperimentMeasure Gstar n) := by
  dsimp only [gaussianBalancedExperimentMeasure]
  split_ifs with hα
  · dsimp [gaussianDataWeightMeasure, gammaProductMeasure]
    letI : IsProbabilityMeasure (gammaMeasure (gaussianPaperBalancedShape d n)
      (gaussianPaperBalancedShape d n)) := isProbabilityMeasure_gammaMeasure hα hα
    infer_instance
  · dsimp [gaussianDataWeightMeasure, gammaProductMeasure]
    letI : IsProbabilityMeasure (gammaMeasure 1 1) :=
      isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
    infer_instance

theorem tendsto_gaussianPaperRiskScale_zero (d : ℕ) :
    Tendsto (gaussianPaperRiskScale d) atTop (𝓝 0) := by
  have hpoly : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) ^ (d + 1) / n) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, id_eq] using
      (Real.isLittleO_pow_log_id_atTop (n := d + 1)).tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop
  apply squeeze_zero' _ _ hpoly
  · filter_upwards [eventually_gaussianPaperLogScale_nonneg_le_log,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 0]
      with n hs hl
    exact div_nonneg (mul_nonneg (pow_nonneg hs.1 d) hl) (Nat.cast_nonneg _)
  · filter_upwards [eventually_gaussianPaperLogScale_nonneg_le_log,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 0]
      with n hs hl
    unfold gaussianPaperRiskScale
    rw [pow_succ]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs.1 hs.2 d) hl) (Nat.cast_nonneg _)

/-- Corollary `cor:weak`, for any rule selecting a weighted NPMLE at positive
weights. The sample space includes both observations and independent weights. -/
theorem gaussian_reweighted_optimizer_weak_consistency
    {d : ℕ} (hd : 0 < d) (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S : ℝ} (hS : 0 ≤ S) (hKbound : ∀ u ∈ K, ‖u‖ ≤ S)
    (Gstar : ProbabilityMeasure K)
    (Ghat : ∀ n : ℕ, GaussianDataWeight d n → ProbabilityMeasure K)
    (hGhat : ∀ n p, p.2 ∈ positiveVectors n →
      Ghat n p ∈ gaussianProbabilityOptimizerSet (fun a : K ↦ (a : Point d)) p) :
    ∀ U ∈ 𝓝 Gstar, Tendsto (fun n ↦ (gaussianBalancedExperimentMeasure Gstar n).real
      {p | Ghat n p ∉ U}) atTop (𝓝 0) := by
  apply gaussianMixture_weak_consistency_of_hellingerSq_tails hKcompact Gstar
    (gaussianBalancedExperimentMeasure Gstar) Ghat
  intro δ hδ
  have hrate : Tendsto (fun n ↦ gaussianPaperRateConstant d 1 * gaussianPaperRiskScale d n)
      atTop (𝓝 0) := by
    simpa using (tendsto_gaussianPaperRiskScale_zero d).const_mul (gaussianPaperRateConstant d 1)
  have htail : Tendsto (fun n : ℕ ↦ (4 * (d : ℝ) + 5) * (n : ℝ) ^ (-(1 + 2 : ℝ)))
      atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 + 2 by norm_num)).comp
      tendsto_natCast_atTop_atTop |>.const_mul (4 * (d : ℝ) + 5)
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ measureReal_nonneg) _ htail
  filter_upwards [gaussian_exact_regularization_joint_balanced_explicit hd K hKcompact hKnonempty
      hS (show (0 : ℝ) ≤ 1 by norm_num) hKbound,
    eventually_gaussianPaperAugmentedDimension_pos d,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
    hrate.eventually (gt_mem_nhds hδ)] with n hmain hdim hlog hsmall
  obtain ⟨G, hG, hGprob, hgood⟩ := hmain Gstar
  have hα : 0 < gaussianPaperBalancedShape d n := mul_pos hdim hlog
  have heq : gaussianBalancedExperimentMeasure Gstar n =
      gaussianDataWeightMeasure Gstar n (gaussianPaperBalancedShape d n) := by
    simp [gaussianBalancedExperimentMeasure, hα]
  letI : IsProbabilityMeasure (gaussianDataWeightMeasure Gstar n (gaussianPaperBalancedShape d n)) := by
    rw [← heq]
    infer_instance
  rw [heq]
  apply le_trans (measureReal_mono (s₂ := Gᶜ) ?_) hGprob
  intro p hp
  by_contra hpG
  obtain ⟨_, hpos, μ, huniq, _, _, _, hrisk⟩ := hgood p (not_not.mp hpG)
  have hμ : Ghat n p = μ := by
    have h := hGhat n p hpos
    rwa [huniq, mem_singleton_iff] at h
  simp only [mem_setOf_eq] at hp
  rw [hμ] at hp
  change δ ≤ hellingerSq volume (compactGaussianMixtureDensity μ)
    (compactGaussianMixtureDensity Gstar) at hp
  have hrisk' : hellingerSq volume (compactGaussianMixtureDensity μ)
      (compactGaussianMixtureDensity Gstar) ≤ gaussianPaperRateConstant d 1 * gaussianPaperRiskScale d n := by
    simpa only [gaussianPaperRiskScale, mul_div_assoc, mul_assoc] using hrisk
  exact (not_lt_of_ge (hp.trans hrisk')) hsmall

end ReweightedNPMLE
