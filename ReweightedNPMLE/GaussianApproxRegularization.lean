import ReweightedNPMLE.GaussianApproxJointEvents
import Mathlib.Tactic

/-! # Conditional ordinary fit control for approximate probability laws -/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal

namespace ReweightedNPMLE

theorem gaussianProbabilityLogLikelihood_score {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ)
    (x : Fin n → Point d) (w : Fin n → ℝ) (ν : ProbabilityMeasure Θ) :
    gaussianProbabilityLogLikelihood θ ((x, w), ν) =
      weightedLogLikelihood w (fun i ↦ gaussianDensity d (x i)) +
        weightedLogLikelihood w (probabilityMixtureValue (fun a ↦ gaussianScoreFeature x (θ a)) ν) := by
  let A := fun a ↦ gaussianScoreFeature x (θ a)
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hpos : ∀ i, 0 < probabilityMixtureValue A ν i :=
    (positive_kernel_hull_properties A hA (fun _ _ ↦ Real.exp_pos _)).2.2
      (probabilityMixtureValue_mem_convexHull A hA ν)
  have hkernel : (fun a i ↦ gaussianKernel d (x i) (θ a)) =
      (fun a i ↦ gaussianDensity d (x i) * A a i) := by
    funext a i
    exact gaussianKernel_eq_density_mul_exp_score (x i) (θ a)
  unfold gaussianProbabilityLogLikelihood
  rw [hkernel, probabilityMixtureValue_coordinate_scale]
  exact weightedLogLikelihood_mul_positive _ _ _ (fun i ↦ gaussianDensity_pos d (x i)) hpos

theorem gaussianSquaredLogRatioGap_score {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (hθ : Continuous θ)
    (x : Fin n → Point d) (w : Fin n → ℝ) (ν μ₀ : ProbabilityMeasure Θ) :
    gaussianSquaredLogRatioGap θ ((x, w), (ν, μ₀)) =
      ∑ i, (fittedLogRatio
        (probabilityMixtureValue (fun a ↦ gaussianScoreFeature x (θ a)) μ₀)
        (probabilityMixtureValue (fun a ↦ gaussianScoreFeature x (θ a)) ν) i) ^ 2 := by
  let A := fun a ↦ gaussianScoreFeature x (θ a)
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hpos (μ : ProbabilityMeasure Θ) : ∀ i, 0 < probabilityMixtureValue A μ i :=
    (positive_kernel_hull_properties A hA (fun _ _ ↦ Real.exp_pos _)).2.2
      (probabilityMixtureValue_mem_convexHull A hA μ)
  have hkernel : (fun a i ↦ gaussianKernel d (x i) (θ a)) =
      (fun a i ↦ gaussianDensity d (x i) * A a i) := by
    funext a i
    exact gaussianKernel_eq_density_mul_exp_score (x i) (θ a)
  unfold gaussianSquaredLogRatioGap
  dsimp only
  rw [hkernel, probabilityMixtureValue_coordinate_scale, probabilityMixtureValue_coordinate_scale]
  apply Finset.sum_congr rfl
  intro i _
  change (Real.log ((gaussianDensity d (x i) * probabilityMixtureValue A ν i) /
    (gaussianDensity d (x i) * probabilityMixtureValue A μ₀ i))) ^ 2 = _
  rw [mul_div_mul_left _ _ (gaussianDensity_pos d (x i)).ne',
    Real.log_div (hpos ν i).ne' (hpos μ₀ i).ne']
  rfl

noncomputable def gaussianPaperApproxTolerance (n : ℕ) : ℝ :=
  (1 / 6144) / Real.log n

noncomputable def gaussianPaperApproxConstant (d : ℕ) (b : ℝ) : ℝ :=
  gaussianPaperSupportConstant d 40 b + 10000000 / 6144

/-- The approximate-fit part holds simultaneously for all attainable laws on
one conditional weight event, at the paper's tolerance `c₀ / log n`. -/
theorem gaussian_approx_regularization_conditional_balanced {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b)
    (θ : Θ → Point d) (hθ : Continuous θ) (hθbound : ∀ a, ‖θ a‖ ≤ S) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → Point d,
      (∀ i, ‖x i‖ ≤ gaussianPaperSampleRadius d S b n) →
      ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
        (gammaProductMeasure n (gaussianPaperBalancedShape d n)
          (gaussianPaperBalancedShape d n)).real Gᶜ ≤ 3 * (n : ℝ) ^ (-(b + 2)) ∧
        ∀ w ∈ G, w ∈ positiveVectors n ∧
          ∀ μw ∈ gaussianProbabilityOptimizerSet θ (x, w),
            ∀ μ₀ ∈ gaussianProbabilityOptimizerSet θ (x, 1), ∀ ν : ProbabilityMeasure Θ,
              gaussianProbabilityLogLikelihood θ ((x, w), μw) - gaussianPaperApproxTolerance n ≤
                gaussianProbabilityLogLikelihood θ ((x, w), ν) →
              0 ≤ gaussianOrdinaryLikelihoodGap θ ((x, w), (ν, μ₀)) ∧
                gaussianOrdinaryLikelihoodGap θ ((x, w), (ν, μ₀)) ≤
                  gaussianPaperApproxConstant d b / Real.log n ∧
                gaussianSquaredLogRatioGap θ ((x, w), (ν, μ₀)) ≤
                  gaussianPaperApproxConstant d b / Real.log n := by
  filter_upwards [eventually_gaussianPaperBalanced_conditions d hS hb,
    eventually_gaussianPaperBalanced_likelihood_bound d (show (0 : ℝ) < 40 by norm_num) hb,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 1,
    eventually_ge_atTop (1 : ℕ)] with n hc hbase hlog hn
  change 1 < Real.log (n : ℝ) at hlog
  change 10000000 * ((gaussianPaperStructuralRank d 40 n : ℝ) + gaussianPaperStructuralTail b n) /
    gaussianPaperBalancedShape d n ≤ gaussianPaperSupportConstant d 40 b / Real.log n at hbase
  intro x hx
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by omega)
  have hT : 0 ≤ gaussianPaperSampleRadius d S b n := by dsimp [gaussianPaperSampleRadius]; positivity
  obtain ⟨G, hG, hGprob, hgood⟩ := gaussian_effective_dimension_full_support
    (gaussianPaperMomentOrder 40 n) hc.1 hT hS x hx θ hθ hθbound hc.2.2.1 hc.2.2.2
  let A := fun a ↦ gaussianScoreFeature x (θ a)
  let vhat := gaussianCanonicalFit x θ hθ
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hfit (w : Fin n → ℝ) := gaussianCanonicalFit_isMax x θ hθ w
  have hτ0 : 0 ≤ gaussianPaperApproxTolerance n := by
    unfold gaussianPaperApproxTolerance
    positivity
  have hτlt : gaussianPaperApproxTolerance n < 1 / 3072 := by
    unfold gaussianPaperApproxTolerance
    have hl : 0 < Real.log (n : ℝ) := by linarith
    apply (div_lt_iff₀ hl).mpr
    nlinarith
  have heffbound : 10000000 *
      (((gaussianPaperStructuralRank d 40 n : ℝ) + gaussianPaperStructuralTail b n) /
        gaussianPaperBalancedShape d n + gaussianPaperApproxTolerance n) ≤
      gaussianPaperApproxConstant d b / Real.log n := by
    calc
      _ = 10000000 * ((gaussianPaperStructuralRank d 40 n : ℝ) + gaussianPaperStructuralTail b n) /
        gaussianPaperBalancedShape d n + 10000000 * gaussianPaperApproxTolerance n := by ring
      _ ≤ gaussianPaperSupportConstant d 40 b / Real.log n +
        10000000 * gaussianPaperApproxTolerance n := by linarith
      _ = _ := by
        simp only [gaussianPaperApproxConstant, gaussianPaperApproxTolerance, div_eq_mul_inv]
        ring
  refine ⟨G, hG, ?_, ?_⟩
  · rw [← gaussianPaperStructural_failure_bound (by omega : 0 < n) b]
    exact hGprob
  · intro w hw
    obtain ⟨_, hpos, _, _, _, _, _, hnearfit⟩ := hgood w hw
    refine ⟨hpos, ?_⟩
    intro μw hμw μ₀ hμ₀ ν hnear
    have hμwscore := (gaussian_probability_optimizer_iff_score_fiber x θ hθ w (vhat w)
      hpos (hfit w) μw).mp hμw
    have hμ₀score := (gaussian_probability_optimizer_iff_score_fiber x θ hθ 1 (vhat 1)
      (fun _ ↦ by norm_num) (hfit 1) μ₀).mp hμ₀
    have hμwval : probabilityMixtureValue A μw = vhat w := hμwscore
    have hμ₀val : probabilityMixtureValue A μ₀ = vhat 1 := hμ₀score
    have hnearA : weightedLogLikelihood w (vhat w) - gaussianPaperApproxTolerance n ≤
        weightedLogLikelihood w (probabilityMixtureValue A ν) := by
      rw [gaussianProbabilityLogLikelihood_score θ hθ, gaussianProbabilityLogLikelihood_score θ hθ] at hnear
      change weightedLogLikelihood w (fun i ↦ gaussianDensity d (x i)) +
        weightedLogLikelihood w (probabilityMixtureValue A μw) - _ ≤ _ at hnear
      rw [hμwval] at hnear
      linarith
    obtain ⟨h0, h1, h2⟩ := hnearfit (gaussianPaperApproxTolerance n) hτ0 hτlt
      (probabilityMixtureValue A ν) (probabilityMixtureValue_mem_convexHull A hA ν) hnearA
    have hgapEq : gaussianOrdinaryLikelihoodGap θ ((x, w), (ν, μ₀)) =
        weightedLogLikelihood 1 (vhat 1) - weightedLogLikelihood 1 (probabilityMixtureValue A ν) := by
      unfold gaussianOrdinaryLikelihoodGap
      rw [gaussianProbabilityLogLikelihood_score θ hθ, gaussianProbabilityLogLikelihood_score θ hθ]
      change _ + weightedLogLikelihood 1 (probabilityMixtureValue A μ₀) - _ = _
      rw [hμ₀val]
      ring
    have hlogEq : gaussianSquaredLogRatioGap θ ((x, w), (ν, μ₀)) =
        ∑ i, (fittedLogRatio (vhat 1) (probabilityMixtureValue A ν) i) ^ 2 := by
      rw [gaussianSquaredLogRatioGap_score θ hθ]
      change (∑ i, (fittedLogRatio (probabilityMixtureValue A μ₀) (probabilityMixtureValue A ν) i) ^ 2) = _
      rw [hμ₀val]
    rw [hgapEq, hlogEq]
    exact ⟨h0, h1.trans heffbound, h2.trans heffbound⟩

end ReweightedNPMLE
