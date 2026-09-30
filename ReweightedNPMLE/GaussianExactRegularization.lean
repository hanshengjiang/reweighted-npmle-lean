import ReweightedNPMLE.GaussianGenericity
import ReweightedNPMLE.GaussianPaperScales
import Mathlib.Tactic

/-!
# Gaussian exact regularization

This module assembles the structural Gaussian result at the paper's actual
balanced concentration. Its optimizer sets consist of all probability laws,
not just finite atomic measures. Statistical risk is assembled separately.
-/

open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace ReweightedNPMLE

noncomputable def gaussianCanonicalFit {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ]
    {d n : ℕ} (x : Fin n → Point d) (θ : Θ → Point d) (hθ : Continuous θ) :
    (Fin n → ℝ) → (Fin n → ℝ) :=
  fittedValueSelection (convexHull ℝ (range (fun a ↦ gaussianScoreFeature x (θ a))))
    (positive_kernel_hull_properties _ ((continuous_gaussianScoreFeature x).comp hθ)
      (fun _ _ ↦ Real.exp_pos _)).1
    (positive_kernel_hull_properties _ ((continuous_gaussianScoreFeature x).comp hθ)
      (fun _ _ ↦ Real.exp_pos _)).2.1
    (positive_kernel_hull_properties _ ((continuous_gaussianScoreFeature x).comp hθ)
      (fun _ _ ↦ Real.exp_pos _)).2.2

theorem gaussianCanonicalFit_isMax {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ]
    {d n : ℕ} (x : Fin n → Point d) (θ : Θ → Point d) (hθ : Continuous θ)
    (w : Fin n → ℝ) :
    IsMaxOn (convexHull ℝ (range (fun a ↦ gaussianScoreFeature x (θ a))))
      (weightedLogLikelihood w) (gaussianCanonicalFit x θ hθ w) :=
  fittedValueSelection_isMax _ _ _ _ w

theorem weightedLogLikelihood_mul_positive {n : ℕ} (w c v : Fin n → ℝ)
    (hc : ∀ i, 0 < c i) (hv : ∀ i, 0 < v i) :
    weightedLogLikelihood w (c * v) =
      weightedLogLikelihood w c + weightedLogLikelihood w v := by
  unfold weightedLogLikelihood
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.mul_apply, Real.log_mul (hc i).ne' (hv i).ne']
  ring

theorem fittedLogRatio_mul_positive {n : ℕ} (c v₀ v : Fin n → ℝ)
    (hc : ∀ i, 0 < c i) (hv₀ : ∀ i, 0 < v₀ i) (hv : ∀ i, 0 < v i) :
    fittedLogRatio (c * v₀) (c * v) = fittedLogRatio v₀ v := by
  funext i
  simp only [fittedLogRatio, Pi.mul_apply, Real.log_mul (hc i).ne' (hv i).ne',
    Real.log_mul (hc i).ne' (hv₀ i).ne']
  ring

/-- Cancelling the centered Gaussian density preserves optimization over
the entire probability-measure space, as well as the fitted moment fiber. -/
theorem gaussian_probability_optimizer_iff_score_fiber {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} [Nonempty (Fin n)] (x : Fin n → Point d)
    (θ : Θ → Point d) (hθ : Continuous θ) (w v : Fin n → ℝ)
    (hw : w ∈ positiveVectors n)
    (hvmax : IsMaxOn (convexHull ℝ (range (fun a ↦ gaussianScoreFeature x (θ a))))
      (weightedLogLikelihood w) v) (μ : ProbabilityMeasure Θ) :
    IsMaxOn univ (fun ν : ProbabilityMeasure Θ ↦ weightedLogLikelihood w
      (probabilityMixtureValue (fun a i ↦ gaussianKernel d (x i) (θ a)) ν)) μ ↔
      μ ∈ probabilityMixtureFiber (fun a ↦ gaussianScoreFeature x (θ a)) v := by
  let A := fun a ↦ gaussianScoreFeature x (θ a)
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hb := positive_kernel_hull_properties A hA (fun _ _ ↦ Real.exp_pos _)
  have hvalpos (ν : ProbabilityMeasure Θ) : ∀ i, 0 < probabilityMixtureValue A ν i :=
    hb.2.2 (probabilityMixtureValue_mem_convexHull A hA ν)
  have heq (ν : ProbabilityMeasure Θ) :
      weightedLogLikelihood w
        (probabilityMixtureValue (fun a i ↦ gaussianKernel d (x i) (θ a)) ν) =
      weightedLogLikelihood w (fun i ↦ gaussianDensity d (x i)) +
        weightedLogLikelihood w (probabilityMixtureValue A ν) := by
    have hkernel : (fun a i ↦ gaussianKernel d (x i) (θ a)) =
        (fun a i ↦ gaussianDensity d (x i) * A a i) := by
      funext a i
      exact gaussianKernel_eq_density_mul_exp_score (x i) (θ a)
    rw [hkernel, probabilityMixtureValue_coordinate_scale]
    exact weightedLogLikelihood_mul_positive _ _ _ (fun i ↦ gaussianDensity_pos d (x i))
      (hvalpos ν)
  rw [← probability_optimizer_iff_mem_fiber A hA rfl hb.2.2 w v hw hvmax μ]
  constructor <;> intro h <;> refine ⟨mem_univ μ, ?_⟩ <;> intro ν _
  · have hh := h.2 ν (mem_univ ν)
    dsimp only at hh ⊢
    rw [heq ν, heq μ] at hh
    linarith
  · dsimp only
    rw [heq ν, heq μ]
    have hh := h.2 ν (mem_univ ν)
    dsimp only at hh
    linarith

noncomputable def gaussianPaperSupportConstant (d : ℕ) (C b : ℝ) : ℝ :=
  10000000 * (1 + (4 * C + 1) ^ d + (b + 4))

/-- Conditional structural parts of the main theorem at
`alpha = (r_n + log n) log n`. There is one Borel conull data set; on the
radius event the weight event has polynomial failure. Every optimizer is
the unique finite law, and the bounds hold against every ordinary NPMLE. -/
theorem gaussian_exact_regularization_conditional_balanced {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b)
    (θ : Θ → Point d) (hθ : Continuous θ) (hθinj : Function.Injective θ)
    (hθbound : ∀ a, ‖θ a‖ ≤ S) :
    ∀ᶠ n : ℕ in atTop,
      ∃ X : Set (Fin n → Point d), MeasurableSet X ∧ volume Xᶜ = 0 ∧
      ∀ x ∈ X, (∀ i, ‖x i‖ ≤ gaussianPaperSampleRadius d S b n) →
      ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
        (gammaProductMeasure n (gaussianPaperBalancedShape d n)
          (gaussianPaperBalancedShape d n)).real Gᶜ ≤ 3 * (n : ℝ) ^ (-(b + 2)) ∧
      ∀ w ∈ G,
        (∀ i, |w i - 1| ≤ (2 * Real.sqrt (b + 4)) /
          Real.sqrt (gaussianPaperAugmentedDimension d n)) ∧
        w ∈ positiveVectors n ∧
        ∃ μ : ProbabilityMeasure Θ,
          {ν : ProbabilityMeasure Θ | IsMaxOn univ (fun ρ : ProbabilityMeasure Θ ↦
            weightedLogLikelihood w
              (probabilityMixtureValue (fun a i ↦ gaussianKernel d (x i) (θ a)) ρ)) ν} = {μ} ∧
          (μ : Measure Θ).support.Finite ∧
          ((μ : Measure Θ).support.ncard : ℝ) ≤
            gaussianPaperSupportConstant d 40 b * gaussianPaperAugmentedDimension d n ∧
          ∀ μ₀ : ProbabilityMeasure Θ,
            IsMaxOn univ (fun ρ : ProbabilityMeasure Θ ↦ weightedLogLikelihood 1
              (probabilityMixtureValue (fun a i ↦ gaussianKernel d (x i) (θ a)) ρ)) μ₀ →
            let f₀ := probabilityMixtureValue (fun a i ↦ gaussianKernel d (x i) (θ a)) μ₀
            let f := probabilityMixtureValue (fun a i ↦ gaussianKernel d (x i) (θ a)) μ
            0 ≤ weightedLogLikelihood 1 f₀ - weightedLogLikelihood 1 f ∧
            weightedLogLikelihood 1 f₀ - weightedLogLikelihood 1 f ≤
              gaussianPaperSupportConstant d 40 b / Real.log n ∧
            (∑ i, (Real.log (f i / f₀ i)) ^ 2) ≤
              gaussianPaperSupportConstant d 40 b / Real.log n := by
  let B := gaussianPaperSupportConstant d 40 b
  have hB : 0 ≤ B := by dsimp [B, gaussianPaperSupportConstant]; positivity
  filter_upwards [eventually_gaussianPaperBalanced_conditions d hS hb,
    eventually_gaussianPaper_sparse_uniqueness_threshold d hB,
    eventually_gaussianPaper_rank_tail_le d (show (0 : ℝ) < 40 by norm_num) hb,
    eventually_gaussianPaperBalanced_likelihood_bound d (show (0 : ℝ) < 40 by norm_num) hb,
    eventually_gaussianPaperBalanced_weight_bound d hb,
    eventually_ge_atTop (1 : ℕ)] with n hc hsize hrank hlossbound hweight hn
  letI : NeZero n := ⟨by omega⟩
  obtain ⟨X, hX, hnull, hgeneric⟩ := gaussian_generic_evaluation_independence n d
  refine ⟨X, hX, hnull, ?_⟩
  intro x hx hxradius
  have hT : 0 ≤ gaussianPaperSampleRadius d S b n := by
    dsimp [gaussianPaperSampleRadius]
    positivity
  obtain ⟨G, hG, hGprob, hgood⟩ := gaussian_effective_dimension_full_support
    (gaussianPaperMomentOrder 40 n) hc.1 hT hS x hxradius θ hθ hθbound hc.2.2.1 hc.2.2.2
  let A := fun a ↦ gaussianScoreFeature x (θ a)
  let K := fun a i ↦ gaussianKernel d (x i) (θ a)
  let c := fun i ↦ gaussianDensity d (x i)
  let vhat := gaussianCanonicalFit x θ hθ
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hprops := positive_kernel_hull_properties A hA (fun _ _ ↦ Real.exp_pos _)
  have hfit (w : Fin n → ℝ) : IsMaxOn (convexHull ℝ (range A))
      (weightedLogLikelihood w) (vhat w) := gaussianCanonicalFit_isMax x θ hθ w
  have hfitpos (w : Fin n → ℝ) : ∀ i, 0 < vhat w i := hprops.2.2 (hfit w).1
  have hsmallreal : 10000000 * ((gaussianPaperStructuralRank d 40 n : ℝ) +
      gaussianPaperStructuralTail b n) ≤ B * gaussianPaperAugmentedDimension d n := by
    calc
      _ ≤ 10000000 * ((1 + (4 * 40 + 1) ^ d + (b + 4)) *
          gaussianPaperAugmentedDimension d n) := mul_le_mul_of_nonneg_left hrank (by norm_num)
      _ = _ := by dsimp [B, gaussianPaperSupportConstant]; ring
  have heqK : K = (fun a i ↦ c i * A a i) := by
    funext a i
    exact gaussianKernel_eq_density_mul_exp_score (x i) (θ a)
  refine ⟨G, hG, ?_, ?_⟩
  · rw [← gaussianPaperStructural_failure_bound (by omega : 0 < n) b]
    exact hGprob
  · intro w hw
    obtain ⟨hcoord, hwpos, _, hall, hnonneg, hloss, hlog, _⟩ := hgood w hw
    change 0 ≤ weightedLogLikelihood 1 (vhat 1) - weightedLogLikelihood 1 (vhat w) at hnonneg
    change weightedLogLikelihood 1 (vhat 1) - weightedLogLikelihood 1 (vhat w) ≤
      10000000 * ((gaussianPaperStructuralRank d 40 n : ℝ) + gaussianPaperStructuralTail b n) /
        gaussianPaperBalancedShape d n at hloss
    change (∑ i, (fittedLogRatio (vhat 1) (vhat w) i) ^ 2) ≤
      10000000 * ((gaussianPaperStructuralRank d 40 n : ℝ) + gaussianPaperStructuralTail b n) /
        gaussianPaperBalancedShape d n at hlog
    change 10000000 * ((gaussianPaperStructuralRank d 40 n : ℝ) + gaussianPaperStructuralTail b n) /
      gaussianPaperBalancedShape d n ≤ B / Real.log n at hlossbound
    refine ⟨fun i ↦ (hcoord i).trans hweight, hwpos, ?_⟩
    have hsmall : ∀ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A (vhat w) μ →
        (μ : Measure Θ).support.ncard ≤ Nat.ceil (B * gaussianPaperAugmentedDimension d n) := by
      intro μ hμ
      have hh := ((hall μ hμ).2.trans hsmallreal).trans (Nat.le_ceil _)
      exact_mod_cast hh
    obtain ⟨μ, hfiber, hext, hfinite, _⟩ :=
      gaussian_optimizer_fiber_unique_of_evaluation_independence x θ hθ hθinj w (vhat w)
        hwpos (hfit w) hsize (hgeneric x hx) hsmall
    have hfiberscore : probabilityMixtureFiber A (vhat w) = {μ} := by
      rw [← gaussian_probability_optimizer_fiber_eq_score x θ (vhat w)]
      exact hfiber
    have hμscore : μ ∈ probabilityMixtureFiber A (vhat w) := by
      rw [hfiberscore]
      exact mem_singleton μ
    have hμext : IsExtremeProbabilityMixture A (vhat w) μ := by
      have hext' : IsExtremeProbabilityMixture K (c * vhat w) μ := hext
      rw [heqK] at hext'
      exact (isExtremeProbabilityMixture_coordinate_scale A c (vhat w)
        (fun i ↦ (gaussianDensity_pos d (x i)).ne') μ).mp hext'
    refine ⟨μ, ?_, hfinite, (hall μ hμext).2.trans hsmallreal, ?_⟩
    · ext ν
      exact (gaussian_probability_optimizer_iff_score_fiber x θ hθ w (vhat w)
        hwpos (hfit w) ν).trans (by rw [hfiberscore])
    · intro μ₀ hμ₀
      have hμ₀score := (gaussian_probability_optimizer_iff_score_fiber x θ hθ 1 (vhat 1)
        (fun _ ↦ by norm_num) (hfit 1) μ₀).mp hμ₀
      have hf : probabilityMixtureValue K μ = c * vhat w := by
        rw [heqK, probabilityMixtureValue_coordinate_scale, show probabilityMixtureValue A μ =
          vhat w from hμscore]
      have hf₀ : probabilityMixtureValue K μ₀ = c * vhat 1 := by
        rw [heqK, probabilityMixtureValue_coordinate_scale, show probabilityMixtureValue A μ₀ =
          vhat 1 from hμ₀score]
      dsimp only
      change 0 ≤ weightedLogLikelihood 1 (probabilityMixtureValue K μ₀) -
        weightedLogLikelihood 1 (probabilityMixtureValue K μ) ∧ _
      rw [hf₀, hf,
        weightedLogLikelihood_mul_positive _ _ _ (fun i ↦ gaussianDensity_pos d (x i)) (hfitpos 1),
        weightedLogLikelihood_mul_positive _ _ _ (fun i ↦ gaussianDensity_pos d (x i)) (hfitpos w)]
      have hlogeq : (fun i ↦ Real.log ((c * vhat w) i / (c * vhat 1) i)) =
          fittedLogRatio (vhat 1) (vhat w) := by
        funext i
        change Real.log (gaussianDensity d (x i) * vhat w i /
          (gaussianDensity d (x i) * vhat 1 i)) = fittedLogRatio (vhat 1) (vhat w) i
        rw [Real.log_div (mul_pos (gaussianDensity_pos d (x i)) (hfitpos w i)).ne'
          (mul_pos (gaussianDensity_pos d (x i)) (hfitpos 1 i)).ne']
        exact congrFun (fittedLogRatio_mul_positive c (vhat 1) (vhat w)
          (fun i ↦ gaussianDensity_pos d (x i)) (hfitpos 1) (hfitpos w)) i
      have hsum : (∑ i, (Real.log ((c * vhat w) i / (c * vhat 1) i)) ^ 2) =
          ∑ i, (fittedLogRatio (vhat 1) (vhat w) i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [congrFun hlogeq i]
      refine ⟨by linarith, by linarith [hloss.trans hlossbound], ?_⟩
      rw [hsum]
      exact hlog.trans hlossbound

/-- Conditional arbitrarily-small-perturbation corollary. The unique law is
also an ordinary near-MLE with total error one, simultaneously against every
comparison law, which is the input required for the uniform risk theorem. -/
theorem gaussian_exact_regularization_conditional_tiny {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (d : ℕ) {S b L : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) (hL : 0 < L)
    (θ : Θ → Point d) (hθ : Continuous θ) (hθinj : Function.Injective θ)
    (hθbound : ∀ a, ‖θ a‖ ≤ S) :
    ∀ᶠ n : ℕ in atTop,
      ∃ X : Set (Fin n → Point d), MeasurableSet X ∧ volume Xᶜ = 0 ∧
      ∀ x ∈ X, (∀ i, ‖x i‖ ≤ gaussianPaperSampleRadius d S b n) →
      ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
        (gammaProductMeasure n ((n : ℝ) ^ (2 * L + 2))
          ((n : ℝ) ^ (2 * L + 2))).real Gᶜ ≤ 3 * (n : ℝ) ^ (-(b + 2)) ∧
      ∀ w ∈ G,
        (∀ i, |w i - 1| ≤ (n : ℝ) ^ (-L)) ∧ w ∈ positiveVectors n ∧
        ∃ μ : ProbabilityMeasure Θ,
          {ν : ProbabilityMeasure Θ | IsMaxOn univ (fun ρ : ProbabilityMeasure Θ ↦
            weightedLogLikelihood w
              (probabilityMixtureValue (fun a i ↦ gaussianKernel d (x i) (θ a)) ρ)) ν} = {μ} ∧
          (μ : Measure Θ).support.Finite ∧
          ((μ : Measure Θ).support.ncard : ℝ) ≤
            gaussianPaperSupportConstant d (8 * (2 * L + 6)) b *
              gaussianPaperAugmentedDimension d n ∧
          ∀ ν : ProbabilityMeasure Θ,
            weightedLogLikelihood 1
              (probabilityMixtureValue (fun a i ↦ gaussianKernel d (x i) (θ a)) ν) - 1 ≤
            weightedLogLikelihood 1
              (probabilityMixtureValue (fun a i ↦ gaussianKernel d (x i) (θ a)) μ) := by
  let C := 8 * (2 * L + 6)
  let B := gaussianPaperSupportConstant d C b
  have hC : 0 < C := by dsimp [C]; linarith
  have hB : 0 ≤ B := by dsimp [B, gaussianPaperSupportConstant]; positivity
  have hsmall := (isLittleO_gaussianPaperAugmentedDimension_rpow d
    (show 0 < 2 * L + 2 by linarith)).const_mul_left B
  filter_upwards [eventually_gaussianPaperTiny_conditions d hS hb hL,
    eventually_gaussianPaper_sparse_uniqueness_threshold d hB,
    eventually_gaussianPaper_rank_tail_le d hC hb,
    eventually_gaussianPaperTiny_weight_bound hb hL,
    hsmall.bound zero_lt_one, eventually_gaussianPaperAugmentedDimension_pos d,
    eventually_ge_atTop (1 : ℕ)] with n hc hsize hrank hweight hbound hd hn
  letI : NeZero n := ⟨by omega⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbound' : B * gaussianPaperAugmentedDimension d n ≤ (n : ℝ) ^ (2 * L + 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hB hd.le),
      abs_of_nonneg (Real.rpow_nonneg hn0.le _), one_mul] using hbound
  obtain ⟨X, hX, hnull, hgeneric⟩ := gaussian_generic_evaluation_independence n d
  refine ⟨X, hX, hnull, ?_⟩
  intro x hx hxradius
  have hT : 0 ≤ gaussianPaperSampleRadius d S b n := by
    dsimp [gaussianPaperSampleRadius]
    positivity
  obtain ⟨G, hG, hGprob, hgood⟩ := gaussian_effective_dimension_full_support
    (gaussianPaperMomentOrder C n) hc.1 hT hS x hxradius θ hθ hθbound hc.2.1 hc.2.2
  let A := fun a ↦ gaussianScoreFeature x (θ a)
  let K := fun a i ↦ gaussianKernel d (x i) (θ a)
  let c := fun i ↦ gaussianDensity d (x i)
  let vhat := gaussianCanonicalFit x θ hθ
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hprops := positive_kernel_hull_properties A hA (fun _ _ ↦ Real.exp_pos _)
  have hfit (w : Fin n → ℝ) : IsMaxOn (convexHull ℝ (range A))
      (weightedLogLikelihood w) (vhat w) := gaussianCanonicalFit_isMax x θ hθ w
  have hfitpos (w : Fin n → ℝ) : ∀ i, 0 < vhat w i := hprops.2.2 (hfit w).1
  have hsmallreal : 10000000 * ((gaussianPaperStructuralRank d C n : ℝ) +
      gaussianPaperStructuralTail b n) ≤ B * gaussianPaperAugmentedDimension d n := by
    calc
      _ ≤ 10000000 * ((1 + (4 * C + 1) ^ d + (b + 4)) *
          gaussianPaperAugmentedDimension d n) := mul_le_mul_of_nonneg_left hrank (by norm_num)
      _ = _ := by dsimp [B, gaussianPaperSupportConstant]; ring
  have heqK : K = (fun a i ↦ c i * A a i) := by
    funext a i
    exact gaussianKernel_eq_density_mul_exp_score (x i) (θ a)
  refine ⟨G, hG, ?_, ?_⟩
  · rw [← gaussianPaperStructural_failure_bound (by omega : 0 < n) b]
    exact hGprob
  · intro w hw
    obtain ⟨hcoord, hwpos, _, hall, _, hloss, _, _⟩ := hgood w hw
    change weightedLogLikelihood 1 (vhat 1) - weightedLogLikelihood 1 (vhat w) ≤
      10000000 * ((gaussianPaperStructuralRank d C n : ℝ) + gaussianPaperStructuralTail b n) /
        (n : ℝ) ^ (2 * L + 2) at hloss
    have hsmall : ∀ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A (vhat w) μ →
        (μ : Measure Θ).support.ncard ≤ Nat.ceil (B * gaussianPaperAugmentedDimension d n) := by
      intro μ hμ
      have hh := ((hall μ hμ).2.trans hsmallreal).trans (Nat.le_ceil _)
      exact_mod_cast hh
    obtain ⟨μ, hfiber, hext, hfinite, _⟩ :=
      gaussian_optimizer_fiber_unique_of_evaluation_independence x θ hθ hθinj w (vhat w)
        hwpos (hfit w) hsize (hgeneric x hx) hsmall
    have hfiberscore : probabilityMixtureFiber A (vhat w) = {μ} := by
      rw [← gaussian_probability_optimizer_fiber_eq_score x θ (vhat w)]
      exact hfiber
    have hμscore : μ ∈ probabilityMixtureFiber A (vhat w) := by
      rw [hfiberscore]
      exact mem_singleton μ
    have hμext : IsExtremeProbabilityMixture A (vhat w) μ := by
      have hext' : IsExtremeProbabilityMixture K (c * vhat w) μ := hext
      rw [heqK] at hext'
      exact (isExtremeProbabilityMixture_coordinate_scale A c (vhat w)
        (fun i ↦ (gaussianDensity_pos d (x i)).ne') μ).mp hext'
    refine ⟨fun i ↦ (hcoord i).trans hweight, hwpos,
      μ, ?_, hfinite, (hall μ hμext).2.trans hsmallreal, ?_⟩
    · ext ν
      exact (gaussian_probability_optimizer_iff_score_fiber x θ hθ w (vhat w)
        hwpos (hfit w) ν).trans (by rw [hfiberscore])
    · intro ν
      have hνhull := probabilityMixtureValue_mem_convexHull A hA ν
      have hνpos : ∀ i, 0 < probabilityMixtureValue A ν i := hprops.2.2 hνhull
      have hνmax := (hfit 1).2 _ hνhull
      have hloss1 : weightedLogLikelihood 1 (vhat 1) - weightedLogLikelihood 1 (vhat w) ≤ 1 := by
        have hr : 10000000 * ((gaussianPaperStructuralRank d C n : ℝ) +
            gaussianPaperStructuralTail b n) / (n : ℝ) ^ (2 * L + 2) ≤ 1 := by
          apply (div_le_one (Real.rpow_pos_of_pos hn0 _)).mpr
          exact hsmallreal.trans hbound'
        exact hloss.trans hr
      change weightedLogLikelihood 1 (probabilityMixtureValue K ν) - 1 ≤
        weightedLogLikelihood 1 (probabilityMixtureValue K μ)
      rw [heqK, probabilityMixtureValue_coordinate_scale, probabilityMixtureValue_coordinate_scale,
        show probabilityMixtureValue A μ = vhat w from hμscore,
        weightedLogLikelihood_mul_positive _ _ _ (fun i ↦ gaussianDensity_pos d (x i)) hνpos,
        weightedLogLikelihood_mul_positive _ _ _ (fun i ↦ gaussianDensity_pos d (x i)) (hfitpos w)]
      linarith

end ReweightedNPMLE
