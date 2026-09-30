import ReweightedNPMLE.FullEffectiveDimension
import ReweightedNPMLE.SupportUniqueness
import ReweightedNPMLE.GaussianWidth
import ReweightedNPMLE.FittedGeometry
import Mathlib.Tactic

/-!
# Gaussian dictionary links for full-measure structural bounds

The canceled Gaussian score dictionary has the same optimizer fibers as the
Gaussian density dictionary. Its relative fitted hull is the convex hull of
the relative atoms used in the verified Taylor-width estimate.
-/

open Set MeasureTheory
open scoped BigOperators Topology

namespace ReweightedNPMLE

theorem relative_gaussian_fitted_mem_convexHull {d n : ℕ}
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (K : Set (Point d))
    {v : Fin n → ℝ} (hv : v ∈ gaussianFittedSet x K) :
    WithLp.toLp 2 (relativeFittedVector v₀ v) ∈
      convexHull ℝ (relativeGaussianAtom x v₀ '' K) := by
  classical
  obtain ⟨ι, hι, p, θ, hp, hpsum, hθ, hval⟩ :=
    (mem_gaussianFittedSet_iff_exists_finite_mixture x K v).mp hv
  letI : Fintype ι := hι
  refine mem_convexHull_of_exists_fintype p (fun j ↦ relativeGaussianAtom x v₀ (θ j))
    hp hpsum (fun j ↦ ⟨θ j, hθ j, rfl⟩) ?_
  apply WithLp.ofLp_injective 2
  funext i
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, relativeGaussianAtom, relativeFittedVector]
  have hi := congrFun hval i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, gaussianScoreFeature] at hi
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [hpsum, ← hi, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem gaussian_relativeFittedSet_width {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (K : Set (Point d))
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ∀ i, ‖x i‖ ≤ T) (hK : ∀ θ ∈ K, ‖θ‖ ≤ S)
    (hv₀ : v₀ ∈ gaussianFittedSet x K) :
    ∀ u ∈ relativeFittedSet (gaussianFittedSet x K) v₀,
      ‖WithLp.toLp 2 u - (gaussianTaylorSubspace L x v₀).starProjection (WithLp.toLp 2 u)‖ ≤
        Real.sqrt n * (Real.exp (2 * T * S + S ^ 2 / 2) *
          (T * S) ^ (L + 1) / (L + 1).factorial) := by
  rintro u ⟨v, hv, rfl⟩
  exact gaussian_convexHull_projection_error L x v₀ K hT hS hx hK
    (gaussianFittedSet_lower_bound x K hT hS hx hK hv₀)
    (relative_gaussian_fitted_mem_convexHull x v₀ K hv)

theorem probabilityMixtureValue_coordinate_scale {Θ : Type*}
    [MeasurableSpace Θ] {n : ℕ} (A : Θ → Fin n → ℝ)
    (c : Fin n → ℝ) (μ : ProbabilityMeasure Θ) :
    probabilityMixtureValue (fun θ i ↦ c i * A θ i) μ = c * probabilityMixtureValue A μ := by
  funext i
  exact integral_const_mul (c i) (fun θ ↦ A θ i)

theorem probabilityMixtureFiber_coordinate_scale {Θ : Type*}
    [MeasurableSpace Θ] {n : ℕ} (A : Θ → Fin n → ℝ)
    (c v : Fin n → ℝ) (hc : ∀ i, c i ≠ 0) :
    probabilityMixtureFiber (fun θ i ↦ c i * A θ i) (c * v) = probabilityMixtureFiber A v := by
  ext μ
  change probabilityMixtureValue (fun θ i ↦ c i * A θ i) μ = c * v ↔
    probabilityMixtureValue A μ = v
  rw [probabilityMixtureValue_coordinate_scale]
  constructor
  · intro h
    funext i
    exact mul_left_cancel₀ (hc i) (congrFun h i)
  · intro h
    rw [h]

theorem isExtremeProbabilityMixture_coordinate_scale {Θ : Type*}
    [TopologicalSpace Θ] [MeasurableSpace Θ] {n : ℕ}
    (A : Θ → Fin n → ℝ) (c v : Fin n → ℝ) (hc : ∀ i, c i ≠ 0)
    (μ : ProbabilityMeasure Θ) :
    IsExtremeProbabilityMixture (fun θ i ↦ c i * A θ i) (c * v) μ ↔
      IsExtremeProbabilityMixture A v μ := by
  unfold IsExtremeProbabilityMixture probabilityFiberImage
  rw [probabilityMixtureFiber_coordinate_scale A c v hc]

theorem gaussian_probability_optimizer_fiber_eq_score {Θ : Type*}
    [MeasurableSpace Θ] {d n : ℕ} (x : Fin n → Point d)
    (θ : Θ → Point d) (v : Fin n → ℝ) :
    probabilityMixtureFiber (fun a i ↦ gaussianKernel d (x i) (θ a))
      ((fun i ↦ gaussianDensity d (x i)) * v) =
        probabilityMixtureFiber (fun a ↦ gaussianScoreFeature x (θ a)) v := by
  have heq : (fun a i ↦ gaussianKernel d (x i) (θ a)) =
      (fun a i ↦ gaussianDensity d (x i) * gaussianScoreFeature x (θ a) i) := by
    funext a i
    exact gaussianKernel_eq_density_mul_exp_score (x i) (θ a)
  rw [heq]
  exact probabilityMixtureFiber_coordinate_scale _ _ _
    (fun i ↦ (gaussianDensity_pos d (x i)).ne')

noncomputable def gaussianTaylorResidual (n : ℕ) (T S : ℝ) (L : ℕ) : ℝ :=
  Real.sqrt n * (Real.exp (2 * T * S + S ^ 2 / 2) *
    (T * S) ^ (L + 1) / (L + 1).factorial)

/-- Finite-sample conditional Gaussian structural bounds with the explicit
Taylor rank and remainder. No assumption about sampling or model correctness
is used. The later polylogarithmic specialization only has to choose `L` and
verify the two displayed scale conditions. -/
theorem gaussian_effective_dimension_full_support {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ]
    [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} [Nonempty (Fin n)] (L : ℕ) {α q T S : ℝ}
    (hq : 1 ≤ q) (hT : 0 ≤ T) (hS : 0 ≤ S)
    (x : Fin n → Point d) (hx : ∀ i, ‖x i‖ ≤ T)
    (θ : Θ → Point d) (hθ : Continuous θ) (hθbound : ∀ a, ‖θ a‖ ≤ S)
    (hscale : 10000000 * (((1 + (L + d).choose d : ℕ) : ℝ) + effectiveQ n q) ≤ α)
    (hwidthScale : gaussianTaylorResidual n T S L *
      Real.sqrt (α * (n : ℝ) * effectiveQ n q) ≤ 1) :
    let A := fun a : Θ ↦ gaussianScoreFeature x (θ a)
    let C := convexHull ℝ (range A)
    let vhat := fittedValueSelection C
      (positive_kernel_hull_properties A ((continuous_gaussianScoreFeature x).comp hθ)
        (fun _ _ ↦ Real.exp_pos _)).1
      (positive_kernel_hull_properties A ((continuous_gaussianScoreFeature x).comp hθ)
        (fun _ _ ↦ Real.exp_pos _)).2.1
      (positive_kernel_hull_properties A ((continuous_gaussianScoreFeature x).comp hθ)
        (fun _ _ ↦ Real.exp_pos _)).2.2
    let v₀ := vhat 1
    ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
      (gammaProductMeasure n α α).real Gᶜ ≤ 3 * Real.exp (-q) ∧
      ∀ w ∈ G, (∀ i, |w i - 1| ≤ 2 * Real.sqrt (effectiveQ n q / α)) ∧
        w ∈ positiveVectors n ∧
        (maximumExtremeSupport A vhat w : ℝ) ≤
          10000000 * (((1 + (L + d).choose d : ℕ) : ℝ) + q) ∧
        (∀ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A (vhat w) μ →
          (μ : Measure Θ).support.Finite ∧ ((μ : Measure Θ).support.ncard : ℝ) ≤
            10000000 * (((1 + (L + d).choose d : ℕ) : ℝ) + q)) ∧
        0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 (vhat w) ∧
        weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 (vhat w) ≤
          10000000 * (((1 + (L + d).choose d : ℕ) : ℝ) + q) / α ∧
        (∑ i, (fittedLogRatio v₀ (vhat w) i) ^ 2) ≤
          10000000 * (((1 + (L + d).choose d : ℕ) : ℝ) + q) / α ∧
        ∀ τ : ℝ, 0 ≤ τ → τ < 1 / 3072 → ∀ v ∈ C,
          weightedLogLikelihood w (vhat w) - τ ≤ weightedLogLikelihood w v →
          0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ∧
          weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ≤
            10000000 * ((((1 + (L + d).choose d : ℕ) : ℝ) + q) / α + τ) ∧
          (∑ i, (fittedLogRatio v₀ v i) ^ 2) ≤
            10000000 * ((((1 + (L + d).choose d : ℕ) : ℝ) + q) / α + τ) := by
  dsimp only
  let A := fun a : Θ ↦ gaussianScoreFeature x (θ a)
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hApos : ∀ a i, 0 < A a i := fun a i ↦ Real.exp_pos _
  let C := convexHull ℝ (range A)
  let hb := positive_kernel_hull_properties A hA hApos
  let vhat := fittedValueSelection C hb.1 hb.2.1 hb.2.2
  have hCeq : C = gaussianFittedSet x (range θ) := by
    unfold C gaussianFittedSet
    congr 1
    ext a
    simp only [mem_range, mem_image, A]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨θ b, ⟨b, rfl⟩, rfl⟩
    · rintro ⟨b, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
  have hwidth : ∀ u ∈ relativeFittedSet C (vhat 1),
      ‖WithLp.toLp 2 u - (gaussianTaylorSubspace L x (vhat 1)).starProjection
        (WithLp.toLp 2 u)‖ ≤ gaussianTaylorResidual n T S L := by
    have hv₀ : vhat 1 ∈ gaussianFittedSet x (range θ) :=
      hCeq ▸ (fittedValueSelection_isMax C hb.1 hb.2.1 hb.2.2 1).1
    intro u hu
    rw [hCeq] at hu
    exact gaussian_relativeFittedSet_width L x (vhat 1) (range θ) hT hS hx
      (fun b hb ↦ by rcases hb with ⟨a, rfl⟩; exact hθbound a) hv₀ u hu
  have hη : 0 ≤ gaussianTaylorResidual n T S L := by
    unfold gaussianTaylorResidual
    positivity
  obtain ⟨hstat, G, hGmeas, hGprob, hG⟩ := effective_dimension_full_support hq hη hscale
    hwidthScale A hA hApos (gaussianTaylorSubspace L x (vhat 1))
    (finrank_gaussianTaylorSubspace_le L x (vhat 1)) hwidth
  refine ⟨G, hGmeas, hGprob, ?_⟩
  intro w hw
  obtain ⟨hcoord, hwpos, hs, hattain, hall, hnonneg, hloss, hlog, hnear⟩ := hG w hw
  exact ⟨hcoord, hwpos, hs, hall, hnonneg, hloss, hlog, hnear⟩

/-- The Gaussian uniqueness consequence of simultaneous evaluation
independence. The independence assumption has exactly the paper's threshold,
and includes data-dependent atom locations. Its almost-everywhere validity is
the separate analytic incidence theorem, not an assumption hidden here. -/
theorem gaussian_optimizer_fiber_unique_of_evaluation_independence {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n m : ℕ} [Nonempty (Fin n)] (x : Fin n → Point d)
    (θ : Θ → Point d) (hθ : Continuous θ) (hθinj : Function.Injective θ)
    (w v : Fin n → ℝ) (hw : w ∈ positiveVectors n)
    (hvmax : IsMaxOn (convexHull ℝ (range (fun a ↦ gaussianScoreFeature x (θ a))))
      (weightedLogLikelihood w) v)
    (hsize : (2 * m) * (d + 1) ≤ n)
    (hgeneric : ∀ k : ℕ, k * (d + 1) ≤ n → ∀ t : Fin k → Point d,
      Function.Injective t → LinearIndependent ℝ (fun j i ↦ gaussianKernel d (x i) (t j)))
    (hsmall : ∀ μ : ProbabilityMeasure Θ,
      IsExtremeProbabilityMixture (fun a ↦ gaussianScoreFeature x (θ a)) v μ →
        (μ : Measure Θ).support.ncard ≤ m) :
    ∃ μ : ProbabilityMeasure Θ,
      probabilityMixtureFiber (fun a i ↦ gaussianKernel d (x i) (θ a))
        ((fun i ↦ gaussianDensity d (x i)) * v) = {μ} ∧
      IsExtremeProbabilityMixture (fun a i ↦ gaussianKernel d (x i) (θ a))
        ((fun i ↦ gaussianDensity d (x i)) * v) μ ∧
      (μ : Measure Θ).support.Finite ∧ (μ : Measure Θ).support.ncard ≤ m := by
  let A := fun a ↦ gaussianScoreFeature x (θ a)
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hCpos : convexHull ℝ (range A) ⊆ positiveVectors n :=
    convexHull_min (by rintro a ⟨b, rfl⟩; exact fun i ↦ Real.exp_pos _)
      (convex_positiveVectors n)
  have hind : ∀ k : ℕ, k ≤ 2 * m → ∀ t : Fin k → Θ,
      Function.Injective t → LinearIndependent ℝ (A ∘ t) := by
    intro k hk t ht
    have hkt : k * (d + 1) ≤ n := (Nat.mul_le_mul_right (d + 1) hk).trans hsize
    have hlin := hgeneric k hkt (θ ∘ t) (hθinj.comp ht)
    let S : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      { toFun := fun u i ↦ gaussianDensity d (x i) * u i
        map_add' := by intro u z; funext i; exact mul_add _ _ _
        map_smul' := by
          intro a u
          funext i
          change gaussianDensity d (x i) * (a * u i) = a * (gaussianDensity d (x i) * u i)
          ring }
    have heq : S ∘ (A ∘ t) = (fun j i ↦ gaussianKernel d (x i) (θ (t j))) := by
      funext j i
      exact (gaussianKernel_eq_density_mul_exp_score (x i) (θ (t j))).symm
    apply LinearIndependent.of_comp S
    rw [heq]
    exact hlin
  obtain ⟨μ, hfiber, hext, hfinite, hcard⟩ :=
    probabilityMixtureFiber_eq_singleton_of_small_extreme_supports A hA
      (convex_convexHull ℝ (range A)) hCpos (subset_convexHull ℝ _)
      w v hw hvmax hvmax.1 (L := 2 * m) le_rfl hind hsmall
  refine ⟨μ, ?_, ?_, hfinite, hcard⟩
  · rw [gaussian_probability_optimizer_fiber_eq_score]
    exact hfiber
  · have heq : (fun a i ↦ gaussianKernel d (x i) (θ a)) =
        (fun a i ↦ gaussianDensity d (x i) * A a i) := by
      funext a i
      exact gaussianKernel_eq_density_mul_exp_score (x i) (θ a)
    rw [heq]
    exact (isExtremeProbabilityMixture_coordinate_scale A _ v
      (fun i ↦ (gaussianDensity_pos d (x i)).ne') μ).mpr hext

end ReweightedNPMLE
