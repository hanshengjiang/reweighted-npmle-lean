import ReweightedNPMLE.GaussianApproxRegularization
import Mathlib.Tactic

/-! # Gaussian width with an arbitrary reference probability law -/

open Set MeasureTheory
open scoped Topology BigOperators

namespace ReweightedNPMLE

theorem gaussianScoreProbabilityValue_mem_fittedSet {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (x : Fin n → Point d) (θ : Θ → Point d) (hθ : Continuous θ)
    (μ : ProbabilityMeasure Θ) :
    probabilityMixtureValue (fun a ↦ gaussianScoreFeature x (θ a)) μ ∈
      gaussianFittedSet x (range θ) := by
  have heq : convexHull ℝ (range (fun a ↦ gaussianScoreFeature x (θ a))) =
      gaussianFittedSet x (range θ) := by
    unfold gaussianFittedSet
    congr 1
    ext v
    simp only [mem_range, mem_image]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨θ a, ⟨a, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
  rw [← heq]
  exact probabilityMixtureValue_mem_convexHull _ ((continuous_gaussianScoreFeature x).comp hθ) μ

/-- Proposition `prop:gaussian-width` over all probability mixing laws,
with an arbitrary reference law and the exact paper rank and remainder. -/
theorem gaussian_probability_relative_width_bound {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} (L : ℕ) (x : Fin n → Point d) (θ : Θ → Point d) (hθ : Continuous θ)
    (μ₀ : ProbabilityMeasure Θ) {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ∀ i, ‖x i‖ ≤ T) (hθbound : ∀ a, ‖θ a‖ ≤ S) :
    ∃ V : Submodule ℝ (EuclideanSpace ℝ (Fin n)),
      Module.finrank ℝ V ≤ 1 + (L + d).choose d ∧
      WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ)) ∈ V ∧
      ∀ μ : ProbabilityMeasure Θ,
        let u := WithLp.toLp 2 (fun i ↦
          gaussianMixture (μ : Measure Θ) θ (x i) /
            gaussianMixture (μ₀ : Measure Θ) θ (x i) - 1)
        ‖u - V.starProjection u‖ ≤ gaussianTaylorResidual n T S L := by
  let A := fun a ↦ gaussianScoreFeature x (θ a)
  let v₀ := probabilityMixtureValue A μ₀
  let V := gaussianTaylorSubspace L x v₀
  have hv₀ : v₀ ∈ gaussianFittedSet x (range θ) :=
    gaussianScoreProbabilityValue_mem_fittedSet x θ hθ μ₀
  have hrange : ∀ u ∈ range θ, ‖u‖ ≤ S := by
    rintro u ⟨a, rfl⟩
    exact hθbound a
  refine ⟨V, finrank_gaussianTaylorSubspace_le L x v₀,
    one_mem_gaussianTaylorSubspace L x v₀, ?_⟩
  intro μ
  let v := probabilityMixtureValue A μ
  have hv : v ∈ gaussianFittedSet x (range θ) :=
    gaussianScoreProbabilityValue_mem_fittedSet x θ hθ μ
  have hkernel : (fun a i ↦ gaussianKernel d (x i) (θ a)) =
      (fun a i ↦ gaussianDensity d (x i) * A a i) := by
    funext a i
    exact gaussianKernel_eq_density_mul_exp_score (x i) (θ a)
  have hrel : (fun i ↦ gaussianMixture (μ : Measure Θ) θ (x i) /
      gaussianMixture (μ₀ : Measure Θ) θ (x i) - 1) = relativeFittedVector v₀ v := by
    change (fun i ↦ probabilityMixtureValue (fun a j ↦ gaussianKernel d (x j) (θ a)) μ i /
      probabilityMixtureValue (fun a j ↦ gaussianKernel d (x j) (θ a)) μ₀ i - 1) = _
    rw [hkernel, probabilityMixtureValue_coordinate_scale, probabilityMixtureValue_coordinate_scale]
    funext i
    change (gaussianDensity d (x i) * v i) / (gaussianDensity d (x i) * v₀ i) - 1 = _
    rw [mul_div_mul_left _ _ (gaussianDensity_pos d (x i)).ne']
    rfl
  dsimp only
  rw [hrel]
  exact gaussian_relativeFittedSet_width L x v₀ (range θ) hT hS hx hrange hv₀
    _ ⟨v, hv, rfl⟩

theorem gaussianTaylorResidual_eq_zero_of_mul_eq_zero {n L : ℕ} {T S : ℝ}
    (hTS : T * S = 0) : gaussianTaylorResidual n T S L = 0 := by
  simp [gaussianTaylorResidual, hTS]

end ReweightedNPMLE
