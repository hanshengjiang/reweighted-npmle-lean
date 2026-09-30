import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import ReweightedNPMLE.Gaussian
import ReweightedNPMLE.Weights
import ReweightedNPMLE.CompactConvexHull
import Mathlib.Tactic

/-!
# Compact fitted-value geometry

The infinite-dimensional mixing-law optimization is reduced to the compact
convex hull of the continuous Gaussian evaluation dictionary.  The compact
convex-hull theorem shows this is the actual finite-mixture hull, not merely
its closure, and the Gaussian lower bound keeps it in the positive orthant.
-/

open Set

namespace ReweightedNPMLE

/-- In a finite-dimensional real normed space, the closed convex hull of a
compact continuous image is compact. -/
theorem isCompact_closedConvexHull_image
    {Θ E : Type*} [TopologicalSpace Θ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set Θ} (hK : IsCompact K) (f : Θ → E) (hf : Continuous f) :
    IsCompact (closedConvexHull ℝ (f '' K)) := by
  letI : ProperSpace E := FiniteDimensional.proper_rclike ℝ E
  rw [closedConvexHull_eq_closure_convexHull]
  exact (isBounded_convexHull.mpr (hK.image hf).isBounded).isCompact_closure

/-- Gaussian evaluation vector after cancellation of the common centered
Gaussian density. -/
noncomputable def gaussianScoreFeature {d n : ℕ}
    (x : Fin n → Point d) (θ : Point d) : Fin n → ℝ :=
  fun i ↦ Real.exp (gaussianScore (x i) θ)

theorem continuous_gaussianScoreFeature {d n : ℕ}
    (x : Fin n → Point d) : Continuous (gaussianScoreFeature x) := by
  apply continuous_pi
  intro i
  unfold gaussianScoreFeature gaussianScore
  fun_prop

/-- Compact convex Gaussian fitted-value class. -/
noncomputable def gaussianFittedSet {d n : ℕ}
    (x : Fin n → Point d) (K : Set (Point d)) : Set (Fin n → ℝ) :=
  convexHull ℝ (gaussianScoreFeature x '' K)

theorem isCompact_gaussianFittedSet {d n : ℕ}
    (x : Fin n → Point d) {K : Set (Point d)} (hK : IsCompact K) :
    IsCompact (gaussianFittedSet x K) := by
  exact isCompact_convexHull_of_isCompact
    (hK.image (continuous_gaussianScoreFeature x))

theorem convex_gaussianFittedSet {d n : ℕ}
    (x : Fin n → Point d) (K : Set (Point d)) :
    Convex ℝ (gaussianFittedSet x K) :=
  convex_convexHull ℝ _

theorem gaussianFittedSet_nonempty {d n : ℕ}
    (x : Fin n → Point d) {K : Set (Point d)} (hK : K.Nonempty) :
    (gaussianFittedSet x K).Nonempty := by
  obtain ⟨θ, hθ⟩ := hK
  exact ⟨gaussianScoreFeature x θ,
    subset_convexHull ℝ _ ⟨θ, hθ, rfl⟩⟩

/-- Membership in the fitted-value set is exactly representation by a finite
probability mixture of Gaussian dictionary atoms. -/
theorem mem_gaussianFittedSet_iff_exists_finite_mixture
    {d n : ℕ} (x : Fin n → Point d) (K : Set (Point d))
    (v : Fin n → ℝ) :
    v ∈ gaussianFittedSet x K ↔
      ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (θ : ι → Point d),
        (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ (∀ i, θ i ∈ K) ∧
          ∑ i, w i • gaussianScoreFeature x (θ i) = v := by
  constructor
  · intro hv
    obtain ⟨ι, hι, w, z, hw, hwsum, hz, hsum⟩ :=
      mem_convexHull_iff_exists_fintype.mp hv
    letI : Fintype ι := hι
    have hchoice : ∀ i, ∃ θ, θ ∈ K ∧ gaussianScoreFeature x θ = z i := by
      intro i
      rcases hz i with ⟨θ, hθ, hθz⟩
      exact ⟨θ, hθ, hθz⟩
    choose θ hθK hθz using hchoice
    refine ⟨ι, hι, w, θ, hw, hwsum, hθK, ?_⟩
    simpa only [hθz] using hsum
  · rintro ⟨ι, hι, w, θ, hw, hwsum, hθK, hsum⟩
    letI : Fintype ι := hι
    exact mem_convexHull_of_exists_fintype w
      (fun i ↦ gaussianScoreFeature x (θ i)) hw hwsum
      (fun i ↦ ⟨θ i, hθK i, rfl⟩) hsum

/-- Carathéodory form: a fitted vector has a representation using a fixed
number `finrank(ℝⁿ)+1 = n+1` of slots (zero masses pad shorter mixtures). -/
theorem exists_bounded_gaussian_finite_mixture
    {d n : ℕ} (x : Fin n → Point d) {K : Set (Point d)}
    (hK : K.Nonempty) {v : Fin n → ℝ} (hv : v ∈ gaussianFittedSet x K) :
    ∃ (w : Fin (Module.finrank ℝ (Fin n → ℝ) + 1) → ℝ)
      (θ : Fin (Module.finrank ℝ (Fin n → ℝ) + 1) → Point d),
      w ∈ stdSimplex ℝ (Fin (Module.finrank ℝ (Fin n → ℝ) + 1)) ∧
      (∀ i, θ i ∈ K) ∧
        ∑ i, w i • gaussianScoreFeature x (θ i) = v := by
  have himage : (gaussianScoreFeature x '' K).Nonempty := hK.image _
  obtain ⟨w, z, hw, hz, hsum⟩ :=
    exists_fixed_barycentric_representation himage hv
  have hchoice : ∀ i, ∃ θ, θ ∈ K ∧ gaussianScoreFeature x θ = z i := by
    intro i
    rcases hz i with ⟨θ, hθ, hθz⟩
    exact ⟨θ, hθ, hθz⟩
  choose θ hθK hθz using hchoice
  refine ⟨w, θ, hw, hθK, ?_⟩
  simpa only [hθz] using hsum

/-- On compact parameter sets, the paper's fitted hull agrees with its closed
convex hull while retaining exact finite-mixture representations. -/
theorem gaussianFittedSet_eq_closedConvexHull
    {d n : ℕ} (x : Fin n → Point d) {K : Set (Point d)}
    (hK : IsCompact K) :
    gaussianFittedSet x K =
      closedConvexHull ℝ (gaussianScoreFeature x '' K) := by
  exact convexHull_eq_closedConvexHull_of_isCompact
    (hK.image (continuous_gaussianScoreFeature x))

/-- The Gaussian score feature is integrable under every probability measure
supported almost surely on a compact parameter set. -/
theorem integrable_gaussianScoreFeature_of_ae_mem_compact
    {d n : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]
    (μ : MeasureTheory.Measure (Point d))
    [MeasureTheory.IsProbabilityMeasure μ]
    (x : Fin n → Point d) {K : Set (Point d)} (hKcompact : IsCompact K)
    (hμK : ∀ᵐ θ ∂μ, θ ∈ K) :
    MeasureTheory.Integrable (gaussianScoreFeature x) μ := by
  have hOn : MeasureTheory.IntegrableOn (gaussianScoreFeature x) K μ :=
    (continuous_gaussianScoreFeature x).continuousOn.integrableOn_compact hKcompact
  have hIndicator := hOn.integrable_indicator hKcompact.measurableSet
  apply hIndicator.congr
  filter_upwards [hμK] with θ hθ
  simp [Set.indicator_of_mem hθ]

/-- The fitted vector of any probability mixing law supported on `K` belongs
to the exact compact hull.  Integrability is explicit here and is automatic
for the bounded Gaussian dictionary on compact `K`. -/
theorem integral_gaussianScoreFeature_mem_gaussianFittedSet
    {Θ : Type*} [MeasurableSpace Θ] {d n : ℕ}
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (x : Fin n → Point d) (K : Set (Point d)) (θ : Θ → Point d)
    (hKcompact : IsCompact K) (hθK : ∀ᵐ a ∂μ, θ a ∈ K)
    (hint : MeasureTheory.Integrable (fun a ↦ gaussianScoreFeature x (θ a)) μ) :
    (∫ a, gaussianScoreFeature x (θ a) ∂μ) ∈ gaussianFittedSet x K := by
  apply (convex_gaussianFittedSet x K).integral_mem
    (isCompact_gaussianFittedSet x hKcompact).isClosed
  · filter_upwards [hθK] with a ha
    exact subset_convexHull ℝ _ ⟨θ a, ha, rfl⟩
  · exact hint

/-- Every probability-law fitted vector on a nonempty compact parameter set
has an exactly matching finite mixture. -/
theorem exists_finite_mixture_eq_gaussian_integral
    {Θ : Type*} [MeasurableSpace Θ] {d n : ℕ}
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (x : Fin n → Point d) (K : Set (Point d)) (θ : Θ → Point d)
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hθK : ∀ᵐ a ∂μ, θ a ∈ K)
    (hint : MeasureTheory.Integrable (fun a ↦ gaussianScoreFeature x (θ a)) μ) :
    ∃ (w : Fin (Module.finrank ℝ (Fin n → ℝ) + 1) → ℝ)
      (θ' : Fin (Module.finrank ℝ (Fin n → ℝ) + 1) → Point d),
      w ∈ stdSimplex ℝ (Fin (Module.finrank ℝ (Fin n → ℝ) + 1)) ∧
      (∀ i, θ' i ∈ K) ∧
        ∑ i, w i • gaussianScoreFeature x (θ' i) =
          ∫ a, gaussianScoreFeature x (θ a) ∂μ := by
  apply exists_bounded_gaussian_finite_mixture x hKnonempty
  exact integral_gaussianScoreFeature_mem_gaussianFittedSet
    μ x K θ hKcompact hθK hint

/-- Specialization to a Borel probability mixing measure on the parameter
space; compact support discharges integrability automatically. -/
theorem gaussianMixtureFittedValue_mem_gaussianFittedSet
    {d n : ℕ} [MeasurableSpace (Point d)] [BorelSpace (Point d)]
    (μ : MeasureTheory.Measure (Point d))
    [MeasureTheory.IsProbabilityMeasure μ]
    (x : Fin n → Point d) (K : Set (Point d))
    (hKcompact : IsCompact K) (hμK : ∀ᵐ θ ∂μ, θ ∈ K) :
    (∫ θ, gaussianScoreFeature x θ ∂μ) ∈ gaussianFittedSet x K := by
  exact integral_gaussianScoreFeature_mem_gaussianFittedSet μ x K id
    hKcompact hμK (integrable_gaussianScoreFeature_of_ae_mem_compact
      μ x hKcompact hμK)

/-- Every point of the closed fitted-value hull inherits the same coordinate
lower bound as the Gaussian dictionary. -/
theorem gaussianFittedSet_lower_bound {d n : ℕ}
    (x : Fin n → Point d) (K : Set (Point d))
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ∀ i, ‖x i‖ ≤ T) (hK : ∀ θ ∈ K, ‖θ‖ ≤ S)
    {v : Fin n → ℝ} (hv : v ∈ gaussianFittedSet x K) (i : Fin n) :
    Real.exp (-(T * S + S ^ 2 / 2)) ≤ v i := by
  let lower := Real.exp (-(T * S + S ^ 2 / 2))
  let H : Set (Fin n → ℝ) := {z | lower ≤ z i}
  have hdict : gaussianScoreFeature x '' K ⊆ H := by
    rintro _ ⟨θ, hθK, rfl⟩
    exact exp_neg_scoreBound_le_exp_score hT hS (hx i) (hK θ hθK)
  have hconv : Convex ℝ H := by
    intro a ha b hb p q hp hq hpq
    change lower ≤ (p • a + q • b) i
    change lower ≤ p * a i + q * b i
    calc
      lower = p * lower + q * lower := by rw [← add_mul, hpq, one_mul]
      _ ≤ p * a i + q * b i :=
        add_le_add (mul_le_mul_of_nonneg_left ha hp)
          (mul_le_mul_of_nonneg_left hb hq)
  exact convexHull_min hdict hconv hv

theorem gaussianFittedSet_subset_positiveVectors {d n : ℕ}
    (x : Fin n → Point d) (K : Set (Point d))
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ∀ i, ‖x i‖ ≤ T) (hK : ∀ θ ∈ K, ‖θ‖ ≤ S) :
    gaussianFittedSet x K ⊆ positiveVectors n := by
  intro v hv i
  exact (Real.exp_pos (-(T * S + S ^ 2 / 2))).trans_le
    (gaussianFittedSet_lower_bound x K hT hS hx hK hv i)

/-- Positive weights therefore have a unique fitted-value maximizer over the
compact Gaussian mixture class. -/
theorem exists_unique_gaussian_fittedValue_maximizer
    {d n : ℕ} [Nonempty (Fin n)]
    (x : Fin n → Point d) {K : Set (Point d)}
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ∀ i, ‖x i‖ ≤ T) (hK : ∀ θ ∈ K, ‖θ‖ ≤ S)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    ∃! v, IsMaxOn (gaussianFittedSet x K) (weightedLogLikelihood w) v := by
  let C := gaussianFittedSet x K
  have hCpos : C ⊆ positiveVectors n :=
    gaussianFittedSet_subset_positiveVectors x K hT hS hx hK
  obtain ⟨v, hv⟩ := exists_fittedValue_maximizer
    (isCompact_gaussianFittedSet x hKcompact)
    (gaussianFittedSet_nonempty x hKnonempty) hCpos w
  refine ⟨v, hv, fun u hu ↦ ?_⟩
  exact fittedValue_maximizer_unique (convex_gaussianFittedSet x K)
    hCpos hw hu hv

end ReweightedNPMLE
