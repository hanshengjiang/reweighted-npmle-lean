import ReweightedNPMLE.GaussianIncidence
import ReweightedNPMLE.IncidenceJacobian
import ReweightedNPMLE.IncidenceProjection
import ReweightedNPMLE.GaussianStructural
import Mathlib.Tactic

/-!
# Simultaneous Gaussian evaluation independence

Normalized Gaussian dependence charts are covered by countably many regular
derivative-equation loci. Their nuisance dimension is below the number of
sample equations, so the implicit-function null-projection theorem excludes
all data-dependent location dependences on one Borel conull data set.
-/

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE

abbrev ObservationDerivativeIndex (d : ℕ) := Σ m : ℕ, Fin m → Fin d

noncomputable def gaussianObservationDerivativeFamily {d k : ℕ} (j₀ : Fin k)
    (ω : ObservationDerivativeIndex d) (η : GaussianDependenceParameter d k j₀)
    (y : Point d) : ℝ :=
  iteratedFDeriv ℝ ω.1 (gaussianDependenceFamily j₀ η) y
    (fun i ↦ (EuclideanSpace.basisFun (Fin d) ℝ) (ω.2 i))

theorem contDiff_gaussianObservationDerivativeFamily_joint {d k : ℕ} (j₀ : Fin k)
    (ω : ObservationDerivativeIndex d) :
    ContDiff ℝ ⊤ (Function.uncurry (gaussianObservationDerivativeFamily j₀ ω)) := by
  have hf : AnalyticOnNhd ℝ (Function.uncurry (gaussianDependenceFamily (d := d) j₀)) univ :=
    fun p _ ↦ analyticAt_gaussianDependenceFamily_joint j₀ p
  exact contDiff_iteratedFDeriv_word_with_parameter _ hf.contDiff ω.1
    (fun i ↦ (EuclideanSpace.basisFun (Fin d) ℝ) (ω.2 i))

def gaussianIncidenceSet {d k n : ℕ} (j₀ : Fin k) :
    Set (GaussianDependenceParameter d k j₀ × (Fin n → Point d)) :=
  {p | p.1 ∈ gaussianDependenceDomain j₀ ∧ ∀ i, gaussianDependenceFamily j₀ p.1 (p.2 i) = 0}

theorem gaussianIncidence_has_regular_derivative_equations {d k n : ℕ} (j₀ : Fin k)
    (p : GaussianDependenceParameter d k j₀ × (Fin n → Point d))
    (hp : p ∈ gaussianIncidenceSet j₀) :
    ∃ ω : Fin n → ObservationDerivativeIndex d,
      incidenceEquations (fun i ↦ gaussianObservationDerivativeFamily j₀ (ω i)) p = 0 ∧
      Function.Surjective (fderiv ℝ
        (incidenceEquations (fun i ↦ gaussianObservationDerivativeFamily j₀ (ω i))) p) := by
  have hregular := fun i ↦ gaussianDependenceFamily_regular_derivative_at_zero j₀ p.1 hp.1
    (p.2 i) (hp.2 i)
  choose m ℓ σ hzero hnonzero using hregular
  let ω : Fin n → ObservationDerivativeIndex d := fun i ↦ ⟨m i, σ i⟩
  refine ⟨ω, funext hzero, ?_⟩
  exact fderiv_incidenceEquations_surjective _ p
    (fun i ↦ (contDiff_gaussianObservationDerivativeFamily_joint j₀ (ω i)).differentiable
      (by simp) |>.differentiableAt) (fun i ↦ (EuclideanSpace.basisFun (Fin d) ℝ) (ℓ i)) hnonzero

theorem volume_projection_gaussianIncidenceSet_eq_zero {d k n : ℕ} (j₀ : Fin k)
    (hkn : k * (d + 1) ≤ n) :
    volume ((ContinuousLinearMap.snd ℝ (GaussianDependenceParameter d k j₀)
      (Fin n → Point d)) '' gaussianIncidenceSet (n := n) j₀) = 0 := by
  let π := ContinuousLinearMap.snd ℝ (GaussianDependenceParameter d k j₀) (Fin n → Point d)
  let g := fun ω : Fin n → ObservationDerivativeIndex d ↦
    incidenceEquations (fun i ↦ gaussianObservationDerivativeFamily j₀ (ω i))
  let R := fun ω : Fin n → ObservationDerivativeIndex d ↦
    {p | g ω p = 0 ∧ Function.Surjective (fderiv ℝ (g ω) p)}
  have hdim : Module.finrank ℝ
      (GaussianDependenceParameter d k j₀ × (Fin n → Point d)) <
        Module.finrank ℝ (Fin n → Point d) + Module.finrank ℝ (Fin n → ℝ) := by
    have hh := finrank_gaussianDependenceParameter_lt j₀ hkn
    rw [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin]
    omega
  have hnull : ∀ ω : Fin n → ObservationDerivativeIndex d, volume (π '' R ω) = 0 := by
    intro ω
    exact measure_projection_regular_zero_locus_eq_zero volume π (g ω)
      ((contDiff_incidenceEquations_of_joint _
        (fun i ↦ contDiff_gaussianObservationDerivativeFamily_joint j₀ (ω i))).of_le le_top) hdim
  have hunion : volume (⋃ ω : Fin n → ObservationDerivativeIndex d, π '' R ω) = 0 :=
    measure_iUnion_null_iff.mpr hnull
  apply measure_mono_null _ hunion
  rintro x ⟨p, hp, rfl⟩
  obtain ⟨ω, hzero, hsurj⟩ := gaussianIncidence_has_regular_derivative_equations j₀ p hp
  exact mem_iUnion.mpr ⟨ω, ⟨p, ⟨hzero, hsurj⟩, rfl⟩⟩

noncomputable def gaussianBadData (n d : ℕ) : Set (Fin n → Point d) :=
  ⋃ k : ℕ, ⋃ j₀ : Fin k, if k * (d + 1) ≤ n then
    (ContinuousLinearMap.snd ℝ (GaussianDependenceParameter d k j₀) (Fin n → Point d)) ''
      gaussianIncidenceSet j₀ else ∅

theorem volume_gaussianBadData_eq_zero (n d : ℕ) : volume (gaussianBadData n d) = 0 := by
  unfold gaussianBadData
  apply measure_iUnion_null_iff.mpr
  intro k
  apply measure_iUnion_null_iff.mpr
  intro j₀
  split_ifs with hkn
  · exact volume_projection_gaussianIncidenceSet_eq_zero j₀ hkn
  · exact measure_empty

/-- Proposition: one Borel conull data set works simultaneously for every
distinct location list with `k(d+1) <= n`. Locations may depend on the data. -/
theorem gaussian_generic_evaluation_independence (n d : ℕ) :
    ∃ X : Set (Fin n → Point d), MeasurableSet X ∧ volume Xᶜ = 0 ∧
      ∀ x ∈ X, ∀ k : ℕ, k * (d + 1) ≤ n → ∀ θ : Fin k → Point d,
        Function.Injective θ →
          LinearIndependent ℝ (fun j i ↦ gaussianKernel d (x i) (θ j)) := by
  let N := toMeasurable volume (gaussianBadData n d)
  refine ⟨Nᶜ, (measurableSet_toMeasurable volume _).compl, ?_, ?_⟩
  · rw [compl_compl]
    exact (measure_toMeasurable (μ := volume) (gaussianBadData n d)).trans
      (volume_gaussianBadData_eq_zero n d)
  · intro x hx k hk θ hθ
    by_contra hdep
    obtain ⟨j₀, η, hη, hzero⟩ := gaussian_evaluation_dependence_has_normalized_chart θ hθ x hdep
    have hbad : x ∈ gaussianBadData n d := by
      unfold gaussianBadData
      refine mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨j₀, ?_⟩⟩
      rw [if_pos hk]
      exact ⟨(η, x), ⟨hη, hzero⟩, rfl⟩
    exact hx (subset_toMeasurable volume _ hbad)

/-- The same Borel conull data set also gives the full-measure uniqueness
consequence. Neither the locations nor the weights are fixed in advance. -/
theorem gaussian_generic_optimizer_fiber_uniqueness (n d : ℕ) [Nonempty (Fin n)] :
    ∃ X : Set (Fin n → Point d), MeasurableSet X ∧ volume Xᶜ = 0 ∧
      ∀ x ∈ X, ∀ (Θ : Type) [MetricSpace Θ] [CompactSpace Θ]
        [MeasurableSpace Θ] [BorelSpace Θ],
      ∀ (θ : Θ → Point d), Continuous θ → Function.Injective θ →
      ∀ (m : ℕ) (w v : Fin n → ℝ), w ∈ positiveVectors n →
        IsMaxOn (convexHull ℝ (range (fun a ↦ gaussianScoreFeature x (θ a))))
          (weightedLogLikelihood w) v →
        (2 * m) * (d + 1) ≤ n →
        (∀ μ : ProbabilityMeasure Θ,
          IsExtremeProbabilityMixture (fun a ↦ gaussianScoreFeature x (θ a)) v μ →
            (μ : Measure Θ).support.ncard ≤ m) →
        ∃ μ : ProbabilityMeasure Θ,
          probabilityMixtureFiber (fun a i ↦ gaussianKernel d (x i) (θ a))
            ((fun i ↦ gaussianDensity d (x i)) * v) = {μ} ∧
          IsExtremeProbabilityMixture (fun a i ↦ gaussianKernel d (x i) (θ a))
            ((fun i ↦ gaussianDensity d (x i)) * v) μ ∧
          (μ : Measure Θ).support.Finite ∧ (μ : Measure Θ).support.ncard ≤ m := by
  obtain ⟨X, hX, hnull, hgeneric⟩ := gaussian_generic_evaluation_independence n d
  refine ⟨X, hX, hnull, ?_⟩
  intro x hx Θ _ _ _ _ θ hθ hθinj m w v hw hv hsize hsmall
  exact gaussian_optimizer_fiber_unique_of_evaluation_independence x θ hθ hθinj
    w v hw hv hsize (hgeneric x hx) hsmall

/-- The simultaneous genericity conclusion holds almost surely under any
data law having a density with respect to Lebesgue measure. -/
theorem gaussian_evaluation_independence_ae {n d : ℕ}
    (P : Measure (Fin n → Point d)) (hP : P ≪ volume) :
    ∀ᵐ x ∂P, ∀ k : ℕ, k * (d + 1) ≤ n → ∀ θ : Fin k → Point d,
      Function.Injective θ →
        LinearIndependent ℝ (fun j i ↦ gaussianKernel d (x i) (θ j)) := by
  obtain ⟨X, _, hnull, hgeneric⟩ := gaussian_generic_evaluation_independence n d
  have hX : ∀ᵐ x ∂P, x ∈ X := by
    rw [ae_iff]
    exact hP hnull
  filter_upwards [hX] with x hx
  exact hgeneric x hx

end ReweightedNPMLE
