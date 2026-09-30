import ReweightedNPMLE.FittedContact
import ReweightedNPMLE.CompactConvexHull
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Convex.Integral
import Mathlib.Tactic

/-!
# Optimizer fibers over arbitrary probability measures

These are genuine probability-measure fibers, not finite coefficient fibers.
Continuous moment constraints are closed for weak convergence and the fiber
is compact on a compact parameter space. The likelihood contact identity
holds almost everywhere and everywhere on the topological support of every
optimizing measure, including measures with infinite support.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE

noncomputable def probabilityMixtureValue {Θ : Type*} [MeasurableSpace Θ] {n : ℕ}
    (A : Θ → Fin n → ℝ) (μ : ProbabilityMeasure Θ) : Fin n → ℝ :=
  fun i ↦ ∫ θ, A θ i ∂μ

def probabilityMixtureFiber {Θ : Type*} [MeasurableSpace Θ] {n : ℕ}
    (A : Θ → Fin n → ℝ) (v : Fin n → ℝ) : Set (ProbabilityMeasure Θ) :=
  {μ | probabilityMixtureValue A μ = v}

noncomputable def probabilityConvexCombination {Θ : Type*} [MeasurableSpace Θ]
    (a b : ℝ≥0) (hab : a + b = 1) (μ ν : ProbabilityMeasure Θ) : ProbabilityMeasure Θ := by
  refine ⟨a • (μ : Measure Θ) + b • (ν : Measure Θ), ⟨?_⟩⟩
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ]
  change (a : ℝ≥0∞) * 1 + (b : ℝ≥0∞) * 1 = 1
  rw [mul_one, mul_one]
  rw [← ENNReal.coe_add, hab]
  rfl

theorem probabilityMixtureValue_convexCombination {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (a b : ℝ≥0) (hab : a + b = 1) (μ ν : ProbabilityMeasure Θ) :
    probabilityMixtureValue A (probabilityConvexCombination a b hab μ ν) =
      (a : ℝ) • probabilityMixtureValue A μ + (b : ℝ) • probabilityMixtureValue A ν := by
  funext i
  have hμi := ((continuous_apply i).comp hA).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := (μ : Measure Θ))
  have hνi := ((continuous_apply i).comp hA).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) (μ := (ν : Measure Θ))
  change Integrable (fun θ ↦ A θ i) (μ : Measure Θ) at hμi
  change Integrable (fun θ ↦ A θ i) (ν : Measure Θ) at hνi
  change (∫ θ, A θ i ∂(a • (μ : Measure Θ) + b • (ν : Measure Θ))) = _
  rw [integral_add_measure hμi.smul_measure_nnreal hνi.smul_measure_nnreal]
  simp only [integral_smul_nnreal_measure, probabilityMixtureValue, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rfl

theorem probabilityMixtureFiber_convexCombination {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ)
    (a b : ℝ≥0) (hab : a + b = 1) (μ ν : ProbabilityMeasure Θ)
    (hμ : μ ∈ probabilityMixtureFiber A v) (hν : ν ∈ probabilityMixtureFiber A v) :
    probabilityConvexCombination a b hab μ ν ∈ probabilityMixtureFiber A v := by
  change probabilityMixtureValue A (probabilityConvexCombination a b hab μ ν) = v
  rw [probabilityMixtureValue_convexCombination A hA a b hab μ ν,
    show probabilityMixtureValue A μ = v from hμ, show probabilityMixtureValue A ν = v from hν,
    ← add_smul]
  have hh : (a : ℝ) + (b : ℝ) = 1 := by exact_mod_cast hab
  rw [hh, one_smul]

noncomputable def finiteProbabilityMeasure {Θ : Type*} [MeasurableSpace Θ] {m : ℕ}
    (θ : Fin m → Θ) (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m) : ProbabilityMeasure Θ := by
  refine ⟨∑ j, ENNReal.ofReal (p j) • Measure.dirac (θ j), ⟨?_⟩⟩
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ hp.1 j), hp.2]
  simp

theorem probabilityMixtureValue_finiteProbabilityMeasure {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {m n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (θ : Fin m → Θ) (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m) :
    probabilityMixtureValue A (finiteProbabilityMeasure θ p hp) =
      finiteMixtureValue (A ∘ θ) p := by
  funext i
  change (∫ a, A a i ∂(∑ j, ENNReal.ofReal (p j) • Measure.dirac (θ j))) = _
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure,
      ENNReal.toReal_ofReal (hp.1 _), finiteMixtureValue, Function.comp_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_dirac' (fun a ↦ A a i) (θ j) ((continuous_apply i).comp hA).stronglyMeasurable]
  · intro j _
    letI := IsFiniteMeasureOnCompacts.smul (Measure.dirac (θ j))
      (c := ENNReal.ofReal (p j)) ENNReal.ofReal_ne_top
    exact ((continuous_apply i).comp hA).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _) (μ := ENNReal.ofReal (p j) • Measure.dirac (θ j))

theorem probabilityMixtureFiber_nonempty_of_mem_convexHull {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ)
    (hv : v ∈ convexHull ℝ (range A)) : (probabilityMixtureFiber A v).Nonempty := by
  classical
  obtain ⟨ι, hι, p₀, B₀, hp₀, hpsum₀, hB₀, hvalue₀⟩ :=
    mem_convexHull_iff_exists_fintype.mp hv
  letI : Fintype ι := hι
  let m := Fintype.card ι
  let e : Fin m ≃ ι := (Fintype.equivFin ι).symm
  have hpre : ∀ j : Fin m, ∃ θ, A θ = B₀ (e j) := fun j ↦ hB₀ (e j)
  choose θ hθ using hpre
  let p : Fin m → ℝ := p₀ ∘ e
  have hp : p ∈ finiteSimplex m := ⟨fun j ↦ hp₀ (e j), (e.sum_comp p₀).trans hpsum₀⟩
  refine ⟨finiteProbabilityMeasure θ p hp, ?_⟩
  change probabilityMixtureValue A (finiteProbabilityMeasure θ p hp) = v
  rw [probabilityMixtureValue_finiteProbabilityMeasure A hA θ p hp]
  calc
    finiteMixtureValue (A ∘ θ) p = ∑ j : Fin m, p₀ (e j) • B₀ (e j) := by
      simp only [finiteMixtureValue, p, Function.comp_apply, hθ]
    _ = v := (e.sum_comp (fun j ↦ p₀ j • B₀ j)).trans hvalue₀

theorem continuous_probabilityMixtureValue {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) :
    Continuous (probabilityMixtureValue A) := by
  apply continuous_pi
  intro i
  exact ProbabilityMeasure.continuous_integral_continuousMap
    (⟨fun θ ↦ A θ i, (continuous_apply i).comp hA⟩ : C(Θ, ℝ))

theorem isCompact_probabilityMixtureFiber {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ) :
    IsCompact (probabilityMixtureFiber A v) := by
  exact (isClosed_eq (continuous_probabilityMixtureValue A hA) continuous_const).isCompact

theorem probabilityMixtureValue_eq_integral {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (μ : ProbabilityMeasure Θ) :
    probabilityMixtureValue A μ = ∫ θ, A θ ∂μ := by
  have hi := hA.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace A)
    (μ := (μ : Measure Θ))
  funext i
  exact (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).integral_comp_comm hi

theorem probabilityMixtureValue_mem_convexHull {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (μ : ProbabilityMeasure Θ) :
    probabilityMixtureValue A μ ∈ convexHull ℝ (range A) := by
  rw [probabilityMixtureValue_eq_integral A hA μ]
  exact (convex_convexHull ℝ (range A)).integral_mem
    (isCompact_convexHull_of_isCompact (isCompact_range hA)).isClosed
    (Eventually.of_forall fun θ ↦ subset_convexHull ℝ _ (mem_range_self θ))
    (hA.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace A))

theorem probabilityMixtureFiber_nonempty_iff_mem_convexHull {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ) :
    (probabilityMixtureFiber A v).Nonempty ↔ v ∈ convexHull ℝ (range A) := by
  constructor
  · rintro ⟨μ, hμ⟩
    rw [← show probabilityMixtureValue A μ = v from hμ]
    exact probabilityMixtureValue_mem_convexHull A hA μ
  · exact probabilityMixtureFiber_nonempty_of_mem_convexHull A hA v

/-- Optimization over all probability measures is exactly the moment fiber
of the unique positive-weight fitted-vector optimum. -/
theorem probability_optimizer_iff_mem_fiber {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} [Nonempty (Fin n)]
    (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hCeq : C = convexHull ℝ (range A))
    (hCpos : C ⊆ positiveVectors n)
    (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v) (μ : ProbabilityMeasure Θ) :
    IsMaxOn univ (fun ν : ProbabilityMeasure Θ ↦ weightedLogLikelihood w (probabilityMixtureValue A ν)) μ ↔
      μ ∈ probabilityMixtureFiber A v := by
  have hC : Convex ℝ C := hCeq ▸ convex_convexHull ℝ (range A)
  have hvalC : ∀ ν : ProbabilityMeasure Θ, probabilityMixtureValue A ν ∈ C := by
    intro ν
    rw [hCeq]
    exact probabilityMixtureValue_mem_convexHull A hA ν
  constructor
  · intro hopt
    have hfitmax : IsMaxOn C (weightedLogLikelihood w) (probabilityMixtureValue A μ) := by
      refine ⟨hvalC μ, ?_⟩
      intro u hu
      obtain ⟨ν, hν⟩ := probabilityMixtureFiber_nonempty_of_mem_convexHull A hA u (hCeq ▸ hu)
      rw [← show probabilityMixtureValue A ν = u from hν]
      exact hopt.2 ν (mem_univ ν)
    exact fittedValue_maximizer_unique hC hCpos hw hfitmax hvmax
  · intro hμ
    refine ⟨mem_univ μ, ?_⟩
    intro ν _
    change weightedLogLikelihood w (probabilityMixtureValue A ν) ≤
      weightedLogLikelihood w (probabilityMixtureValue A μ)
    rw [show probabilityMixtureValue A μ = v from hμ]
    exact hvmax.2 _ (hvalC ν)

theorem probability_optimizer_exists {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} [Nonempty (Fin n)]
    (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hCeq : C = convexHull ℝ (range A))
    (hCpos : C ⊆ positiveVectors n)
    (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v) :
    ∃ μ : ProbabilityMeasure Θ,
      IsMaxOn univ (fun ν : ProbabilityMeasure Θ ↦ weightedLogLikelihood w (probabilityMixtureValue A ν)) μ := by
  obtain ⟨μ, hμ⟩ := probabilityMixtureFiber_nonempty_of_mem_convexHull A hA v (hCeq ▸ hvmax.1)
  exact ⟨μ, (probability_optimizer_iff_mem_fiber A hA hCeq hCpos w v hw hvmax μ).mpr hμ⟩

theorem integral_likelihoodContactFunctional {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (μ : ProbabilityMeasure Θ) (w v : Fin n → ℝ) :
    (∫ θ, likelihoodContactFunctional w v (A θ) ∂μ) =
      likelihoodContactFunctional w v (probabilityMixtureValue A μ) := by
  simp only [likelihoodContactFunctional_apply, probabilityMixtureValue]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro i _
    exact ((continuous_apply i).comp hA).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
      |>.const_mul _

theorem probability_optimizer_likelihood_contact_ae {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} [Nonempty (Fin n)]
    (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v)
    (μ : ProbabilityMeasure Θ) (hμ : μ ∈ probabilityMixtureFiber A v) :
    (fun θ ↦ likelihoodContactFunctional w v (A θ)) =ᵐ[(μ : Measure Θ)] fun _ ↦ 1 := by
  have hq : Continuous (fun θ ↦ likelihoodContactFunctional w v (A θ)) := by
    simp only [likelihoodContactFunctional_apply]
    fun_prop
  have hqi := hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := (μ : Measure Θ))
  have hle : (fun θ ↦ likelihoodContactFunctional w v (A θ)) ≤ᵐ[(μ : Measure Θ)] fun _ ↦ 1 :=
    Eventually.of_forall fun θ ↦ likelihoodContactFunctional_le_one_of_isMaxOn
      hC hCpos w v (A θ) hw hvmax (hAC (mem_range_self θ))
  apply (integral_eq_iff_of_ae_le hqi (integrable_const 1) hle).mp
  rw [integral_likelihoodContactFunctional A hA μ w v, show probabilityMixtureValue A μ = v from hμ]
  simpa using likelihoodContactFunctional_self w v hw (hCpos hvmax.1)

theorem probability_optimizer_likelihood_contact_on_support {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} [Nonempty (Fin n)]
    (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v)
    (μ : ProbabilityMeasure Θ) (hμ : μ ∈ probabilityMixtureFiber A v) :
    ∀ θ ∈ (μ : Measure Θ).support, likelihoodContactFunctional w v (A θ) = 1 := by
  have hq : Continuous (fun θ ↦ likelihoodContactFunctional w v (A θ)) := by
    simp only [likelihoodContactFunctional_apply]
    fun_prop
  exact (μ : Measure Θ).support_subset_of_isClosed (isClosed_eq hq continuous_const)
    (probability_optimizer_likelihood_contact_ae A hA hC hCpos hAC w v hw hvmax μ hμ)

end ReweightedNPMLE
