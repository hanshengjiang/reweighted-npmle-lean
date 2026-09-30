import ReweightedNPMLE.ProbabilityFiberGeometry
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Tactic

/-!
# Independent finite mixing laws are full-fiber extreme points

Finite-support representation and uniqueness are proved for arbitrary
probability measures concentrated on that finite support. Consequently,
an independent finite mixing law is extreme against decompositions into
arbitrary probability measures, not only against finite coefficient vectors.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE

theorem measure_eq_sum_dirac_of_ae_mem_range {Θ : Type*} [MeasurableSpace Θ]
    [MeasurableSingletonClass Θ] {m : ℕ} (θ : Fin m → Θ) (hθ : Function.Injective θ)
    (μ : Measure Θ) (hμ : ∀ᵐ x ∂μ, x ∈ range θ) :
    μ = ∑ j, μ {θ j} • Measure.dirac (θ j) := by
  classical
  let S : Finset Θ := Finset.univ.image θ
  have hS : ∀ᵐ x ∂μ, x ∈ S := hμ.mono (fun x hx ↦ by simpa [S] using hx)
  have hh := Measure.ae_mem_finset_iff.mp hS
  dsimp [S] at hh
  rw [Finset.sum_image (fun j _ k _ hjk ↦ hθ hjk)] at hh
  exact hh

theorem probabilityMeasure_finiteRepresentation_of_ae_mem_range {Θ : Type*}
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] {m : ℕ}
    (θ : Fin m → Θ) (hθ : Function.Injective θ) (μ : ProbabilityMeasure Θ)
    (hμ : ∀ᵐ x ∂(μ : Measure Θ), x ∈ range θ) :
    ∃ (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m), finiteProbabilityMeasure θ p hp = μ := by
  let p : Fin m → ℝ := fun j ↦ (μ : Measure Θ).real {θ j}
  have hrepr := measure_eq_sum_dirac_of_ae_mem_range θ hθ (μ : Measure Θ) hμ
  have hsum : (∑ j, (μ : Measure Θ) {θ j}) = 1 := by
    have hh := congrArg (fun ρ : Measure Θ ↦ ρ univ) hrepr
    simpa only [measure_univ, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one] using hh.symm
  have hp : p ∈ finiteSimplex m := by
    refine ⟨fun j ↦ measureReal_nonneg, ?_⟩
    dsimp [p, measureReal_def]
    rw [← ENNReal.toReal_sum (fun j _ ↦ measure_ne_top (μ : Measure Θ) {θ j}), hsum]
    norm_num
  refine ⟨p, hp, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  change (∑ j, ENNReal.ofReal (p j) • Measure.dirac (θ j)) = (μ : Measure Θ)
  have hpcast : ∀ j, ENNReal.ofReal (p j) = (μ : Measure Θ) {θ j} := fun j ↦
    ENNReal.ofReal_toReal (measure_ne_top (μ : Measure Θ) {θ j})
  simp_rw [hpcast]
  exact hrepr.symm

theorem finiteProbabilityMeasure_ae_mem_range {Θ : Type*}
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] {m : ℕ}
    (θ : Fin m → Θ) (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m) :
    ∀ᵐ x ∂(finiteProbabilityMeasure θ p hp : Measure Θ), x ∈ range θ := by
  change ∀ᵐ x ∂(∑ j, ENNReal.ofReal (p j) • Measure.dirac (θ j)), x ∈ range θ
  rw [ae_finsetSum_measure_iff]
  intro j _
  apply Measure.ae_smul_measure
  filter_upwards [ae_eq_dirac (fun x : Θ ↦ x)] with x hx
  rw [hx]
  exact mem_range_self j

theorem finiteProbabilityMeasure_singleton_mass {Θ : Type*}
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] {m : ℕ}
    (θ : Fin m → Θ) (hθ : Function.Injective θ)
    (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m) (j : Fin m) :
    (finiteProbabilityMeasure θ p hp : Measure Θ) {θ j} = ENNReal.ofReal (p j) := by
  classical
  change (∑ k, ENNReal.ofReal (p k) • Measure.dirac (θ k)) {θ j} = _
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    have hneq : θ k ≠ θ j := fun hh ↦ hkj (hθ hh)
    simp [hneq]
  · simp

theorem finiteProbabilityMeasure_coefficients_injective {Θ : Type*}
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] {m : ℕ}
    (θ : Fin m → Θ) (hθ : Function.Injective θ)
    (p q : Fin m → ℝ) (hp : p ∈ finiteSimplex m) (hq : q ∈ finiteSimplex m)
    (heq : finiteProbabilityMeasure θ p hp = finiteProbabilityMeasure θ q hq) : p = q := by
  funext j
  have hh := congrArg (fun μ : ProbabilityMeasure Θ ↦ (μ : Measure Θ) {θ j}) heq
  dsimp only at hh
  rw [finiteProbabilityMeasure_singleton_mass θ hθ p hp,
    finiteProbabilityMeasure_singleton_mass θ hθ q hq] at hh
  have hr := congrArg ENNReal.toReal hh
  simpa only [ENNReal.toReal_ofReal (hp.1 j), ENNReal.toReal_ofReal (hq.1 j)] using hr

theorem finiteProbabilityMeasure_support {Θ : Type*}
    [TopologicalSpace Θ] [T1Space Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]
    {m : ℕ} (θ : Fin m → Θ) (hθ : Function.Injective θ)
    (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m) (hpPos : ∀ j, 0 < p j) :
    (finiteProbabilityMeasure θ p hp : Measure Θ).support = range θ := by
  apply Subset.antisymm
  · exact Measure.support_subset_of_isClosed (finite_range θ).isClosed
      (finiteProbabilityMeasure_ae_mem_range θ p hp)
  · rintro x ⟨j, rfl⟩
    apply (Measure.mem_support_iff_forall (θ j)).mpr
    intro U hU
    have hsub : {θ j} ⊆ U := singleton_subset_iff.mpr (mem_of_mem_nhds hU)
    have hsingle : 0 < (finiteProbabilityMeasure θ p hp : Measure Θ) {θ j} := by
      rw [finiteProbabilityMeasure_singleton_mass θ hθ p hp]
      exact ENNReal.ofReal_pos.mpr (hpPos j)
    exact hsingle.trans_le (measure_mono hsub)

theorem probabilityIntegralFunctional_finiteProbabilityMeasure {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {m : ℕ} (θ : Fin m → Θ) (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m) (f : C(Θ, ℝ)) :
    probabilityIntegralFunctional (finiteProbabilityMeasure θ p hp) f = ∑ j, p j * f (θ j) := by
  have hh := congrFun (probabilityMixtureValue_finiteProbabilityMeasure
    (fun x : Θ ↦ fun _ : Fin 1 ↦ f x) (by fun_prop) θ p hp) (0 : Fin 1)
  simpa only [probabilityMixtureValue, probabilityIntegralFunctional, finiteMixtureValue,
    Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hh

theorem finiteProbabilityMeasure_convexCombination {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {m : ℕ} (θ : Fin m → Θ) (p q r : Fin m → ℝ)
    (hp : p ∈ finiteSimplex m) (hq : q ∈ finiteSimplex m) (hr : r ∈ finiteSimplex m)
    (a b : ℝ≥0) (hab : a + b = 1)
    (hrepr : (a : ℝ) • q + (b : ℝ) • r = p) :
    probabilityConvexCombination a b hab (finiteProbabilityMeasure θ q hq)
      (finiteProbabilityMeasure θ r hr) = finiteProbabilityMeasure θ p hp := by
  apply probabilityIntegralFunctional_injective
  rw [probabilityIntegralFunctional_convexCombination]
  funext f
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    probabilityIntegralFunctional_finiteProbabilityMeasure, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hj := congrFun hrepr j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj
  rw [← hj]
  ring

theorem probabilityMixtureFiber_unique_of_supported_independent_range {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ]
    [OpensMeasurableSpace Θ] [MeasurableSingletonClass Θ] {m n : ℕ}
    (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ)
    (θ : Fin m → Θ) (hlin : LinearIndependent ℝ (A ∘ θ))
    (μ ν : ProbabilityMeasure Θ) (hμ : μ ∈ probabilityMixtureFiber A v)
    (hν : ν ∈ probabilityMixtureFiber A v)
    (hμS : ∀ᵐ x ∂(μ : Measure Θ), x ∈ range θ)
    (hνS : ∀ᵐ x ∂(ν : Measure Θ), x ∈ range θ) : μ = ν := by
  have hθ : Function.Injective θ := fun j k hjk ↦ hlin.injective (congrArg A hjk)
  obtain ⟨p, hp, hpm⟩ := probabilityMeasure_finiteRepresentation_of_ae_mem_range θ hθ μ hμS
  obtain ⟨q, hq, hqn⟩ := probabilityMeasure_finiteRepresentation_of_ae_mem_range θ hθ ν hνS
  have hpeq : finiteMixtureValue (A ∘ θ) p = v := by
    rw [← probabilityMixtureValue_finiteProbabilityMeasure A hA θ p hp, hpm]
    exact hμ
  have hqeq : finiteMixtureValue (A ∘ θ) q = v := by
    rw [← probabilityMixtureValue_finiteProbabilityMeasure A hA θ q hq, hqn]
    exact hν
  have hpq : p = q := hlin.fintypeLinearCombination_injective (hpeq.trans hqeq.symm)
  subst q
  exact hpm.symm.trans hqn

theorem probabilityConvexCombination_left_absolutelyContinuous {Θ : Type*} [MeasurableSpace Θ]
    (a b : ℝ≥0) (hab : a + b = 1) (ha : 0 < a) (μ ν : ProbabilityMeasure Θ) :
    (μ : Measure Θ) ≪ (probabilityConvexCombination a b hab μ ν : Measure Θ) := by
  intro s hs
  change (a • (μ : Measure Θ) + b • (ν : Measure Θ)) s = 0 at hs
  rw [Measure.add_apply] at hs
  have hh := (add_eq_zero.mp hs).1
  rw [Measure.smul_apply] at hh
  change (a : ℝ≥0∞) * (μ : Measure Θ) s = 0 at hh
  exact (mul_eq_zero.mp hh).resolve_left (by exact_mod_cast ha.ne')

theorem finiteProbabilityMeasure_extreme_of_linearIndependent {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {m n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (θ : Fin m → Θ) (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m)
    (hlin : LinearIndependent ℝ (A ∘ θ)) :
    IsExtremeProbabilityMixture A (finiteMixtureValue (A ∘ θ) p) (finiteProbabilityMeasure θ p hp) := by
  let μ := finiteProbabilityMeasure θ p hp
  let v := finiteMixtureValue (A ∘ θ) p
  have hμ : μ ∈ probabilityMixtureFiber A v := probabilityMixtureValue_finiteProbabilityMeasure A hA θ p hp
  have hμS := finiteProbabilityMeasure_ae_mem_range θ p hp
  rw [isExtremeProbabilityMixture_iff]
  refine ⟨hμ, ?_⟩
  intro a b ha hb hab ν ρ hν hρ heq
  change probabilityConvexCombination a b hab ν ρ = μ at heq
  have hνac : (ν : Measure Θ) ≪ (μ : Measure Θ) := by
    rw [← heq]
    exact probabilityConvexCombination_left_absolutelyContinuous a b hab ha ν ρ
  exact probabilityMixtureFiber_unique_of_supported_independent_range A hA v θ hlin ν μ hν hμ
    (hνac.ae_le hμS) hμS

theorem finiteMixtureFiber_extreme_of_probability_extreme {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {m n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (θ : Fin m → Θ) (hθ : Function.Injective θ) (v : Fin n → ℝ)
    (p : Fin m → ℝ) (hp : p ∈ finiteMixtureFiber (A ∘ θ) v)
    (hext : IsExtremeProbabilityMixture A v (finiteProbabilityMeasure θ p hp.1)) :
    p ∈ (finiteMixtureFiber (A ∘ θ) v).extremePoints ℝ := by
  rw [mem_extremePoints_iff_left]
  refine ⟨hp, ?_⟩
  rintro q hq r hr ⟨a, b, ha, hb, hab, hrepr⟩
  let a' : ℝ≥0 := ⟨a, ha.le⟩
  let b' : ℝ≥0 := ⟨b, hb.le⟩
  have hab' : a' + b' = 1 := by apply Subtype.ext; exact hab
  have hqval : finiteProbabilityMeasure θ q hq.1 ∈ probabilityMixtureFiber A v := by
    change probabilityMixtureValue A (finiteProbabilityMeasure θ q hq.1) = v
    rw [probabilityMixtureValue_finiteProbabilityMeasure A hA θ q hq.1]
    exact hq.2
  have hrval : finiteProbabilityMeasure θ r hr.1 ∈ probabilityMixtureFiber A v := by
    change probabilityMixtureValue A (finiteProbabilityMeasure θ r hr.1) = v
    rw [probabilityMixtureValue_finiteProbabilityMeasure A hA θ r hr.1]
    exact hr.2
  have heq := (isExtremeProbabilityMixture_iff A v _).mp hext |>.2
    a' b' (by exact_mod_cast ha) (by exact_mod_cast hb) hab'
    (finiteProbabilityMeasure θ q hq.1) (finiteProbabilityMeasure θ r hr.1) hqval hrval
    (finiteProbabilityMeasure_convexCombination θ p q r hp.1 hq.1 hr.1 a' b' hab' hrepr)
  exact finiteProbabilityMeasure_coefficients_injective θ hθ q p hq.1 hp.1 heq

theorem finite_probability_optimizer_extreme_iff_linearIndependent {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {m n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (θ : Fin m → Θ) (hθ : Function.Injective θ) (v : Fin n → ℝ)
    (p : Fin m → ℝ) (hp : p ∈ finiteMixtureFiber (A ∘ θ) v) (hpPos : ∀ j, 0 < p j)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (hvpos : ∀ i, 0 < v i)
    (hApos : ∀ j i, 0 < A (θ j) i)
    (hvmax : IsMaxOn (convexHull ℝ (range (A ∘ θ))) (weightedLogLikelihood w) v) :
    IsExtremeProbabilityMixture A v (finiteProbabilityMeasure θ p hp.1) ↔
      LinearIndependent ℝ (A ∘ θ) := by
  constructor
  · intro hext
    have hf := finiteMixtureFiber_extreme_of_probability_extreme A hA θ hθ v p hp hext
    have hl := (finite_likelihood_optimizer_extreme_iff_linearIndepOn
      (A ∘ θ) v p w hw hp hvpos hApos hvmax).mp hf
    have hs : (coefficientSupport p : Set (Fin m)) = univ := by
      ext j
      simp only [Finset.mem_coe, mem_coefficientSupport, mem_univ, iff_true]
      exact (hpPos j).ne'
    rw [hs, linearIndepOn_univ_iff] at hl
    exact hl
  · intro hl
    simpa only [hp.2] using finiteProbabilityMeasure_extreme_of_linearIndependent A hA θ p hp.1 hl

end ReweightedNPMLE
