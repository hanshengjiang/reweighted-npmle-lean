import ReweightedNPMLE.ProbabilityOptimizerFiber
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Tactic

/-!
# Real-vector-space geometry of full probability fibers

Integration against continuous test functions embeds probability measures
injectively into a locally convex real vector space with its product topology.
The weakly compact mixture fiber has a compact convex image. Extreme points
are thus mathlib extreme points of a faithful representation of the full
probability-measure fiber, rather than of a finite coefficient simplex.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE

noncomputable def probabilityIntegralFunctional {Θ : Type*}
    [TopologicalSpace Θ] [MeasurableSpace Θ] (μ : ProbabilityMeasure Θ) : C(Θ, ℝ) → ℝ :=
  fun f ↦ ∫ θ, f θ ∂μ

theorem continuous_probabilityIntegralFunctional {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ] :
    Continuous (probabilityIntegralFunctional (Θ := Θ)) := by
  apply continuous_pi
  intro f
  exact ProbabilityMeasure.continuous_integral_continuousMap f

theorem probabilityIntegralFunctional_injective {Θ : Type*}
    [TopologicalSpace Θ] [HasOuterApproxClosed Θ] [MeasurableSpace Θ] [BorelSpace Θ] :
    Function.Injective (probabilityIntegralFunctional (Θ := Θ)) := by
  intro μ ν h
  have hh : μ.toFiniteMeasure = ν.toFiniteMeasure :=
    FiniteMeasure.ext_of_forall_integral_eq (fun f ↦ congrFun h f.toContinuousMap)
  apply ProbabilityMeasure.toMeasure_injective
  exact congrArg (fun ρ : FiniteMeasure Θ ↦ (ρ : Measure Θ)) hh

theorem probabilityIntegralFunctional_convexCombination {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (a b : ℝ≥0) (hab : a + b = 1) (μ ν : ProbabilityMeasure Θ) :
    probabilityIntegralFunctional (probabilityConvexCombination a b hab μ ν) =
      (a : ℝ) • probabilityIntegralFunctional μ + (b : ℝ) • probabilityIntegralFunctional ν := by
  funext f
  have hμ := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
    (μ := (μ : Measure Θ))
  have hν := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
    (μ := (ν : Measure Θ))
  change (∫ θ, f θ ∂(a • (μ : Measure Θ) + b • (ν : Measure Θ))) = _
  rw [integral_add_measure hμ.smul_measure_nnreal hν.smul_measure_nnreal]
  simp only [integral_smul_nnreal_measure, probabilityIntegralFunctional, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rfl

def probabilityFiberImage {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] {n : ℕ}
    (A : Θ → Fin n → ℝ) (v : Fin n → ℝ) : Set (C(Θ, ℝ) → ℝ) :=
  probabilityIntegralFunctional '' probabilityMixtureFiber A v

theorem isCompact_probabilityFiberImage {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ) :
    IsCompact (probabilityFiberImage A v) :=
  (isCompact_probabilityMixtureFiber A hA v).image continuous_probabilityIntegralFunctional

theorem convex_probabilityFiberImage {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ) :
    Convex ℝ (probabilityFiberImage A v) := by
  rintro x ⟨μ, hμ, rfl⟩ y ⟨ν, hν, rfl⟩ a b ha hb hab
  let a' : ℝ≥0 := ⟨a, ha⟩
  let b' : ℝ≥0 := ⟨b, hb⟩
  have hab' : a' + b' = 1 := by apply Subtype.ext; exact hab
  refine ⟨probabilityConvexCombination a' b' hab' μ ν,
    probabilityMixtureFiber_convexCombination A hA v a' b' hab' μ ν hμ hν, ?_⟩
  exact probabilityIntegralFunctional_convexCombination a' b' hab' μ ν

def IsExtremeProbabilityMixture {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ] {n : ℕ}
    (A : Θ → Fin n → ℝ) (v : Fin n → ℝ) (μ : ProbabilityMeasure Θ) : Prop :=
  probabilityIntegralFunctional μ ∈ (probabilityFiberImage A v).extremePoints ℝ

theorem isExtremeProbabilityMixture_mem_fiber {Θ : Type*}
    [TopologicalSpace Θ] [HasOuterApproxClosed Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (v : Fin n → ℝ) (μ : ProbabilityMeasure Θ)
    (hμ : IsExtremeProbabilityMixture A v μ) : μ ∈ probabilityMixtureFiber A v := by
  obtain ⟨ν, hν, heq⟩ := hμ.1
  exact probabilityIntegralFunctional_injective heq ▸ hν

theorem isExtremeProbabilityMixture_iff {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [HasOuterApproxClosed Θ]
    [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (v : Fin n → ℝ) (μ : ProbabilityMeasure Θ) :
    IsExtremeProbabilityMixture A v μ ↔ μ ∈ probabilityMixtureFiber A v ∧
      ∀ (a b : ℝ≥0) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
        (ν ρ : ProbabilityMeasure Θ), ν ∈ probabilityMixtureFiber A v →
        ρ ∈ probabilityMixtureFiber A v →
        probabilityConvexCombination a b hab ν ρ = μ → ν = μ := by
  constructor
  · intro hμ
    refine ⟨isExtremeProbabilityMixture_mem_fiber A v μ hμ, ?_⟩
    intro a b ha hb hab ν ρ hν hρ heq
    apply probabilityIntegralFunctional_injective
    apply (mem_extremePoints_iff_left.mp hμ).2 _ ⟨ν, hν, rfl⟩ _ ⟨ρ, hρ, rfl⟩
    refine ⟨(a : ℝ), (b : ℝ), by exact_mod_cast ha, by exact_mod_cast hb,
      by exact_mod_cast hab, ?_⟩
    rw [← probabilityIntegralFunctional_convexCombination a b hab ν ρ, heq]
  · rintro ⟨hμ, huniq⟩
    refine ⟨⟨μ, hμ, rfl⟩, ?_⟩
    rintro x ⟨ν, hν, rfl⟩ y ⟨ρ, hρ, rfl⟩ ⟨a, b, ha, hb, hab, hrepr⟩
    let a' : ℝ≥0 := ⟨a, ha.le⟩
    let b' : ℝ≥0 := ⟨b, hb.le⟩
    have hab' : a' + b' = 1 := by apply Subtype.ext; exact hab
    have heq : probabilityConvexCombination a' b' hab' ν ρ = μ := by
      apply probabilityIntegralFunctional_injective
      rw [probabilityIntegralFunctional_convexCombination a' b' hab' ν ρ]
      exact hrepr
    exact congrArg probabilityIntegralFunctional
      (huniq a' b' (by exact_mod_cast ha) (by exact_mod_cast hb) hab' ν ρ hν hρ heq)

theorem probabilityMixtureFiber_extreme_nonempty {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ)
    (hv : v ∈ convexHull ℝ (range A)) :
    ∃ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A v μ := by
  have hnonempty : (probabilityFiberImage A v).Nonempty :=
    (probabilityMixtureFiber_nonempty_of_mem_convexHull A hA v hv).image _
  obtain ⟨x, hx⟩ := (isCompact_probabilityFiberImage A hA v).extremePoints_nonempty hnonempty
  obtain ⟨μ, hμ, rfl⟩ := hx.1
  exact ⟨μ, hx⟩

theorem probabilityFiberImage_kreinMilman {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ) :
    closure (convexHull ℝ ((probabilityFiberImage A v).extremePoints ℝ)) =
      probabilityFiberImage A v :=
  closure_convexHull_extremePoints (isCompact_probabilityFiberImage A hA v)
    (convex_probabilityFiberImage A hA v)

/-- The full probability-measure uniqueness step of Krein--Milman. No
finite-dictionary or finite-support assumption is made here. -/
theorem probabilityMixtureFiber_eq_singleton_of_extreme_unique {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A) (v : Fin n → ℝ)
    (hv : v ∈ convexHull ℝ (range A))
    (hunique : ∀ μ ν : ProbabilityMeasure Θ,
      IsExtremeProbabilityMixture A v μ → IsExtremeProbabilityMixture A v ν → μ = ν) :
    ∃ μ : ProbabilityMeasure Θ, probabilityMixtureFiber A v = {μ} ∧
      IsExtremeProbabilityMixture A v μ := by
  obtain ⟨μ, hμ⟩ := probabilityMixtureFiber_extreme_nonempty A hA v hv
  have hext : (probabilityFiberImage A v).extremePoints ℝ = {probabilityIntegralFunctional μ} := by
    ext x
    constructor
    · intro hx
      obtain ⟨ν, hν, rfl⟩ := hx.1
      exact congrArg probabilityIntegralFunctional (hunique ν μ hx hμ)
    · rintro rfl
      exact hμ
  have himage : probabilityFiberImage A v = {probabilityIntegralFunctional μ} := by
    rw [← probabilityFiberImage_kreinMilman A hA v, hext, convexHull_singleton, closure_singleton]
  refine ⟨μ, ?_, hμ⟩
  ext ν
  constructor
  · intro hν
    have hh : probabilityIntegralFunctional ν ∈ probabilityFiberImage A v := ⟨ν, hν, rfl⟩
    rw [himage] at hh
    exact probabilityIntegralFunctional_injective hh
  · intro hν
    have heq : ν = μ := hν
    rw [heq]
    exact isExtremeProbabilityMixture_mem_fiber A v μ hμ

end ReweightedNPMLE
