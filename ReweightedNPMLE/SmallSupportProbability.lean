import ReweightedNPMLE.FullExtremeSupport
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Tactic

/-!
# Closed sets of probability laws with bounded finite support

The at-most-`m`-atom laws form a compact set in the weak topology. Finite
atomic laws are parameterized by compact atom lists and closed simplices,
including zero masses and coincident locations.
-/

open Set MeasureTheory
open scoped BigOperators Topology

namespace ReweightedNPMLE

noncomputable def finiteProbabilityLawMap {Θ : Type*} [MeasurableSpace Θ] (m : ℕ) :
    (Fin m → Θ) × (finiteSimplex m) → ProbabilityMeasure Θ :=
  fun p ↦ finiteProbabilityMeasure p.1 p.2.val p.2.property

theorem continuous_finiteProbabilityLawMap {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (m : ℕ) : Continuous (finiteProbabilityLawMap (Θ := Θ) m) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro f
  change Continuous (fun p : (Fin m → Θ) × (finiteSimplex m) ↦
    probabilityIntegralFunctional (finiteProbabilityMeasure p.1 p.2.val p.2.property) f)
  simp_rw [probabilityIntegralFunctional_finiteProbabilityMeasure]
  apply continuous_finsetSum
  intro j _
  have hp : Continuous (fun p : (Fin m → Θ) × (finiteSimplex m) ↦ p.2.val j) :=
    (continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)
  have hθ : Continuous (fun p : (Fin m → Θ) × (finiteSimplex m) ↦ p.1 j) :=
    (continuous_apply j).comp continuous_fst
  exact hp.mul (f.continuous.comp hθ)

theorem isCompact_range_finiteProbabilityLawMap {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (m : ℕ) : IsCompact (range (finiteProbabilityLawMap (Θ := Θ) m)) := by
  letI : CompactSpace (finiteSimplex m) := isCompact_iff_compactSpace.mp (isCompact_finiteSimplex m)
  exact isCompact_range (continuous_finiteProbabilityLawMap m)

noncomputable def smallSupportProbabilityLaws (Θ : Type*) [MeasurableSpace Θ] (m : ℕ) :
    Set (ProbabilityMeasure Θ) :=
  ⋃ k : Fin (m + 1), range (finiteProbabilityLawMap (Θ := Θ) (k : ℕ))

theorem isCompact_smallSupportProbabilityLaws {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (m : ℕ) : IsCompact (smallSupportProbabilityLaws Θ m) :=
  isCompact_iUnion (fun k ↦ isCompact_range_finiteProbabilityLawMap (k : ℕ))

theorem mem_smallSupportProbabilityLaws_iff {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (m : ℕ) (μ : ProbabilityMeasure Θ) :
    μ ∈ smallSupportProbabilityLaws Θ m ↔
      (μ : Measure Θ).support.Finite ∧ (μ : Measure Θ).support.ncard ≤ m := by
  constructor
  · intro hμ
    obtain ⟨k, p, rfl⟩ := mem_iUnion.mp hμ
    have hsub : (finiteProbabilityLawMap (k : ℕ) p : Measure Θ).support ⊆ range p.1 :=
      Measure.support_subset_of_isClosed (finite_range p.1).isClosed
        (finiteProbabilityMeasure_ae_mem_range p.1 p.2.val p.2.property)
    have hfinite := (finite_range p.1).subset hsub
    have hrange : (range p.1).ncard ≤ (k : ℕ) := by
      simpa only [image_univ, ncard_univ, Nat.card_fin] using
        (ncard_image_le (s := (univ : Set (Fin (k : ℕ)))) (f := p.1))
    refine ⟨hfinite, ?_⟩
    exact (ncard_le_ncard hsub (finite_range p.1)).trans
      (hrange.trans (by omega))
  · rintro ⟨hfinite, hcard⟩
    obtain ⟨k, θ, p, hp, hk, _, _, _, heq⟩ :=
      probabilityMeasure_positive_finiteRepresentation_of_finite_support μ hfinite
    have hkm : k < m + 1 := by omega
    exact mem_iUnion.mpr ⟨⟨k, hkm⟩, ⟨(θ, ⟨p, hp⟩), heq⟩⟩

theorem isClosed_smallSupportProbabilityLaws {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (m : ℕ) : IsClosed (smallSupportProbabilityLaws Θ m) :=
  (isCompact_smallSupportProbabilityLaws m).isClosed

end ReweightedNPMLE
