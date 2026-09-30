import ReweightedNPMLE.MeasureExtremeSupport
import Mathlib.Tactic

/-!
# Uniqueness from small extreme supports and evaluation independence

Two extreme laws are concentrated on the union of their finite supports.
Independence on that union forces equality; the full-measure Krein--Milman
theorem then makes the whole optimizer fiber a singleton. This does not assume
finite support of non-extreme optimizing measures.
-/

open Set MeasureTheory
open scoped Topology

namespace ReweightedNPMLE

theorem probabilityMixtureFiber_eq_singleton_of_small_extreme_supports {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n m L : ℕ} [Nonempty (Fin n)]
    (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (w v : Fin n → ℝ) (hw : w ∈ positiveVectors n)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v)
    (hvHull : v ∈ convexHull ℝ (range A)) (hsize : 2 * m ≤ L)
    (hind : ∀ (k : ℕ), k ≤ L → ∀ θ : Fin k → Θ,
      Function.Injective θ → LinearIndependent ℝ (A ∘ θ))
    (hsmall : ∀ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A v μ →
      (μ : Measure Θ).support.ncard ≤ m) :
    ∃ μ : ProbabilityMeasure Θ, probabilityMixtureFiber A v = {μ} ∧
      IsExtremeProbabilityMixture A v μ ∧ (μ : Measure Θ).support.Finite ∧
        (μ : Measure Θ).support.ncard ≤ m := by
  classical
  have hunique : ∀ μ ν : ProbabilityMeasure Θ,
      IsExtremeProbabilityMixture A v μ → IsExtremeProbabilityMixture A v ν → μ = ν := by
    intro μ ν hμext hνext
    have hμfinite := (full_extreme_optimizer_support_finite_card_le A hA hC hCpos
      hAC w v hw hvmax μ hμext).1
    have hνfinite := (full_extreme_optimizer_support_finite_card_le A hA hC hCpos
      hAC w v hw hvmax ν hνext).1
    let T := (μ : Measure Θ).support ∪ (ν : Measure Θ).support
    have hTfinite : T.Finite := hμfinite.union hνfinite
    letI : Fintype T := hTfinite.fintype
    let k := Fintype.card T
    let e : Fin k ≃ T := (Fintype.equivFin T).symm
    let θ : Fin k → Θ := fun j ↦ (e j).val
    have hθ : Function.Injective θ := fun j l hjl ↦ e.injective (Subtype.ext hjl)
    have hRange : range θ = T := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact (e j).property
      · intro hx
        refine ⟨e.symm ⟨x, hx⟩, ?_⟩
        exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)
    have hk : k ≤ L := by
      have hcard : k = T.ncard := by
        change Fintype.card T = T.ncard
        rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
      rw [hcard]
      exact (ncard_union_le _ _).trans
        ((Nat.add_le_add (hsmall μ hμext) (hsmall ν hνext)).trans (by omega))
    have hμAE : ∀ᵐ x ∂(μ : Measure Θ), x ∈ range θ := by
      rw [hRange]
      filter_upwards [(μ : Measure Θ).support_mem_ae] with x hx
      exact Or.inl hx
    have hνAE : ∀ᵐ x ∂(ν : Measure Θ), x ∈ range θ := by
      rw [hRange]
      filter_upwards [(ν : Measure Θ).support_mem_ae] with x hx
      exact Or.inr hx
    exact probabilityMixtureFiber_unique_of_supported_independent_range A hA v θ (hind k hk θ hθ)
      μ ν (isExtremeProbabilityMixture_mem_fiber A v μ hμext)
      (isExtremeProbabilityMixture_mem_fiber A v ν hνext) hμAE hνAE
  obtain ⟨μ, hfiber, hext⟩ := probabilityMixtureFiber_eq_singleton_of_extreme_unique
    A hA v hvHull hunique
  exact ⟨μ, hfiber, hext, (full_extreme_optimizer_support_finite_card_le A hA hC hCpos
    hAC w v hw hvmax μ hext).1, hsmall μ hext⟩

end ReweightedNPMLE
