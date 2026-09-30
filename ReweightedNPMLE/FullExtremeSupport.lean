import ReweightedNPMLE.ExtremeSupportPartition
import ReweightedNPMLE.FiniteProbabilityExtreme
import Mathlib.Data.Set.Card
import Mathlib.Tactic

/-!
# Finite support of every full-measure extreme optimizer

Distinct support points have disjoint positive-mass metric neighborhoods.
The partition perturbation theorem excludes more than `n` such points,
including infinitely many support points. Consequently every full-fiber
extreme optimizer has finite topological support of cardinality at most `n`.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE

theorem exists_disjoint_open_neighborhoods_of_finite_injective {Θ : Type*}
    [MetricSpace Θ] {m : ℕ} [Nonempty (Fin m)]
    (θ : Fin m → Θ) (hθ : Function.Injective θ) :
    ∃ E : Fin m → Set Θ, (∀ j, IsOpen (E j) ∧ θ j ∈ E j) ∧
      Pairwise (fun j k ↦ Disjoint (E j) (E k)) := by
  classical
  let d : Fin m × Fin m → ℝ := fun p ↦ if p.1 = p.2 then 1 else dist (θ p.1) (θ p.2)
  have hd : ∀ p, 0 < d p := by
    intro p
    dsimp [d]
    split_ifs with h
    · norm_num
    · exact dist_pos.mpr (fun hh ↦ h (hθ hh))
  let S : Finset ℝ := Finset.univ.image d
  have hSne : S.Nonempty := Finset.univ_nonempty.image d
  let δ := S.min' hSne
  have hδ : 0 < δ := by
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp (Finset.min'_mem S hSne)
    dsimp only [δ]
    rw [← heq]
    exact hd p
  have hδle : ∀ j k, δ ≤ d (j, k) := fun j k ↦
    Finset.min'_le S (d (j, k)) (Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, rfl⟩)
  refine ⟨fun j ↦ Metric.ball (θ j) (δ / 3), ?_, ?_⟩
  · intro j
    exact ⟨Metric.isOpen_ball, Metric.mem_ball_self (by positivity)⟩
  · intro j k hjk
    have hh := hδle j k
    dsimp [d] at hh
    rw [if_neg hjk] at hh
    exact Metric.ball_disjoint_ball (by linarith)

theorem full_extreme_optimizer_no_large_injective_support {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {m n : ℕ} [Nonempty (Fin n)] (hmn : n < m)
    (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v)
    (μ : ProbabilityMeasure Θ) (hext : IsExtremeProbabilityMixture A v μ)
    (θ : Fin m → Θ) (hθ : Function.Injective θ)
    (hθS : ∀ j, θ j ∈ (μ : Measure Θ).support) : False := by
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (by omega)
  obtain ⟨E, hE, hEd⟩ := exists_disjoint_open_neighborhoods_of_finite_injective θ hθ
  have hEpos : ∀ j, 0 < (μ : Measure Θ) (E j) := fun j ↦
    (Measure.mem_support_iff_forall (θ j)).mp (hθS j) (E j) ((hE j).1.mem_nhds (hE j).2)
  exact probability_optimizer_not_extreme_of_disjoint_positive_regions hmn A hA hC hCpos hAC
    w v hw hvmax μ (isExtremeProbabilityMixture_mem_fiber A v μ hext) E
    (fun j ↦ (hE j).1.measurableSet) hEd hEpos hext

theorem full_extreme_optimizer_support_finite_card_le {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v)
    (μ : ProbabilityMeasure Θ) (hext : IsExtremeProbabilityMixture A v μ) :
    (μ : Measure Θ).support.Finite ∧ (μ : Measure Θ).support.ncard ≤ n := by
  classical
  let T := (μ : Measure Θ).support
  have hfinite : T.Finite := by
    by_contra hinfinite
    letI : Infinite T := Set.infinite_coe_iff.mpr hinfinite
    let e := Infinite.natEmbedding T
    let θ : Fin (n + 1) → Θ := fun j ↦ (e j.val).val
    have hθ : Function.Injective θ := by
      intro j k hjk
      apply Fin.ext
      exact e.injective (Subtype.ext hjk)
    exact full_extreme_optimizer_no_large_injective_support (Nat.lt_succ_self n)
      A hA hC hCpos hAC w v hw hvmax μ hext θ hθ (fun j ↦ (e j.val).property)
  letI : Fintype T := hfinite.fintype
  have hcard : Fintype.card T ≤ n := by
    by_contra hle
    let e : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
    let θ : Fin (Fintype.card T) → Θ := fun j ↦ (e j).val
    have hθ : Function.Injective θ := fun j k hjk ↦ e.injective (Subtype.ext hjk)
    exact full_extreme_optimizer_no_large_injective_support (lt_of_not_ge hle)
      A hA hC hCpos hAC w v hw hvmax μ hext θ hθ (fun j ↦ (e j).property)
  refine ⟨hfinite, ?_⟩
  change T.ncard ≤ n
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact hcard

theorem measure_support_singleton_pos_of_finite_support {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (μ : Measure Θ) (hs : μ.support.Finite) (x : Θ) (hx : x ∈ μ.support) :
    0 < μ {x} := by
  by_contra hpos
  have hzero : μ {x} = 0 := le_antisymm (not_lt.mp hpos) bot_le
  have hAE : ∀ᵐ a ∂μ, a ∈ μ.support \ {x} := by
    filter_upwards [μ.support_mem_ae, measure_eq_zero_iff_ae_notMem.mp hzero] with a ha hax
    exact ⟨ha, hax⟩
  have hsub := μ.support_subset_of_isClosed (hs.diff (t := {x})).isClosed hAE
  have hh := hsub hx
  exact hh.2 (mem_singleton x)

theorem probabilityMeasure_positive_finiteRepresentation_of_finite_support {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    (μ : ProbabilityMeasure Θ) (hs : (μ : Measure Θ).support.Finite) :
    ∃ (k : ℕ) (θ : Fin k → Θ) (p : Fin k → ℝ) (hp : p ∈ finiteSimplex k),
      k = (μ : Measure Θ).support.ncard ∧ Function.Injective θ ∧
      range θ = (μ : Measure Θ).support ∧ (∀ j, 0 < p j) ∧ finiteProbabilityMeasure θ p hp = μ := by
  classical
  let T := (μ : Measure Θ).support
  letI : Fintype T := hs.fintype
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
  have hAE : ∀ᵐ x ∂(μ : Measure Θ), x ∈ range θ := by
    rw [hRange]
    exact (μ : Measure Θ).support_mem_ae
  obtain ⟨p, hp, heq⟩ := probabilityMeasure_finiteRepresentation_of_ae_mem_range θ hθ μ hAE
  have hpPos : ∀ j, 0 < p j := by
    intro j
    have hj : 0 < (finiteProbabilityMeasure θ p hp : Measure Θ) {θ j} := by
      rw [heq]
      exact measure_support_singleton_pos_of_finite_support (μ : Measure Θ) hs (θ j) (e j).property
    rw [finiteProbabilityMeasure_singleton_mass θ hθ p hp] at hj
    exact ENNReal.ofReal_pos.mp hj
  refine ⟨k, θ, p, hp, ?_, hθ, hRange, hpPos, heq⟩
  change Fintype.card T = T.ncard
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

/-- The complete full-measure extreme-optimizer characterization. In
particular, finite support and the `n`-atom bound are conclusions, not
hypotheses. -/
theorem full_probability_optimizer_extreme_iff {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v)
    (μ : ProbabilityMeasure Θ) :
    IsExtremeProbabilityMixture A v μ ↔
      ∃ (k : ℕ) (θ : Fin k → Θ) (p : Fin k → ℝ) (hp : p ∈ finiteSimplex k),
        k ≤ n ∧ Function.Injective θ ∧ (∀ j, 0 < p j) ∧ LinearIndependent ℝ (A ∘ θ) ∧
          finiteMixtureValue (A ∘ θ) p = v ∧ finiteProbabilityMeasure θ p hp = μ := by
  constructor
  · intro hext
    have hμ := isExtremeProbabilityMixture_mem_fiber A v μ hext
    have hsupport := full_extreme_optimizer_support_finite_card_le A hA hC hCpos hAC w v hw hvmax μ hext
    obtain ⟨k, θ, p, hp, hkcard, hθ, hRange, hpPos, heq⟩ :=
      probabilityMeasure_positive_finiteRepresentation_of_finite_support μ hsupport.1
    have hpval : finiteMixtureValue (A ∘ θ) p = v := by
      rw [← probabilityMixtureValue_finiteProbabilityMeasure A hA θ p hp, heq]
      exact hμ
    have hpf : p ∈ finiteMixtureFiber (A ∘ θ) v := ⟨hp, hpval⟩
    have hvHull : v ∈ convexHull ℝ (range (A ∘ θ)) :=
      mem_convexHull_iff_exists_fintype.mpr
        ⟨Fin k, inferInstance, p, A ∘ θ, hp.1, hp.2, (fun j ↦ mem_range_self j), hpval⟩
    have hHullC : convexHull ℝ (range (A ∘ θ)) ⊆ C :=
      convexHull_min (fun a ha ↦ by rcases ha with ⟨j, rfl⟩; exact hAC (mem_range_self (θ j))) hC
    have hvmaxFinite : IsMaxOn (convexHull ℝ (range (A ∘ θ))) (weightedLogLikelihood w) v :=
      ⟨hvHull, fun a ha ↦ hvmax.2 a (hHullC ha)⟩
    have hextFinite : IsExtremeProbabilityMixture A v (finiteProbabilityMeasure θ p hpf.1) := by
      simpa only [heq] using hext
    have hlin := (finite_probability_optimizer_extreme_iff_linearIndependent A hA θ hθ v p hpf hpPos
      w hw (hCpos hvmax.1) (fun j ↦ hCpos (hAC (mem_range_self (θ j)))) hvmaxFinite).mp hextFinite
    exact ⟨k, θ, p, hp, hkcard ▸ hsupport.2, hθ, hpPos, hlin, hpval, heq⟩
  · rintro ⟨k, θ, p, hp, hk, hθ, hpPos, hlin, hpval, heq⟩
    have hext := finiteProbabilityMeasure_extreme_of_linearIndependent A hA θ p hp hlin
    simpa only [hpval, heq] using hext

end ReweightedNPMLE
