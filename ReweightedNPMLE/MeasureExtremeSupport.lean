import ReweightedNPMLE.FullExtremeSupport
import ReweightedNPMLE.ExtremeSupport
import Mathlib.Tactic

/-!
# Maximum support of full probability-measure extreme optimizers

The statistic is defined directly from arbitrary probability measures, not
from finite representations. The full extreme-optimizer characterization
identifies each cardinality event with the independent representation event.
Consequently its supremum is a measurable, attained maximum bounded by `n`.
-/

open Set MeasureTheory
open scoped BigOperators Topology

namespace ReweightedNPMLE

/-- Positive weights admitting a full-fiber extreme law of support size `k`. -/
def fullExtremeSupportEvent {Θ : Type*} [TopologicalSpace Θ] [MeasurableSpace Θ]
    {n : ℕ} (A : Θ → Fin n → ℝ)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ)) (k : ℕ) : Set (Fin n → ℝ) :=
  {w | w ∈ positiveVectors n ∧ ∃ μ : ProbabilityMeasure Θ,
    IsExtremeProbabilityMixture A (vhat w) μ ∧ (μ : Measure Θ).support.ncard = k}

/-- The paper's maximum extreme-optimizer support statistic, extended by zero
outside positive weights. Finiteness and attainment are proved below. -/
noncomputable def maximumExtremeSupport {Θ : Type*}
    [TopologicalSpace Θ] [MeasurableSpace Θ] {n : ℕ}
    (A : Θ → Fin n → ℝ) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (w : Fin n → ℝ) : ℕ :=
  sSup {k | w ∈ fullExtremeSupportEvent A vhat k}

theorem maximumIndependentSupport_eq_sSup {n : ℕ}
    (D : Set (Fin n → ℝ)) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (w : Fin n → ℝ) :
    maximumIndependentSupport D vhat w =
      sSup {k | w ∈ independentRepresentationEvent D vhat k} := by
  let S : Set ℕ := {k | w ∈ independentRepresentationEvent D vhat k}
  have hbounded : BddAbove S := ⟨n, fun k hk ↦ independentRepresentationEvent_size_le D vhat hk⟩
  apply le_antisymm
  · by_cases hpos : 0 < maximumIndependentSupport D vhat w
    · exact le_csSup hbounded (maximumIndependentSupport_mem_of_pos D vhat hpos)
    · have hz : maximumIndependentSupport D vhat w = 0 := by omega
      rw [hz]
      exact Nat.zero_le _
  · exact csSup_le' (fun k hk ↦ le_maximumIndependentSupport_of_mem D vhat hk)

theorem fullExtremeSupportEvent_eq_independentRepresentationEvent {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hvmax : ∀ w ∈ positiveVectors n, IsMaxOn C (weightedLogLikelihood w) (vhat w))
    (k : ℕ) :
    fullExtremeSupportEvent A vhat k = independentRepresentationEvent (range A) vhat k := by
  classical
  ext w
  constructor
  · rintro ⟨hw, μ, hext, hk⟩
    obtain ⟨m, θ, p, hp, hm, hθ, hpPos, hlin, hpval, heq⟩ :=
      (full_probability_optimizer_extreme_iff A hA hC hCpos hAC w (vhat w) hw
        (hvmax w hw) μ).mp hext
    have hmcard : (μ : Measure Θ).support.ncard = m := by
      rw [← heq, finiteProbabilityMeasure_support θ hθ p hp hpPos]
      simpa using ncard_range_of_injective hθ
    have hmk : m = k := hmcard.symm.trans hk
    rw [← hmk]
    refine ⟨hw, A ∘ θ, ?_, hlin, p, hp, hpPos, hpval⟩
    rintro a ⟨j, rfl⟩
    exact mem_range_self (θ j)
  · rintro ⟨hw, B, hB, hlin, p, hp, hpPos, hpval⟩
    have hpre : ∀ j, ∃ θ : Θ, A θ = B j := fun j ↦ hB (mem_range_self j)
    choose θ hθval using hpre
    have hcomp : A ∘ θ = B := funext hθval
    have hθ : Function.Injective θ := by
      intro j l hjl
      apply hlin.injective
      rw [← hθval j, ← hθval l, hjl]
    let μ := finiteProbabilityMeasure θ p hp
    refine ⟨hw, μ, ?_, ?_⟩
    · have hext := finiteProbabilityMeasure_extreme_of_linearIndependent A hA θ p hp
        (hcomp.symm ▸ hlin)
      simpa only [hcomp, hpval] using hext
    · change (finiteProbabilityMeasure θ p hp : Measure Θ).support.ncard = k
      rw [finiteProbabilityMeasure_support θ hθ p hp hpPos]
      simpa using ncard_range_of_injective hθ

theorem maximumExtremeSupport_eq_maximumIndependentSupport {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hvmax : ∀ w ∈ positiveVectors n, IsMaxOn C (weightedLogLikelihood w) (vhat w))
    (w : Fin n → ℝ) :
    maximumExtremeSupport A vhat w = maximumIndependentSupport (range A) vhat w := by
  rw [maximumIndependentSupport_eq_sSup]
  unfold maximumExtremeSupport
  congr 1
  ext k
  change (w ∈ fullExtremeSupportEvent A vhat k) ↔
    (w ∈ independentRepresentationEvent (range A) vhat k)
  rw [fullExtremeSupportEvent_eq_independentRepresentationEvent A hA hC hCpos hAC vhat hvmax k]

theorem measurable_maximumExtremeSupport {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hvmax : ∀ w ∈ positiveVectors n, IsMaxOn C (weightedLogLikelihood w) (vhat w))
    (hvcont : ContinuousOn vhat (positiveVectors n)) :
    Measurable (maximumExtremeSupport A vhat) := by
  have heq : maximumExtremeSupport A vhat = maximumIndependentSupport (range A) vhat :=
    funext (maximumExtremeSupport_eq_maximumIndependentSupport A hA hC hCpos hAC vhat hvmax)
  rw [heq]
  exact measurable_maximumIndependentSupport (range A) (isCompact_range hA).isClosed vhat hvcont

theorem full_extreme_optimizer_support_le_maximum {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hvmax : ∀ w ∈ positiveVectors n, IsMaxOn C (weightedLogLikelihood w) (vhat w))
    (w : Fin n → ℝ) (hw : w ∈ positiveVectors n)
    (μ : ProbabilityMeasure Θ) (hext : IsExtremeProbabilityMixture A (vhat w) μ) :
    (μ : Measure Θ).support.Finite ∧
      (μ : Measure Θ).support.ncard ≤ maximumExtremeSupport A vhat w := by
  have hfinite := full_extreme_optimizer_support_finite_card_le A hA hC hCpos hAC
    w (vhat w) hw (hvmax w hw) μ hext
  have hevent : w ∈ fullExtremeSupportEvent A vhat (μ : Measure Θ).support.ncard :=
    ⟨hw, μ, hext, rfl⟩
  rw [fullExtremeSupportEvent_eq_independentRepresentationEvent A hA hC hCpos hAC
    vhat hvmax] at hevent
  rw [maximumExtremeSupport_eq_maximumIndependentSupport A hA hC hCpos hAC vhat hvmax w]
  exact ⟨hfinite.1, le_maximumIndependentSupport_of_mem (range A) vhat hevent⟩

theorem canonical_maximumExtremeSupport_attained {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (hChull : C ⊆ convexHull ℝ (range A))
    (w : Fin n → ℝ) (hw : w ∈ positiveVectors n) :
    let vhat := fittedValueSelection C hCcompact hCnonempty hCpos
    0 < maximumExtremeSupport A vhat w ∧ maximumExtremeSupport A vhat w ≤ n ∧
      ∃ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A (vhat w) μ ∧
        (μ : Measure Θ).support.ncard = maximumExtremeSupport A vhat w := by
  dsimp only
  let vhat := fittedValueSelection C hCcompact hCnonempty hCpos
  have hvmax : ∀ w ∈ positiveVectors n, IsMaxOn C (weightedLogLikelihood w) (vhat w) :=
    fun w _ ↦ fittedValueSelection_isMax C hCcompact hCnonempty hCpos w
  have heq := maximumExtremeSupport_eq_maximumIndependentSupport A hA hC hCpos hAC vhat hvmax w
  have hpos := maximumIndependentSupport_pos_of_mem_convexHull C hC hCcompact hCnonempty
    hCpos (range A) hAC w hw (hChull (hvmax w hw).1)
  have hevent := maximumIndependentSupport_mem_of_pos (range A) vhat hpos
  rw [← fullExtremeSupportEvent_eq_independentRepresentationEvent A hA hC hCpos hAC
    vhat hvmax] at hevent
  rw [← heq] at hevent hpos
  exact ⟨hpos, heq.trans_le (maximumIndependentSupport_le (range A) vhat w), hevent.2⟩

end ReweightedNPMLE
