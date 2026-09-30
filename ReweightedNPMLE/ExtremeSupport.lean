import ReweightedNPMLE.SupportSensitivityAnalytic
import ReweightedNPMLE.Caratheodory
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.LocallyClosed
import Mathlib.Tactic

/-!
# Maximum independent optimizer support

This file defines the maximum cardinality of independent full-support finite
representations of a fitted vector.  The fixed-cardinality representation
events are measurable because their parameter sets are locally closed in
second-countable locally compact spaces and hence sigma-compact.  Projection
preserves sigma-compactness.  The maximum is attained when positive, is at
most the ambient dimension, and satisfies the canonical support-sensitivity
Jacobian bound.  Its identification with extreme mixing-measure supports is
a separate optimizer-fiber statement.
-/

open Set Filter MeasureTheory Matrix
open scoped BigOperators Topology

namespace ReweightedNPMLE

/-- Positive weights at which the fitted vector admits an independent
full-support representation using exactly `k` dictionary vectors. -/
def independentRepresentationEvent {n : ℕ}
    (D : Set (Fin n → ℝ)) (vhat : (Fin n → ℝ) → (Fin n → ℝ)) (k : ℕ) :
    Set (Fin n → ℝ) :=
  {w | w ∈ positiveVectors n ∧ ∃ A : Fin k → Fin n → ℝ,
    Set.range A ⊆ D ∧ LinearIndependent ℝ A ∧
      ∃ p : Fin k → ℝ, p ∈ finiteSimplex k ∧ (∀ j, 0 < p j) ∧
        finiteMixtureValue A p = vhat w}

theorem measurableSet_independentRepresentationEvent {n : ℕ}
    (D : Set (Fin n → ℝ)) (hDclosed : IsClosed D)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hvcont : ContinuousOn vhat (positiveVectors n)) (k : ℕ) :
    MeasurableSet (independentRepresentationEvent D vhat k) := by
  let U := positiveVectors n
  letI : LocallyCompactSpace U := (isOpen_positiveVectors n).locallyCompactSpace
  let X := U × ((Fin k → Fin n → ℝ) × (Fin k → ℝ))
  let O : Set X := {x | LinearIndependent ℝ x.2.1 ∧ x.2.2 ∈ positiveVectors k}
  let Z : Set X := {x | (∀ j, x.2.1 j ∈ D) ∧ x.2.2 ∈ finiteSimplex k ∧
    finiteMixtureValue x.2.1 x.2.2 = vhat x.1.val}
  have hO : IsOpen O := by
    exact (isOpen_setOf_linearIndependent.preimage
      (continuous_fst.comp continuous_snd)).inter
      ((isOpen_positiveVectors k).preimage (continuous_snd.comp continuous_snd))
  have hZ : IsClosed Z := by
    have hA : IsClosed {x : X | ∀ j, x.2.1 j ∈ D} := by
      have heq : {x : X | ∀ j, x.2.1 j ∈ D} = ⋂ j : Fin k, {x : X | x.2.1 j ∈ D} := by
        ext x
        simp
      rw [heq]
      exact isClosed_iInter fun j ↦ hDclosed.preimage
        ((continuous_apply j).comp (continuous_fst.comp continuous_snd))
    have hp : IsClosed {x : X | x.2.2 ∈ finiteSimplex k} :=
      (isCompact_finiteSimplex k).isClosed.preimage (continuous_snd.comp continuous_snd)
    have hf : Continuous (fun x : X ↦ finiteMixtureValue x.2.1 x.2.2) := by
      unfold finiteMixtureValue
      fun_prop
    have hg : Continuous (fun x : X ↦ vhat x.1.val) :=
      (continuousOn_iff_continuous_restrict.mp hvcont).comp continuous_fst
    exact hA.inter (hp.inter (isClosed_eq hf hg))
  let S := O ∩ Z
  have hSloc : IsLocallyClosed S := hO.isLocallyClosed.inter hZ.isLocallyClosed
  letI : LocallyCompactSpace S := hSloc.locallyCompactSpace
  have hsigma : IsSigmaCompact S := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  let f : X → Fin n → ℝ := fun x ↦ x.1.val
  have himage : IsSigmaCompact (f '' S) := hsigma.image (continuous_subtype_val.comp continuous_fst)
  have heq : independentRepresentationEvent D vhat k = f '' S := by
    ext w
    constructor
    · rintro ⟨hw, A, hA, hlin, p, hp, hpfull, hvalue⟩
      refine ⟨(⟨w, hw⟩, A, p), ?_, rfl⟩
      exact ⟨⟨hlin, hpfull⟩, (fun j ↦ hA (mem_range_self j)), hp, hvalue⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.1.property, x.2.1, ?_, hx.1.1, x.2.2, hx.2.2.1, hx.1.2, hx.2.2.2⟩
      rintro a ⟨j, rfl⟩
      exact hx.2.1 j
  obtain ⟨K, hK, hKeq⟩ := himage
  rw [heq, ← hKeq]
  exact MeasurableSet.iUnion fun m ↦ (hK m).measurableSet

/-- Maximum independent full-support representation size.  Its value is
zero when no such representation exists (in particular outside the positive
orthant). -/
noncomputable def maximumIndependentSupport {n : ℕ}
    (D : Set (Fin n → ℝ)) (vhat : (Fin n → ℝ) → (Fin n → ℝ)) (w : Fin n → ℝ) : ℕ := by
  classical
  exact (Finset.range (n + 1)).sup
    (fun k ↦ if w ∈ independentRepresentationEvent D vhat k then k else 0)

theorem measurable_maximumIndependentSupport {n : ℕ}
    (D : Set (Fin n → ℝ)) (hDclosed : IsClosed D)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hvcont : ContinuousOn vhat (positiveVectors n)) :
    Measurable (maximumIndependentSupport D vhat) := by
  classical
  have hsup : ∀ s : Finset ℕ, Measurable (fun w : Fin n → ℝ ↦
      s.sup (fun k ↦ if w ∈ independentRepresentationEvent D vhat k then k else 0)) := by
    intro s
    induction s using Finset.induction with
    | empty => simpa using (measurable_const : Measurable (fun _ : Fin n → ℝ ↦ (0 : ℕ)))
    | @insert k s hk ih =>
      simp only [Finset.sup_insert]
      exact (Measurable.ite (measurableSet_independentRepresentationEvent D hDclosed vhat hvcont k)
        measurable_const measurable_const).sup ih
  exact hsup (Finset.range (n + 1))

theorem maximumIndependentSupport_le {n : ℕ}
    (D : Set (Fin n → ℝ)) (vhat : (Fin n → ℝ) → (Fin n → ℝ)) (w : Fin n → ℝ) :
    maximumIndependentSupport D vhat w ≤ n := by
  classical
  apply Finset.sup_le
  intro k hk
  split_ifs
  · exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  · exact Nat.zero_le n

theorem independentRepresentationEvent_size_le {n k : ℕ}
    (D : Set (Fin n → ℝ)) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {w : Fin n → ℝ} (hw : w ∈ independentRepresentationEvent D vhat k) : k ≤ n := by
  obtain ⟨_, A, _, hlin, _⟩ := hw
  simpa using hlin.fintype_card_le_finrank

theorem le_maximumIndependentSupport_of_mem {n k : ℕ}
    (D : Set (Fin n → ℝ)) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {w : Fin n → ℝ} (hw : w ∈ independentRepresentationEvent D vhat k) :
    k ≤ maximumIndependentSupport D vhat w := by
  classical
  have hk := independentRepresentationEvent_size_le D vhat hw
  have hh := Finset.le_sup (s := Finset.range (n + 1))
    (f := fun j ↦ if w ∈ independentRepresentationEvent D vhat j then j else 0)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  simpa [maximumIndependentSupport, hw] using hh

theorem maximumIndependentSupport_mem_of_pos {n : ℕ}
    (D : Set (Fin n → ℝ)) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {w : Fin n → ℝ} (hw : 0 < maximumIndependentSupport D vhat w) :
    w ∈ independentRepresentationEvent D vhat (maximumIndependentSupport D vhat w) := by
  classical
  let f : ℕ → ℕ := fun k ↦ if w ∈ independentRepresentationEvent D vhat k then k else 0
  have hne : (Finset.range (n + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨k, hk, heq⟩ := (Finset.sup_mem_of_nonempty (f := f) hne)
  have hkevent : w ∈ independentRepresentationEvent D vhat k := by
    by_contra hn
    have hz : f k = 0 := by simp [f, hn]
    change 0 < (Finset.range (n + 1)).sup f at hw
    rw [← heq, hz] at hw
    omega
  have hkeq : k = maximumIndependentSupport D vhat w := by
    simpa [f, maximumIndependentSupport, hkevent] using heq
  simpa [← hkeq] using hkevent

theorem canonical_maximumIndependentSupport_jacobian_determinant_lower
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (D : Set (Fin n → ℝ)) (hD : D ⊆ C)
    (w : Fin n → ℝ) (hw : w ∈ positiveVectors n)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fittedLogSelection C hCcompact hCnonempty hCpos) J w)
    (a : Fin n → ℝ) (ha0 : ∀ i, 0 < a i) (haUpper : ∀ i, a i ≤ 9 / 8) :
    (∏ i, a i) * (17 / 9 : ℝ) ^
      (maximumIndependentSupport D (fittedValueSelection C hCcompact hCnonempty hCpos) w - 1) ≤
      (Matrix.diagonal a + Matrix.diagonal w * fittedLogDerivativeMatrix J).det := by
  classical
  let m := maximumIndependentSupport D (fittedValueSelection C hCcompact hCnonempty hCpos) w
  by_cases hm : 0 < m
  · obtain ⟨_, A, hA, hlin, p, hp, hpfull, hpvalue⟩ :=
      maximumIndependentSupport_mem_of_pos D
        (fittedValueSelection C hCcompact hCnonempty hCpos) hm
    have hpFiber : p ∈ finiteMixtureFiber A
        (fittedValueSelection C hCcompact hCnonempty hCpos w) := ⟨hp, hpvalue⟩
    have hsupport : (coefficientSupport p : Set (Fin m)) = univ := by
      ext j
      simp [ne_of_gt (hpfull j)]
    have hlinOn : LinearIndepOn ℝ A (coefficientSupport p : Set (Fin m)) := by
      rw [hsupport]
      exact linearIndepOn_univ_iff.mpr hlin
    have hext := finiteMixtureFiber_extreme_of_linearIndepOn A _ p hpFiber hlinOn
    letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact canonical_finite_extreme_optimizer_jacobian_determinant_lower
      C hC hCcompact hCnonempty hCpos A (hA.trans hD) p w hw hpFiber hpfull hext hz
        a ha0 haUpper
  · have hmzero : m = 0 := by omega
    have hJ := fittedLogDerivativeMatrix_posSemidef_of_eventually
      (fittedValueSelection C hCcompact hCnonempty hCpos)
      (fun q ↦ fittedValueSelection_isMax C hCcompact hCnonempty hCpos q)
      (fittedOptimalValue (fittedValueSelection C hCcompact hCnonempty hCpos))
      (eventually_canonicalFittedOptimalValue_hasFDerivAt_of_positive_weights
        C hC hCcompact hCnonempty hCpos w hw) hz
    let W : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i ↦ Real.sqrt (w i))
    have hW : Wᴴ = W := (Matrix.isHermitian_diagonal _).eq
    have hR := hJ.conjTranspose_mul_mul_same W
    rw [hW] at hR
    rw [det_diagonal_add_weight_mul_eq_sqrt_conj w a hw]
    have hd := det_mono_of_posDef_of_sub_posSemidef
      (B := Matrix.diagonal a + W * fittedLogDerivativeMatrix J * W)
      (Matrix.posDef_diagonal_iff.mpr ha0)
      (by simpa using hR)
    change (∏ i, a i) * (17 / 9 : ℝ) ^ (m - 1) ≤ _
    simpa [Matrix.det_diagonal, hmzero, W] using hd

theorem exists_independentRepresentationEvent_of_mem_convexHull
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (D : Set (Fin n → ℝ)) (hD : D ⊆ C)
    (w : Fin n → ℝ) (hw : w ∈ positiveVectors n)
    (hvHull : fittedValueSelection C hCcompact hCnonempty hCpos w ∈ convexHull ℝ D) :
    ∃ k : ℕ, w ∈ independentRepresentationEvent D
      (fittedValueSelection C hCcompact hCnonempty hCpos) k := by
  classical
  let v := fittedValueSelection C hCcompact hCnonempty hCpos w
  obtain ⟨ι, hι, p₀, A₀, hp₀, hpsum₀, hA₀, hvalue₀⟩ :=
    mem_convexHull_iff_exists_fintype.mp hvHull
  letI : Fintype ι := hι
  let m := Fintype.card ι
  let e : Fin m ≃ ι := (Fintype.equivFin ι).symm
  let A : Fin m → Fin n → ℝ := fun j ↦ A₀ (e j)
  let p : Fin m → ℝ := fun j ↦ p₀ (e j)
  have hp : p ∈ finiteMixtureFiber A v := by
    refine ⟨⟨fun j ↦ hp₀ (e j), ?_⟩, ?_⟩
    · exact (e.sum_comp p₀).trans hpsum₀
    · exact (e.sum_comp (fun j ↦ p₀ j • A₀ j)).trans hvalue₀
  have hA : Set.range A ⊆ D := by
    rintro a ⟨j, rfl⟩
    exact hA₀ (e j)
  obtain ⟨q, hqExt⟩ := (isCompact_finiteMixtureFiber A v).extremePoints_nonempty ⟨p, hp⟩
  have hq : q ∈ finiteMixtureFiber A v := hqExt.1
  have hvmax : IsMaxOn (convexHull ℝ (Set.range A)) (weightedLogLikelihood w) v := by
    refine ⟨?_, ?_⟩
    · rw [← hp.2]
      exact finiteMixtureValue_mem_convexHull_of_mem_finiteSimplex A p hp.1
    · intro b hb
      exact (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).2 b
        (convexHull_min (hA.trans hD) hC hb)
  have hlin := (finite_likelihood_optimizer_extreme_iff_linearIndepOn
    A v q w hw hq (hCpos (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).1)
    (fun j ↦ hCpos (hD (hA (mem_range_self j)))) hvmax).mp hqExt
  let S := coefficientSupport q
  let k := Fintype.card S
  let f : Fin k ≃ S := (Fintype.equivFin S).symm
  let B : Fin k → Fin n → ℝ := fun j ↦ A (f j)
  let r : Fin k → ℝ := fun j ↦ q (f j)
  have hsum : (∑ j : S, q j) = 1 := by
    calc
      (∑ j : S, q j) = ∑ j ∈ S, q j := Finset.sum_coe_sort S q
      _ = ∑ j, q j := Finset.sum_subset (Finset.subset_univ S)
        (fun j _ hj ↦ (not_mem_coefficientSupport_iff q j).mp hj)
      _ = 1 := hq.1.2
  have hvalue : (∑ j : S, q j • A j) = v := by
    calc
      (∑ j : S, q j • A j) = ∑ j ∈ S, q j • A j :=
        Finset.sum_coe_sort S (fun j ↦ q j • A j)
      _ = ∑ j, q j • A j := Finset.sum_subset (Finset.subset_univ S)
        (fun j _ hj ↦ by rw [(not_mem_coefficientSupport_iff q j).mp hj, zero_smul])
      _ = v := hq.2
  have hBlin : LinearIndependent ℝ B := hlin.comp f f.injective
  refine ⟨k, hw, B, ?_, hBlin, r, ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro b ⟨j, rfl⟩
    exact hA ⟨(f j).val, rfl⟩
  · intro j
    exact hq.1.1 (f j)
  · exact (f.sum_comp (fun j : S ↦ q j)).trans hsum
  · intro j
    exact lt_of_le_of_ne (hq.1.1 (f j))
      (Ne.symm ((mem_coefficientSupport q (f j)).mp (f j).property))
  · exact (f.sum_comp (fun j : S ↦ q j • A j)).trans hvalue

theorem independentRepresentationEvent_size_pos {n k : ℕ}
    (D : Set (Fin n → ℝ)) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {w : Fin n → ℝ} (hw : w ∈ independentRepresentationEvent D vhat k) : 0 < k := by
  obtain ⟨_, A, _, _, p, hp, _, _⟩ := hw
  apply Nat.pos_of_ne_zero
  intro hk
  letI : IsEmpty (Fin k) := ⟨fun i ↦ Nat.not_lt_zero i.val (hk ▸ i.isLt)⟩
  have hh := hp.2
  simp at hh

theorem maximumIndependentSupport_pos_of_mem_convexHull
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (D : Set (Fin n → ℝ)) (hD : D ⊆ C)
    (w : Fin n → ℝ) (hw : w ∈ positiveVectors n)
    (hvHull : fittedValueSelection C hCcompact hCnonempty hCpos w ∈ convexHull ℝ D) :
    0 < maximumIndependentSupport D (fittedValueSelection C hCcompact hCnonempty hCpos) w := by
  obtain ⟨k, hk⟩ := exists_independentRepresentationEvent_of_mem_convexHull
    C hC hCcompact hCnonempty hCpos D hD w hw hvHull
  exact (independentRepresentationEvent_size_pos D _ hk).trans_le
    (le_maximumIndependentSupport_of_mem D _ hk)

theorem independentRepresentationEvent_iff_extreme_finite_representation
    {n k : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (D : Set (Fin n → ℝ)) (hD : D ⊆ C)
    (w : Fin n → ℝ) (hw : w ∈ positiveVectors n) :
    w ∈ independentRepresentationEvent D (fittedValueSelection C hCcompact hCnonempty hCpos) k ↔
      ∃ (A : Fin k → Fin n → ℝ) (p : Fin k → ℝ),
        Set.range A ⊆ D ∧ (∀ j, 0 < p j) ∧
        p ∈ (finiteMixtureFiber A
          (fittedValueSelection C hCcompact hCnonempty hCpos w)).extremePoints ℝ := by
  classical
  let v := fittedValueSelection C hCcompact hCnonempty hCpos w
  constructor
  · rintro ⟨_, A, hA, hlin, p, hp, hpfull, hvalue⟩
    refine ⟨A, p, hA, hpfull, finiteMixtureFiber_extreme_of_linearIndepOn A v p ⟨hp, hvalue⟩ ?_⟩
    have hsupport : (coefficientSupport p : Set (Fin k)) = univ := by
      ext j
      simp [(hpfull j).ne']
    rw [hsupport]
    exact linearIndepOn_univ_iff.mpr hlin
  · rintro ⟨A, p, hA, hpfull, hext⟩
    have hp : p ∈ finiteMixtureFiber A v := hext.1
    have hvmax : IsMaxOn (convexHull ℝ (Set.range A)) (weightedLogLikelihood w) v := by
      refine ⟨?_, ?_⟩
      · rw [← hp.2]
        exact finiteMixtureValue_mem_convexHull_of_mem_finiteSimplex A p hp.1
      · intro b hb
        exact (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).2 b
          (convexHull_min (hA.trans hD) hC hb)
    have hlin := (finite_likelihood_optimizer_extreme_iff_linearIndepOn
      A v p w hw hp (hCpos (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).1)
      (fun j ↦ hCpos (hD (hA (mem_range_self j)))) hvmax).mp hext
    have hsupport : (coefficientSupport p : Set (Fin k)) = univ := by
      ext j
      simp [(hpfull j).ne']
    rw [hsupport] at hlin
    exact ⟨hw, A, hA, linearIndepOn_univ_iff.mp hlin, p, hp.1, hpfull, hp.2⟩

end ReweightedNPMLE
