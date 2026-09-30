import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Order.Compact

/-!
# Weighted likelihood and normalization

This file formalizes the deterministic normalization statements in Section 2.2 of the
paper.  Vectors are represented by functions on `Fin n`; this is the representation used
throughout the rest of the development.
-/

open scoped BigOperators

namespace ReweightedNPMLE

/-- The sum of the coordinates of a finite real vector. -/
def total {n : ℕ} (w : Fin n → ℝ) : ℝ := ∑ i, w i

/-- Coordinatewise normalization by the total mass. -/
noncomputable def normalize {n : ℕ} (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ w i / total w

/-- The finite weighted log-likelihood of a positive fitted-value vector. -/
noncomputable def weightedLogLikelihood {n : ℕ} (w v : Fin n → ℝ) : ℝ :=
  ∑ i, w i * Real.log (v i)

/-- A point `v` maximizes `f` on the feasible set `C`. -/
def IsMaxOn {E : Type*} (C : Set E) (f : E → ℝ) (v : E) : Prop :=
  v ∈ C ∧ ∀ u ∈ C, f u ≤ f v

/-- The strictly positive orthant containing all fitted-value vectors. -/
def positiveVectors (n : ℕ) : Set (Fin n → ℝ) :=
  {v | ∀ i, 0 < v i}

theorem convex_positiveVectors (n : ℕ) : Convex ℝ (positiveVectors n) := by
  intro x hx y hy a b ha hb hab i
  change 0 < a * x i + b * y i
  rcases ha.eq_or_lt with rfl | ha
  · simp only [zero_mul, zero_add] at hab ⊢
    subst b
    simpa using hy i
  · rcases hb.eq_or_lt with rfl | hb
    · simp only [mul_zero, add_zero] at hab ⊢
      subst a
      simpa using hx i
    · exact add_pos (mul_pos ha (hx i)) (mul_pos hb (hy i))

/-- For positive weights, the finite log-likelihood is strictly concave in fitted values. -/
theorem strictConcaveOn_weightedLogLikelihood {n : ℕ} [Nonempty (Fin n)]
    {w : Fin n → ℝ} (hw : ∀ i, 0 < w i) :
    StrictConcaveOn ℝ (positiveVectors n) (weightedLogLikelihood w) := by
  classical
  refine ⟨convex_positiveVectors n, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hdiff : ∃ i, x i ≠ y i := by
    by_contra h
    apply hxy
    funext i
    simpa using not_ne_iff.mp (not_exists.mp h i)
  have hcoord_le : ∀ i, a * Real.log (x i) + b * Real.log (y i) ≤
      Real.log (a * x i + b * y i) := by
    intro i
    simpa [smul_eq_mul] using
      strictConcaveOn_log_Ioi.concaveOn.2 (hx i) (hy i) ha.le hb.le hab
  have hcoord_lt : ∃ i, a * Real.log (x i) + b * Real.log (y i) <
      Real.log (a * x i + b * y i) := by
    obtain ⟨i, hi⟩ := hdiff
    refine ⟨i, ?_⟩
    simpa [smul_eq_mul] using
      strictConcaveOn_log_Ioi.2 (hx i) (hy i) hi ha hb hab
  calc
    a • weightedLogLikelihood w x + b • weightedLogLikelihood w y =
        ∑ i, w i * (a * Real.log (x i) + b * Real.log (y i)) := by
          simp only [weightedLogLikelihood, smul_eq_mul, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ < ∑ i, w i * Real.log (a * x i + b * y i) := by
      apply Finset.sum_lt_sum
      · intro i _
        exact mul_le_mul_of_nonneg_left (hcoord_le i) (hw i).le
      · obtain ⟨i, hi⟩ := hcoord_lt
        exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi (hw i)⟩
    _ = weightedLogLikelihood w (a • x + b • y) := by
      simp [weightedLogLikelihood, smul_eq_mul]

/-- The finite weighted log-likelihood is continuous on the positive orthant. -/
theorem continuousOn_weightedLogLikelihood {n : ℕ} (w : Fin n → ℝ) :
    ContinuousOn (weightedLogLikelihood w) (positiveVectors n) := by
  change ContinuousOn (fun v ↦ ∑ i : Fin n, w i * Real.log (v i)) (positiveVectors n)
  apply continuousOn_finsetSum Finset.univ
  intro i _ v hv
  have happ : ContinuousAt (fun z : Fin n → ℝ ↦ z i) v :=
    (continuous_apply i).continuousAt
  exact ((Real.continuousAt_log (hv i).ne').comp
    (f := fun z : Fin n → ℝ ↦ z i) (x := v) happ).const_mul (w i) |>.continuousWithinAt

/-- A nonempty compact positive fitted-value set has a weighted maximizer. -/
theorem exists_fittedValue_maximizer {n : ℕ}
    {C : Set (Fin n → ℝ)} (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) (w : Fin n → ℝ) :
    ∃ v, IsMaxOn C (weightedLogLikelihood w) v := by
  obtain ⟨v, hvC, hvmax⟩ := hCcompact.exists_isMaxOn hCnonempty
    ((continuousOn_weightedLogLikelihood w).mono hCpos)
  exact ⟨v, hvC, fun u hu ↦ hvmax hu⟩

/-- Strict concavity makes the fitted-value maximizer unique on any convex feasible set. -/
theorem fittedValue_maximizer_unique {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C)
    (hCpos : C ⊆ positiveVectors n) {w : Fin n → ℝ} (hw : ∀ i, 0 < w i)
    {u v : Fin n → ℝ}
    (hu : IsMaxOn C (weightedLogLikelihood w) u)
    (hv : IsMaxOn C (weightedLogLikelihood w) v) : u = v := by
  by_contra huv
  let m := (2 : ℝ)⁻¹ • u + (2 : ℝ)⁻¹ • v
  have hm : m ∈ C := hC hu.1 hv.1 (by norm_num) (by norm_num) (by norm_num)
  have hstrict := ((strictConcaveOn_weightedLogLikelihood hw).subset hCpos hC).2
    hu.1 hv.1 huv (by norm_num : (0 : ℝ) < 2⁻¹)
    (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ + 2⁻¹ = 1)
  have huv_obj : weightedLogLikelihood w u = weightedLogLikelihood w v :=
    le_antisymm (hv.2 u hu.1) (hu.2 v hv.1)
  have hm_le : weightedLogLikelihood w m ≤ weightedLogLikelihood w u := hu.2 m hm
  change (2 : ℝ)⁻¹ • weightedLogLikelihood w u +
      (2 : ℝ)⁻¹ • weightedLogLikelihood w v < weightedLogLikelihood w m at hstrict
  rw [← huv_obj] at hstrict
  have hstrict' : weightedLogLikelihood w u < weightedLogLikelihood w m := by
    calc
      weightedLogLikelihood w u = (2 : ℝ)⁻¹ • weightedLogLikelihood w u +
          (2 : ℝ)⁻¹ • weightedLogLikelihood w u := by
            norm_num [smul_eq_mul]
            ring
      _ < weightedLogLikelihood w m := hstrict
  exact (not_lt_of_ge hm_le) hstrict'

@[simp] theorem total_zero {n : ℕ} : total (fun _ : Fin n ↦ (0 : ℝ)) = 0 := by
  simp [total]

theorem total_pos {n : ℕ} [Nonempty (Fin n)] {w : Fin n → ℝ}
    (hw : ∀ i, 0 < w i) : 0 < total w := by
  classical
  exact Finset.sum_pos (fun i _ ↦ hw i) Finset.univ_nonempty

theorem total_ne_zero {n : ℕ} [Nonempty (Fin n)] {w : Fin n → ℝ}
    (hw : ∀ i, 0 < w i) : total w ≠ 0 :=
  (total_pos hw).ne'

theorem sum_normalize {n : ℕ} {w : Fin n → ℝ} (hw : total w ≠ 0) :
    ∑ i, normalize w i = 1 := by
  classical
  simp only [normalize, div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ hw

theorem normalize_pos {n : ℕ} [Nonempty (Fin n)] {w : Fin n → ℝ}
    (hw : ∀ i, 0 < w i) (i : Fin n) : 0 < normalize w i := by
  exact div_pos (hw i) (total_pos hw)

theorem total_smul {n : ℕ} (c : ℝ) (w : Fin n → ℝ) :
    total (c • w) = c * total w := by
  classical
  simp [total, Finset.mul_sum]

theorem normalize_smul {n : ℕ} {c : ℝ} (hc : c ≠ 0) (w : Fin n → ℝ) :
    normalize (c • w) = normalize w := by
  funext i
  simpa [normalize, total_smul] using mul_div_mul_left (w i) (total w) hc

theorem weightedLogLikelihood_smul {n : ℕ} (c : ℝ) (w v : Fin n → ℝ) :
    weightedLogLikelihood (c • w) v = c * weightedLogLikelihood w v := by
  classical
  simp [weightedLogLikelihood, Finset.mul_sum, mul_assoc]

theorem weightedLogLikelihood_normalize {n : ℕ} (w v : Fin n → ℝ) :
    weightedLogLikelihood (normalize w) v =
      (total w)⁻¹ * weightedLogLikelihood w v := by
  classical
  simp only [weightedLogLikelihood, normalize, div_eq_mul_inv]
  calc
    ∑ i, w i * (total w)⁻¹ * Real.log (v i) =
        ∑ i, (total w)⁻¹ * (w i * Real.log (v i)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (total w)⁻¹ * ∑ i, w i * Real.log (v i) := by
      rw [Finset.mul_sum]

/-- Multiplication of an objective by a positive scalar leaves its maximizers unchanged. -/
theorem isMaxOn_pos_mul_iff {E : Type*} {C : Set E} {f : E → ℝ}
    {c : ℝ} (hc : 0 < c) (v : E) :
    IsMaxOn C (fun u ↦ c * f u) v ↔ IsMaxOn C f v := by
  constructor
  · rintro ⟨hv, hmax⟩
    refine ⟨hv, ?_⟩
    intro u hu
    exact le_of_mul_le_mul_left (hmax u hu) hc
  · rintro ⟨hv, hmax⟩
    refine ⟨hv, ?_⟩
    intro u hu
    exact mul_le_mul_of_nonneg_left (hmax u hu) hc.le

/-- Normalizing strictly positive weights does not change the likelihood maximizers. -/
theorem isMaxOn_normalize_iff {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)} {w : Fin n → ℝ} (hw : ∀ i, 0 < w i)
    (v : Fin n → ℝ) :
    IsMaxOn C (weightedLogLikelihood (normalize w)) v ↔
      IsMaxOn C (weightedLogLikelihood w) v := by
  rw [show weightedLogLikelihood (normalize w) =
      fun u ↦ (total w)⁻¹ * weightedLogLikelihood w u by
    funext u
    exact weightedLogLikelihood_normalize w u]
  exact isMaxOn_pos_mul_iff (inv_pos.mpr (total_pos hw)) v

/-- Scaling all positive weights does not change the likelihood maximizers. -/
theorem isMaxOn_weight_smul_iff {n : ℕ} {C : Set (Fin n → ℝ)}
    {c : ℝ} (hc : 0 < c) (w v : Fin n → ℝ) :
    IsMaxOn C (weightedLogLikelihood (c • w)) v ↔
      IsMaxOn C (weightedLogLikelihood w) v := by
  rw [show weightedLogLikelihood (c • w) =
      fun u ↦ c * weightedLogLikelihood w u by
    funext u
    exact weightedLogLikelihood_smul c w u]
  exact isMaxOn_pos_mul_iff hc v

end ReweightedNPMLE
