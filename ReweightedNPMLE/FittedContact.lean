import ReweightedNPMLE.Weights
import ReweightedNPMLE.FiniteOptimizerFiber
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Likelihood contact hyperplanes

At a positive fitted-value maximizer, differentiating toward any other
feasible fitted vector gives the supporting hyperplane used in the paper's
extreme-optimizer argument.  This file proves that first-order statement and
packages its normalized linear functional.
-/

open Set
open scoped BigOperators

namespace ReweightedNPMLE

/-- The unnormalized directional derivative of weighted log likelihood at
`v`, applied to a candidate fitted vector `a`. -/
noncomputable def likelihoodContactNumerator {n : ℕ}
    (w v a : Fin n → ℝ) : ℝ :=
  ∑ i, w i * (a i / v i)

/-- Directional optimality of a positive weighted fitted-value maximizer. -/
theorem likelihoodContactNumerator_le_total_of_isMaxOn
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (w v a : Fin n → ℝ)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v) (ha : a ∈ C) :
    likelihoodContactNumerator w v a ≤ total w := by
  let g : ℝ → ℝ := fun t ↦
    weightedLogLikelihood w (v + t • (a - v))
  have hvpos : ∀ i, 0 < v i := hCpos hvmax.1
  have hderiv : HasDerivAt g
      (∑ i : Fin n, w i * ((a i - v i) / v i)) 0 := by
    have hi (i : Fin n) : HasDerivAt
        (fun t : ℝ ↦ w i * Real.log (v i + t * (a i - v i)))
        (w i * ((a i - v i) / v i)) 0 := by
      have hlin : HasDerivAt (fun t : ℝ ↦ v i + t * (a i - v i))
          (a i - v i) 0 := by
        exact (hasDerivAt_mul_const (x := (0 : ℝ)) (a i - v i)).const_add (v i)
      have hne : v i + (0 : ℝ) * (a i - v i) ≠ 0 := by
        simpa using (hvpos i).ne'
      simpa using (hlin.log hne).const_mul (w i)
    simpa [g, weightedLogLikelihood] using
      (HasDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ hi i)
  have hgmax : IsLocalMaxOn g (Icc (0 : ℝ) 1) 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htC : v + t • (a - v) ∈ C := by
      have hrepr : v + t • (a - v) = (1 - t) • v + t • a := by module
      rw [hrepr]
      exact hC hvmax.1 ha (sub_nonneg.mpr ht.2) ht.1 (by ring)
    simpa [g] using hvmax.2 _ htC
  have hone_tangent : (1 : ℝ) ∈ posTangentConeAt (Icc (0 : ℝ) 1) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    simpa using (segment_subset_Icc (𝕜 := ℝ) (show (0 : ℝ) ≤ 1 by norm_num))
  have hnonpos := hgmax.hasFDerivWithinAt_nonpos
    hderiv.hasFDerivAt.hasFDerivWithinAt hone_tangent
  have hdirection : (∑ i : Fin n, w i * ((a i - v i) / v i)) ≤ 0 := by
    simpa using hnonpos
  have hdiff :
    (∑ i : Fin n, w i * (a i / v i)) - ∑ i, w i =
        ∑ i, w i * ((a i - v i) / v i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      field_simp [(hvpos i).ne']
  unfold likelihoodContactNumerator total
  linarith
  
/-- The normalized likelihood contact functional `a ↦ Σᵢ wᵢaᵢ/(vᵢΣw)`.
It is defined as zero only in the degenerate case `Σw = 0`; the theorems below
use positive weights. -/
noncomputable def likelihoodContactFunctional {n : ℕ}
    (w v : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i : Fin n,
    (w i / (v i * total w)) • LinearMap.proj i

@[simp] theorem likelihoodContactFunctional_apply {n : ℕ}
    (w v a : Fin n → ℝ) :
    likelihoodContactFunctional w v a =
      ∑ i, w i / (v i * total w) * a i := by
  simp [likelihoodContactFunctional]

/-- The fitted vector itself lies on the normalized contact hyperplane. -/
theorem likelihoodContactFunctional_self {n : ℕ} [Nonempty (Fin n)]
    (w v : Fin n → ℝ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) :
    likelihoodContactFunctional w v v = 1 := by
  rw [likelihoodContactFunctional_apply]
  calc
    (∑ i, w i / (v i * total w) * v i) =
        ∑ i, w i / total w := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [(hv i).ne', (total_pos hw).ne']
    _ = 1 := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, total]
      exact mul_inv_cancel₀ (total_ne_zero hw)

/-- Every feasible vector lies below the contact hyperplane at a positive
weighted maximizer. -/
theorem likelihoodContactFunctional_le_one_of_isMaxOn
    {n : ℕ} [Nonempty (Fin n)] {C : Set (Fin n → ℝ)}
    (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (w v a : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hvmax : IsMaxOn C (weightedLogLikelihood w) v) (ha : a ∈ C) :
    likelihoodContactFunctional w v a ≤ 1 := by
  have hvpos := hCpos hvmax.1
  have hraw := likelihoodContactNumerator_le_total_of_isMaxOn
    hC hCpos w v a hvmax ha
  have hrewrite : likelihoodContactFunctional w v a =
      likelihoodContactNumerator w v a / total w := by
    rw [likelihoodContactFunctional_apply]
    unfold likelihoodContactNumerator
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(hvpos i).ne', (total_pos hw).ne']
  rw [hrewrite, div_le_one (total_pos hw)]
  exact hraw

/-- For a finite dictionary, every active atom of an optimizing mixture lies
on the likelihood contact hyperplane. -/
theorem likelihood_contact_on_finite_optimizer_support
    {m n : ℕ} [Nonempty (Fin n)]
    (A : Fin m → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin m → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hvpos : ∀ i, 0 < v i)
    (hApos : ∀ j i, 0 < A j i)
    (hvmax : IsMaxOn (convexHull ℝ (Set.range A))
      (weightedLogLikelihood w) v) :
    ∀ j ∈ coefficientSupport p,
      likelihoodContactFunctional w v (A j) = 1 := by
  apply contact_eq_one_on_coefficientSupport A v p
    (likelihoodContactFunctional w v) hp
  · exact likelihoodContactFunctional_self w v hw hvpos
  · intro j
    apply likelihoodContactFunctional_le_one_of_isMaxOn
      (convex_convexHull ℝ (Set.range A))
      _ w v (A j) hw hvmax
        (subset_convexHull ℝ (Set.range A) (Set.mem_range_self j))
    exact convexHull_min (fun a ha i ↦ by
      rcases ha with ⟨j, rfl⟩
      exact hApos j i) (convex_positiveVectors n)

/-- Exact finite-dictionary form of the paper's extreme-optimizer lemma:
under positive likelihood weights, an optimizing probability vector is
extreme precisely when its active evaluation vectors are linearly
independent. -/
theorem finite_likelihood_optimizer_extreme_iff_linearIndepOn
    {m n : ℕ} [Nonempty (Fin n)]
    (A : Fin m → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin m → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hvpos : ∀ i, 0 < v i)
    (hApos : ∀ j i, 0 < A j i)
    (hvmax : IsMaxOn (convexHull ℝ (Set.range A))
      (weightedLogLikelihood w) v) :
    p ∈ (finiteMixtureFiber A v).extremePoints ℝ ↔
      LinearIndepOn ℝ A (coefficientSupport p : Set (Fin m)) := by
  have hcontact := likelihood_contact_on_finite_optimizer_support
    A v p w hw hp hvpos hApos hvmax
  rw [finiteMixtureFiber_extreme_iff_linearIndepOn_of_contact
    A v p (likelihoodContactFunctional w v) hcontact, and_iff_right hp]

/-- Consequently every extreme optimizer over a finite evaluation dictionary
in `ℝⁿ` has at most `n` active atoms. -/
theorem finite_likelihood_extreme_optimizer_support_card_le
    {m n : ℕ} [Nonempty (Fin n)]
    (A : Fin m → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin m → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hvpos : ∀ i, 0 < v i)
    (hApos : ∀ j i, 0 < A j i)
    (hvmax : IsMaxOn (convexHull ℝ (Set.range A))
      (weightedLogLikelihood w) v)
    (hextreme : p ∈ (finiteMixtureFiber A v).extremePoints ℝ) :
    (coefficientSupport p).card ≤ n := by
  apply coefficientSupport_card_le_fin A p
  exact (finite_likelihood_optimizer_extreme_iff_linearIndepOn
    A v p w hw hp hvpos hApos hvmax).mp hextreme

end ReweightedNPMLE
