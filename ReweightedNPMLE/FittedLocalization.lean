import ReweightedNPMLE.FittedRegularity
import Mathlib.Tactic

/-!
# Likelihood-facing radial localization

Relative feasible fitted vectors and their log-ratios translate the radial
localization inequalities into ordinary likelihood loss and fitted-log
error.  The theorem applies simultaneously to every near-optimal fit.
-/

open Set Filter MeasureTheory Matrix
open scoped BigOperators Topology

namespace ReweightedNPMLE

noncomputable def relativeFittedVector {n : ℕ} (v₀ v : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ v i / v₀ i - 1

def relativeFittedSet {n : ℕ} (C : Set (Fin n → ℝ)) (v₀ : Fin n → ℝ) :
    Set (Fin n → ℝ) := relativeFittedVector v₀ '' C

noncomputable def fittedLogRatio {n : ℕ} (v₀ v : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ Real.log (v i) - Real.log (v₀ i)

theorem convex_relativeFittedSet {n : ℕ}
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (v₀ : Fin n → ℝ) :
    Convex ℝ (relativeFittedSet C v₀) := by
  rintro u ⟨v, hv, rfl⟩ u' ⟨v', hv', rfl⟩ a b ha hb hab
  refine ⟨a • v + b • v', hC hv hv' ha hb hab, ?_⟩
  funext i
  simp only [relativeFittedVector, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [add_div, mul_div_assoc, mul_div_assoc]
  nlinarith

theorem zero_mem_relativeFittedSet {n : ℕ}
    {C : Set (Fin n → ℝ)} {v₀ : Fin n → ℝ}
    (hv₀ : v₀ ∈ C) (hv₀pos : ∀ i, 0 < v₀ i) :
    (0 : Fin n → ℝ) ∈ relativeFittedSet C v₀ := by
  refine ⟨v₀, hv₀, ?_⟩
  funext i
  simp [relativeFittedVector, (hv₀pos i).ne']

theorem relativeFittedVector_one_add_pos {n : ℕ}
    (v₀ v : Fin n → ℝ) (hv₀ : ∀ i, 0 < v₀ i) (hv : ∀ i, 0 < v i) :
    ∀ i, 0 < 1 + relativeFittedVector v₀ v i := by
  intro i
  simpa [relativeFittedVector] using div_pos (hv i) (hv₀ i)

theorem relativeFittedVector_log_one_add {n : ℕ}
    (v₀ v : Fin n → ℝ) (hv₀ : ∀ i, 0 < v₀ i) (hv : ∀ i, 0 < v i) :
    (fun i ↦ Real.log (1 + relativeFittedVector v₀ v i)) = fittedLogRatio v₀ v := by
  funext i
  simp [relativeFittedVector, fittedLogRatio, Real.log_div (hv i).ne' (hv₀ i).ne']

theorem weightedLogLikelihood_sub_eq_logRatio {n : ℕ}
    (w v₀ v : Fin n → ℝ) :
    weightedLogLikelihood w v - weightedLogLikelihood w v₀ =
      ∑ i, w i * fittedLogRatio v₀ v i := by
  simp only [weightedLogLikelihood, fittedLogRatio, mul_sub, Finset.sum_sub_distrib]

theorem relativeFittedSet_firstOrder {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (v₀ : Fin n → ℝ) (hv₀ : IsMaxOn C (weightedLogLikelihood 1) v₀) :
    ∀ u ∈ relativeFittedSet C v₀, ∑ i, u i ≤ 0 := by
  rintro u ⟨v, hv, rfl⟩
  have hf := fitted_maximizer_firstOrder_nonpos hC hCpos (1 : Fin n → ℝ) v₀ v hv₀ hv
  have heq : (∑ i, (1 : Fin n → ℝ) i * ((v i - v₀ i) / v₀ i)) =
      ∑ i, relativeFittedVector v₀ v i := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.one_apply, one_mul, relativeFittedVector]
    field_simp [(hCpos hv₀.1 i).ne']
  rwa [heq] at hf

theorem fitted_radial_localization {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (v₀ : Fin n → ℝ) (hv₀ : IsMaxOn C (weightedLogLikelihood 1) v₀)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (η : ℝ) (hη : 0 ≤ η)
    (hwidth : ∀ u ∈ relativeFittedSet C v₀,
      ‖WithLp.toLp 2 u - V.starProjection (WithLp.toLp 2 u)‖ ≤ η)
    (w v : Fin n → ℝ) (hv : v ∈ C) (τ : ℝ) (hτ₀ : 0 ≤ τ)
    (hw : ∀ i, |w i - 1| ≤ 1 / 16)
    (hA : ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖ ≤ (1 / 16 : ℝ) / 24)
    (hE : η * ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖ ≤ (1 / 16 : ℝ) ^ 2 / 24)
    (hτ : τ < (1 / 16 : ℝ) ^ 2 / 12)
    (hnear : weightedLogLikelihood w v₀ - τ ≤ weightedLogLikelihood w v) :
    let A := ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖
    let E := η * ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖
    (∀ i, |fittedLogRatio v₀ v i| ≤ 1 / 8) ∧
    0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ∧
    weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ≤ 37 * A ^ 2 + 13 * E + 13 * τ ∧
    (∑ i, (fittedLogRatio v₀ v i) ^ 2) ≤ 72 * A ^ 2 + 24 * E + 24 * τ ∧
    (∑ i, (w i - 1) * fittedLogRatio v₀ v i) ≤ 37 * A ^ 2 + 13 * E + 12 * τ := by
  let u := relativeFittedVector v₀ v
  have hu : u ∈ relativeFittedSet C v₀ := ⟨v, hv, rfl⟩
  have hlog := relativeFittedVector_log_one_add v₀ v (hCpos hv₀.1) (hCpos hv)
  have hnear' : -τ ≤ ∑ i, w i * Real.log (1 + u i) := by
    have heq : (∑ i, w i * Real.log (1 + u i)) =
        weightedLogLikelihood w v - weightedLogLikelihood w v₀ := by
      rw [weightedLogLikelihood_sub_eq_logRatio]
      exact congrArg (fun z : Fin n → ℝ ↦ ∑ i, w i * z i) hlog
    rw [heq]
    linarith
  have hloc := radial_localization_of_projection (relativeFittedSet C v₀)
    (convex_relativeFittedSet hC v₀) (zero_mem_relativeFittedSet hv₀.1 (hCpos hv₀.1))
    V η hη hwidth w u hu (relativeFittedVector_one_add_pos v₀ v (hCpos hv₀.1) (hCpos hv))
    τ hτ₀ hw hA hE (relativeFittedSet_firstOrder hC hCpos v₀ hv₀) hτ hnear'
  have hcoord : ∀ i, |fittedLogRatio v₀ v i| ≤ 1 / 8 := by
    intro i
    have hui : |u i| ≤ 1 / 16 := (abs_le_sqrt_sum_sq u i).trans hloc.1.le
    have hui' : |u i| < 1 := hui.trans_lt (by norm_num)
    have hl := abs_log_one_add_le hui'
    have hden : 0 < 1 - |u i| := by linarith
    have hfrac : |u i| / (1 - |u i|) ≤ 1 / 8 := by
      apply (div_le_iff₀ hden).mpr
      linarith
    have hz := congrFun hlog i
    change Real.log (1 + u i) = fittedLogRatio v₀ v i at hz
    rw [← hz]
    exact hl.trans hfrac
  have hloss : weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v =
      -(∑ i, Real.log (1 + u i)) := by
    rw [← neg_sub (weightedLogLikelihood 1 v) (weightedLogLikelihood 1 v₀),
      weightedLogLikelihood_sub_eq_logRatio]
    simp only [Pi.one_apply, one_mul]
    congr 1
    exact (congrArg (fun z : Fin n → ℝ ↦ ∑ i, z i) hlog).symm
  refine ⟨hcoord, ?_, ?_, ?_, ?_⟩
  · rw [hloss]
    exact hloc.2.2.1
  · rw [hloss]
    exact hloc.2.2.2.1
  · have heq := congrArg (fun z : Fin n → ℝ ↦ ∑ i, z i ^ 2) hlog
    dsimp only at heq
    rw [← heq]
    exact hloc.2.2.2.2.1
  · have heq := congrArg (fun z : Fin n → ℝ ↦ ∑ i, (w i - 1) * z i) hlog
    dsimp only at heq
    rw [← heq]
    exact hloc.2.2.2.2.2

end ReweightedNPMLE
