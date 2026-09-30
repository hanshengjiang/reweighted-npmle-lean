import ReweightedNPMLE.FullEffectiveDimension
import ReweightedNPMLE.SupportSensitivityAnalytic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-! # Full-law support sensitivity and the maximal-rank Hessian summary

One dictionary-dependent almost-everywhere differentiability set controls
every extreme optimizing law, including laws not initially known to be atomic.
-/

open Set Filter MeasureTheory Matrix
open scoped Topology BigOperators

namespace ReweightedNPMLE

theorem orthonormal_matrix_projection_properties {n m : ℕ}
    (V : Matrix (Fin n) (Fin m) ℝ) (hV : Vᴴ * V = 1) :
    (V * Vᴴ).IsHermitian ∧ (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ ∧ (V * Vᴴ).rank = m := by
  have hVr : V.rank = m := by
    apply le_antisymm (rank_le_width V)
    have h := rank_mul_le_right Vᴴ V
    simpa only [hV, rank_one, Fintype.card_fin] using h
  refine ⟨isHermitian_mul_conjTranspose_self V, ?_, ?_⟩
  · calc
      _ = V * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, Matrix.mul_one]
  · rw [rank_self_mul_conjTranspose, hVr]

theorem full_extreme_optimizer_hessian_projection {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C) (hCcompact : IsCompact C)
    (hCnonempty : C.Nonempty) (hCpos : C ⊆ positiveVectors n) (hAC : range A ⊆ C)
    (w : Fin n → ℝ) (hw : w ∈ positiveVectors n)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fittedLogSelection C hCcompact hCnonempty hCpos) J w)
    (μ : ProbabilityMeasure Θ)
    (hμ : IsExtremeProbabilityMixture A (fittedValueSelection C hCcompact hCnonempty hCpos w) μ) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ,
      P.IsHermitian ∧ P * P = P ∧ P.rank = (μ : Measure Θ).support.ncard - 1 ∧
      (Matrix.diagonal (fun i ↦ Real.sqrt (w i)) * fittedLogDerivativeMatrix J *
        Matrix.diagonal (fun i ↦ Real.sqrt (w i)) - P).PosSemidef := by
  let vhat := fittedValueSelection C hCcompact hCnonempty hCpos
  let v := vhat w
  have hmax (q : Fin n → ℝ) : IsMaxOn C (weightedLogLikelihood q) (vhat q) :=
    fittedValueSelection_isMax C hCcompact hCnonempty hCpos q
  obtain ⟨k, θ, p, hp, _, hθ, hpPos, hlin, hpval, heqμ⟩ :=
    (full_probability_optimizer_extreme_iff A hA hC hCpos hAC w v hw (hmax w) μ).mp hμ
  have hk : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    subst k
    have hsum := hp.2
    simp at hsum
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  have hcard : (μ : Measure Θ).support.ncard = k := by
    rw [← heqμ, finiteProbabilityMeasure_support θ hθ p hp hpPos, ncard_range_of_injective hθ]
    simp
  have hfiniteAC : range (A ∘ θ) ⊆ C := by
    rintro u ⟨j, rfl⟩
    exact hAC (mem_range_self (θ j))
  have hvpos : ∀ i, 0 < v i := hCpos (hmax w).1
  let S := weightedRelativeTangentSpace (A ∘ θ) v w
  let V := submoduleOrthonormalMatrix S
  let P := V * Vᴴ
  have hrankS : Module.finrank ℝ S = k - 1 :=
    finrank_weightedRelativeTangentSpace _ _ _ hlin (fun i ↦ (hvpos i).ne') hw
  obtain ⟨hPH, hPP, hPrank⟩ := orthonormal_matrix_projection_properties V
    (submoduleOrthonormalMatrix_conjTranspose_mul S)
  have hpsi := eventually_canonicalFittedOptimalValue_hasFDerivAt_of_positive_weights
    C hC hCcompact hCnonempty hCpos w hw
  have hdom := finite_optimizer_hessian_sub_projection_posSemidef (A ∘ θ) v p w hw
    ⟨hp, hpval⟩ hpPos hvpos (fun j ↦ hCpos (hfiniteAC (mem_range_self j)))
    vhat hC hfiniteAC hmax rfl hpsi hz
  refine ⟨P, hPH, hPP, ?_, hdom⟩
  rw [hcard]
  exact hPrank.trans hrankS

/-- Lemmas `lem:matrix-sensitivity` and `lem:hessian-summary`, with the actual
Hessian of the optimized value and the full-measure maximum support statistic. -/
theorem full_support_sensitivity_ae {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C) (hCcompact : IsCompact C)
    (hCnonempty : C.Nonempty) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C) (hChull : C ⊆ convexHull ℝ (range A)) :
    let vhat := fittedValueSelection C hCcompact hCnonempty hCpos
    let z := fittedLogSelection C hCcompact hCnonempty hCpos
    ∀ᵐ w ∂volume, w ∈ positiveVectors n →
      let J := fderiv ℝ z w
      let H := fittedLogDerivativeMatrix J
      let D := Matrix.diagonal (fun i ↦ Real.sqrt (w i))
      HasFDerivAt (fderiv ℝ (fittedOptimalValue vhat)) (fittedSecondDerivativeOfLogDerivative J) w ∧
      (∀ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A (vhat w) μ →
        ∃ P : Matrix (Fin n) (Fin n) ℝ,
          P.IsHermitian ∧ P * P = P ∧ P.rank = (μ : Measure Θ).support.ncard - 1 ∧
            (D * H * D - P).PosSemidef) ∧
      ∃ P : Matrix (Fin n) (Fin n) ℝ,
        P.IsHermitian ∧ P * P = P ∧ P.rank = maximumExtremeSupport A vhat w - 1 ∧
          (D * H * D - P).PosSemidef := by
  dsimp only
  let vhat := fittedValueSelection C hCcompact hCnonempty hCpos
  let z := fittedLogSelection C hCcompact hCnonempty hCpos
  filter_upwards [canonicalFittedLog_ae_differentiableAt C hC hCcompact hCnonempty hCpos]
    with w hdiff hw
  have hz := (hdiff hw).hasFDerivAt
  have hpsi := eventually_canonicalFittedOptimalValue_hasFDerivAt_of_positive_weights
    C hC hCcompact hCnonempty hCpos w hw
  have hsecond : HasFDerivAt (fderiv ℝ (fittedOptimalValue vhat))
      (fittedSecondDerivativeOfLogDerivative (fderiv ℝ z w)) w := by
    apply (hasFDerivAt_fittedLogLinearFunctional hz).congr_of_eventuallyEq
    filter_upwards [hpsi] with q hq
    exact hq.fderiv
  have hall : ∀ μ : ProbabilityMeasure Θ, IsExtremeProbabilityMixture A (vhat w) μ →
      ∃ P : Matrix (Fin n) (Fin n) ℝ,
        P.IsHermitian ∧ P * P = P ∧ P.rank = (μ : Measure Θ).support.ncard - 1 ∧
          (Matrix.diagonal (fun i ↦ Real.sqrt (w i)) * fittedLogDerivativeMatrix (fderiv ℝ z w) *
            Matrix.diagonal (fun i ↦ Real.sqrt (w i)) - P).PosSemidef :=
    fun μ hμ ↦ full_extreme_optimizer_hessian_projection A hA C hC hCcompact hCnonempty hCpos hAC w hw hz μ hμ
  refine ⟨hsecond, hall, ?_⟩
  obtain ⟨_, _, μ, hμ, hcard⟩ := canonical_maximumExtremeSupport_attained A hA C hC
    hCcompact hCnonempty hCpos hAC hChull w hw
  obtain ⟨P, hPH, hPP, hPrank, hdom⟩ := hall μ hμ
  exact ⟨P, hPH, hPP, hcard ▸ hPrank, hdom⟩

end ReweightedNPMLE
