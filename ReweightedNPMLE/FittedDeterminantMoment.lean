import ReweightedNPMLE.SupportSensitivityAnalytic
import ReweightedNPMLE.ExtremeSupport
import ReweightedNPMLE.ChangeOfVariables
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Canonical fitted-value determinant moment

The Gamma determinant moment is proved for a compact positive convex fitted
set and any measurable cardinality function realized by full-support extreme
finite representations.  The representing atoms and coefficients may vary
with the weights, and need not be measurable choices.  All analytic and
change-of-variables hypotheses follow from canonical fitted-value regularity
and support sensitivity.
-/

open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace ReweightedNPMLE

theorem canonical_gamma_determinant_moment
    {n : ℕ} [Nonempty (Fin n)] {α : ℝ} (hα : 0 < α)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (z₀ : Fin n → ℝ)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) (hspos : s ⊆ positiveVectors n)
    (k : (Fin n → ℝ) → ℕ) (hkmeas : Measurable k)
    (A : (w : Fin n → ℝ) → Fin (k w) → Fin n → ℝ)
    (p : (w : Fin n → ℝ) → Fin (k w) → ℝ)
    (hA : ∀ w ∈ s, Set.range (A w) ⊆ C)
    (hp : ∀ w ∈ s, p w ∈ finiteMixtureFiber (A w)
      (fittedValueSelection C hCcompact hCnonempty hCpos w))
    (hpfull : ∀ w ∈ s, ∀ j, 0 < p w j)
    (hextreme : ∀ w ∈ s, p w ∈ (finiteMixtureFiber (A w)
      (fittedValueSelection C hCcompact hCnonempty hCpos w)).extremePoints ℝ)
    (ht : ∀ w ∈ s, ∀ i,
      |fittedLogDisplacement C hCcompact hCnonempty hCpos z₀ w i| ≤ 1 / 8) :
    let t := fittedLogDisplacement C hCcompact hCnonempty hCpos z₀
    ∫⁻ w in s, ENNReal.ofReal
        ((17 / 9 : ℝ) ^ (k w - 1) * Real.exp (-α *
          (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2)))
      ∂gammaProductMeasure n α α ≤ 1 := by
  let z := fittedLogSelection C hCcompact hCnonempty hCpos
  let t := fittedLogDisplacement C hCcompact hCnonempty hCpos z₀
  let J := fderiv ℝ z
  have hdiff := canonicalFittedLog_ae_differentiableAt C hC hCcompact hCnonempty hCpos
  apply gamma_determinant_moment_of_monotone_ae_deriv hα hs t
    (fun w ↦ (17 / 9 : ℝ) ^ (k w - 1)) J
  · filter_upwards [hdiff] with w hw hws
    exact fittedLogDisplacement_hasFDerivAt C hCcompact hCnonempty hCpos z₀
      (hspos hws) (hw (hspos hws)).hasFDerivAt
  · exact measurable_fittedLogDisplacement C hC hCcompact hCnonempty hCpos z₀
  · exact (hkmeas.sub_const 1).const_pow (17 / 9 : ℝ)
  · exact fun w hws ↦ hspos hws
  · exact ht
  · intro w hws v hvs
    have hmon := fittedLog_monotone
      (fittedValueSelection C hCcompact hCnonempty hCpos)
      (s := s) (fun q _ ↦ fittedValueSelection_isMax C hCcompact hCnonempty hCpos q)
      w hws v hvs
    dsimp only [t]
    rw [fittedLogDisplacement_eq C hCcompact hCnonempty hCpos z₀ (hspos hws),
      fittedLogDisplacement_eq C hCcompact hCnonempty hCpos z₀ (hspos hvs)]
    simpa only [fittedLogSelection, Pi.sub_apply, sub_sub_sub_cancel_right] using hmon
  · intro w hws
    positivity
  · filter_upwards [hdiff] with w hw hws
    have hkpos : 0 < k w := by
      apply Nat.pos_of_ne_zero
      intro hk
      have hh := (hp w hws).1.2
      letI : IsEmpty (Fin (k w)) := ⟨fun i ↦ Nat.not_lt_zero i.val (hk ▸ i.isLt)⟩
      simp at hh
    letI : Nonempty (Fin (k w)) := ⟨⟨0, hkpos⟩⟩
    have ha0 : ∀ i, 0 < 1 + t w i := by
      intro i
      have hi := neg_le_of_abs_le (ht w hws i)
      norm_num at hi ⊢
      linarith
    have haUpper : ∀ i, 1 + t w i ≤ 9 / 8 := by
      intro i
      have hi := le_of_abs_le (ht w hws i)
      norm_num at hi ⊢
      linarith
    have hd := canonical_finite_extreme_optimizer_jacobian_determinant_lower
      C hC hCcompact hCnonempty hCpos (A w) (hA w hws) (p w) w (hspos hws)
      (hp w hws) (hpfull w hws) (hextreme w hws) (hw (hspos hws)).hasFDerivAt
      (fun i ↦ 1 + t w i) ha0 haUpper
    rw [continuousLinearMap_det_eq_toMatrix', multiplicativeChangeDeriv_toMatrix]
    exact hd.trans (le_abs_self _)

/-- The determinant moment for the maximum independent support statistic.
Neither a measurable support statistic nor a selected extreme representation
is supplied as an assumption; both its measurability and its Jacobian gain
come from the representation geometry. -/
theorem canonical_maximumIndependentSupport_gamma_moment
    {n : ℕ} [Nonempty (Fin n)] {α : ℝ} (hα : 0 < α)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (D : Set (Fin n → ℝ)) (hDclosed : IsClosed D) (hD : D ⊆ C)
    (z₀ : Fin n → ℝ)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) (hspos : s ⊆ positiveVectors n)
    (ht : ∀ w ∈ s, ∀ i,
      |fittedLogDisplacement C hCcompact hCnonempty hCpos z₀ w i| ≤ 1 / 8) :
    let t := fittedLogDisplacement C hCcompact hCnonempty hCpos z₀
    let k := maximumIndependentSupport D (fittedValueSelection C hCcompact hCnonempty hCpos)
    ∫⁻ w in s, ENNReal.ofReal
        ((17 / 9 : ℝ) ^ (k w - 1) * Real.exp (-α *
          (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2)))
      ∂gammaProductMeasure n α α ≤ 1 := by
  let z := fittedLogSelection C hCcompact hCnonempty hCpos
  let t := fittedLogDisplacement C hCcompact hCnonempty hCpos z₀
  let k := maximumIndependentSupport D (fittedValueSelection C hCcompact hCnonempty hCpos)
  let J := fderiv ℝ z
  have hdiff := canonicalFittedLog_ae_differentiableAt C hC hCcompact hCnonempty hCpos
  apply gamma_determinant_moment_of_monotone_ae_deriv hα hs t
    (fun w ↦ (17 / 9 : ℝ) ^ (k w - 1)) J
  · filter_upwards [hdiff] with w hw hws
    exact fittedLogDisplacement_hasFDerivAt C hCcompact hCnonempty hCpos z₀
      (hspos hws) (hw (hspos hws)).hasFDerivAt
  · exact measurable_fittedLogDisplacement C hC hCcompact hCnonempty hCpos z₀
  · exact ((measurable_maximumIndependentSupport D hDclosed
      (fittedValueSelection C hCcompact hCnonempty hCpos)
      (canonicalFittedValue_continuousOn C hC hCcompact hCnonempty hCpos)).sub_const 1).const_pow _
  · exact fun w hws ↦ hspos hws
  · exact ht
  · intro w hws v hvs
    have hmon := fittedLog_monotone
      (fittedValueSelection C hCcompact hCnonempty hCpos)
      (s := s) (fun q _ ↦ fittedValueSelection_isMax C hCcompact hCnonempty hCpos q)
      w hws v hvs
    dsimp only [t]
    rw [fittedLogDisplacement_eq C hCcompact hCnonempty hCpos z₀ (hspos hws),
      fittedLogDisplacement_eq C hCcompact hCnonempty hCpos z₀ (hspos hvs)]
    simpa only [fittedLogSelection, Pi.sub_apply, sub_sub_sub_cancel_right] using hmon
  · intro w hws
    positivity
  · filter_upwards [hdiff] with w hw hws
    have ha0 : ∀ i, 0 < 1 + t w i := by
      intro i
      have hi := neg_le_of_abs_le (ht w hws i)
      norm_num at hi ⊢
      linarith
    have haUpper : ∀ i, 1 + t w i ≤ 9 / 8 := by
      intro i
      have hi := le_of_abs_le (ht w hws i)
      norm_num at hi ⊢
      linarith
    have hd := canonical_maximumIndependentSupport_jacobian_determinant_lower
      C hC hCcompact hCnonempty hCpos D hD w (hspos hws)
      (hw (hspos hws)).hasFDerivAt (fun i ↦ 1 + t w i) ha0 haUpper
    rw [continuousLinearMap_det_eq_toMatrix', multiplicativeChangeDeriv_toMatrix]
    exact hd.trans (le_abs_self _)

end ReweightedNPMLE
