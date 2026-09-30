import ReweightedNPMLE.EffectiveDimension
import ReweightedNPMLE.FittedLocalization
import ReweightedNPMLE.GammaEffectiveEvent
import Mathlib.Tactic

/-!
# Effective-dimension sparsification on a common event

Gamma concentration instantiates radial localization and the determinant
support tail. All near-optimal fitted vectors obey the error bounds on the
same measurable event. The support statistic here is the maximum independent
finite representation; identification with full measure-fiber extreme points
is a separate theorem, not an assumption hidden in this result.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace ReweightedNPMLE

theorem gammaEffectiveEvent_fitted_localization {n r : ℕ} [Nonempty (Fin n)]
    {α q η : ℝ} (hα : 0 < α) (hQ : 0 ≤ effectiveQ n q) (hN : 0 ≤ effectiveN r q)
    (hη : 0 ≤ η) (hwidthScale : η * Real.sqrt (α * (n : ℝ) * effectiveQ n q) ≤ 1)
    (hαQ : 1024 * effectiveQ n q ≤ α)
    (hαN : 2359296 * effectiveN r q ≤ α) (hα₀ : 12288 ≤ α)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hwidth : ∀ u ∈ relativeFittedSet C (fittedValueSelection C hCcompact hCnonempty hCpos 1),
      ‖WithLp.toLp 2 u - V.starProjection (WithLp.toLp 2 u)‖ ≤ η)
    {w : Fin n → ℝ} (hw : w ∈ gammaEffectiveEvent V r α q)
    (v : Fin n → ℝ) (hv : v ∈ C) (τ : ℝ) (hτ₀ : 0 ≤ τ) (hτ : τ < 1 / 3072)
    (hnear : weightedLogLikelihood w (fittedValueSelection C hCcompact hCnonempty hCpos w) - τ ≤
      weightedLogLikelihood w v) :
    let v₀ := fittedValueSelection C hCcompact hCnonempty hCpos 1
    (∀ i, |fittedLogRatio v₀ v i| ≤ 1 / 8) ∧
    0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ∧
    α * (weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v) ≤
      592 * effectiveN r q + 26 + 13 * α * τ ∧
    α * (∑ i, (fittedLogRatio v₀ v i) ^ 2) ≤
      1152 * effectiveN r q + 48 + 24 * α * τ ∧
    α * (∑ i, (w i - 1) * fittedLogRatio v₀ v i) ≤
      592 * effectiveN r q + 26 + 12 * α * τ := by
  let v₀ := fittedValueSelection C hCcompact hCnonempty hCpos 1
  have hb := gammaEffectiveEvent_localization_bounds hα hQ hN hη hwidthScale hαQ hαN hα₀ V hw
  have hv₀ := fittedValueSelection_isMax C hCcompact hCnonempty hCpos 1
  have hvw := fittedValueSelection_isMax C hCcompact hCnonempty hCpos w
  have hnear₀ : weightedLogLikelihood w v₀ - τ ≤ weightedLogLikelihood w v := by
    have hh := hvw.2 _ hv₀.1
    dsimp [v₀]
    linarith
  have hl := fitted_radial_localization hC hCpos v₀ hv₀ V η hη hwidth
    w v hv τ hτ₀ hb.1 hb.2.2.2.2.1 hb.2.2.2.2.2 (by norm_num at *; exact hτ) hnear₀
  refine ⟨hl.1, hl.2.1, ?_, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hl.2.2.1 hα.le
    nlinarith [hb.2.2.1, hb.2.2.2.1]
  · have hh := mul_le_mul_of_nonneg_left hl.2.2.2.1 hα.le
    nlinarith [hb.2.2.1, hb.2.2.2.1]
  · have hh := mul_le_mul_of_nonneg_left hl.2.2.2.2 hα.le
    nlinarith [hb.2.2.1, hb.2.2.2.1]

theorem effective_dimension_finite_support_common_event
    {n r : ℕ} [Nonempty (Fin n)] {α q η : ℝ}
    (hα : 0 < α) (hq : 1 ≤ q) (hη : 0 ≤ η)
    (hwidthScale : η * Real.sqrt (α * (n : ℝ) * effectiveQ n q) ≤ 1)
    (hαQ : 1024 * effectiveQ n q ≤ α)
    (hαN : 2359296 * effectiveN r q ≤ α) (hα₀ : 12288 ≤ α)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (D : Set (Fin n → ℝ)) (hDclosed : IsClosed D) (hD : D ⊆ C)
    (hChull : C ⊆ convexHull ℝ D)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hrank : Module.finrank ℝ V ≤ r)
    (hwidth : ∀ u ∈ relativeFittedSet C (fittedValueSelection C hCcompact hCnonempty hCpos 1),
      ‖WithLp.toLp 2 u - V.starProjection (WithLp.toLp 2 u)‖ ≤ η) :
    let vhat := fittedValueSelection C hCcompact hCnonempty hCpos
    let v₀ := vhat 1
    let k := maximumIndependentSupport D vhat
    ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
      (gammaProductMeasure n α α).real Gᶜ ≤ 3 * Real.exp (-q) ∧
      ∀ w ∈ G, w ∈ gammaEffectiveEvent V r α q ∧ w ∈ positiveVectors n ∧ 0 < k w ∧
        Real.log (17 / 9 : ℝ) * ((k w - 1 : ℕ) : ℝ) < 1744 * effectiveN r q + 74 + q ∧
        ∀ (τ : ℝ), 0 ≤ τ → τ < 1 / 3072 → ∀ v ∈ C,
          weightedLogLikelihood w (vhat w) - τ ≤ weightedLogLikelihood w v →
          (∀ i, |fittedLogRatio v₀ v i| ≤ 1 / 8) ∧
          0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ∧
          α * (weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v) ≤
            592 * effectiveN r q + 26 + 13 * α * τ ∧
          α * (∑ i, (fittedLogRatio v₀ v i) ^ 2) ≤
            1152 * effectiveN r q + 48 + 24 * α * τ := by
  classical
  let vhat := fittedValueSelection C hCcompact hCnonempty hCpos
  let v₀ := vhat 1
  let k := maximumIndependentSupport D vhat
  let E := gammaEffectiveEvent V r α q
  let H := 1744 * effectiveN r q + 74
  let z₀ := fittedLogSelection C hCcompact hCnonempty hCpos 1
  let t := fittedLogDisplacement C hCcompact hCnonempty hCpos z₀
  have hn1 : 1 ≤ (n : ℝ) := by
    exact_mod_cast (show 1 ≤ n from Fin.pos_iff_nonempty.mpr inferInstance)
  have hQ : 0 ≤ effectiveQ n q := by
    have hh := Real.log_nonneg (show 1 ≤ 2 * (n : ℝ) by linarith)
    dsimp [effectiveQ]
    linarith
  have hN : 0 ≤ effectiveN r q := by
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ 5 by norm_num)
    dsimp [effectiveN]
    positivity
  have hEmeas : MeasurableSet E := (isClosed_gammaEffectiveEvent V r α q).measurableSet
  have hEpos : E ⊆ positiveVectors n := fun w hw ↦
    (gammaEffectiveEvent_localization_bounds hα hQ hN hη hwidthScale hαQ hαN hα₀ V hw).2.1
  have hloc : ∀ w ∈ E,
      (∀ i, |fittedLogRatio v₀ (vhat w) i| ≤ 1 / 8) ∧
      α * (∑ i, (w i - 1) * fittedLogRatio v₀ (vhat w) i +
        ∑ i, (fittedLogRatio v₀ (vhat w) i) ^ 2) ≤ H := by
    intro w hw
    have hl := gammaEffectiveEvent_fitted_localization hα hQ hN hη hwidthScale
      hαQ hαN hα₀ C hC hCcompact hCnonempty hCpos V hwidth hw (vhat w)
      (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).1 0 (by norm_num)
      (by norm_num) (by simp [vhat])
    refine ⟨hl.1, ?_⟩
    dsimp [H]
    nlinarith [hl.2.2.2.1, hl.2.2.2.2]
  have htRatio : ∀ w ∈ E, t w = fittedLogRatio v₀ (vhat w) := by
    intro w hw
    rw [show t w = fittedLogSelection C hCcompact hCnonempty hCpos w - z₀ from
      fittedLogDisplacement_eq C hCcompact hCnonempty hCpos z₀ (hEpos hw)]
    rfl
  have ht : ∀ w ∈ E, ∀ i, |t w i| ≤ 1 / 8 := by
    intro w hw
    rw [htRatio w hw]
    exact (hloc w hw).1
  have hcost : ∀ w ∈ E,
      α * (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2) ≤ H := by
    intro w hw
    rw [htRatio w hw]
    exact (hloc w hw).2
  let B : Set (Fin n → ℝ) := {w | w ∈ E ∧ H + q ≤ Real.log (17 / 9 : ℝ) * ((k w - 1 : ℕ) : ℝ)}
  have hkmeas : Measurable k := measurable_maximumIndependentSupport D hDclosed vhat
    (canonicalFittedValue_continuousOn C hC hCcompact hCnonempty hCpos)
  have hcast : Measurable (fun w ↦ ((k w - 1 : ℕ) : ℝ)) :=
    (measurable_of_countable (fun j : ℕ ↦ (j : ℝ))).comp (hkmeas.sub_const 1)
  have hBmeas : MeasurableSet B := hEmeas.inter
    (measurableSet_le measurable_const (measurable_const.mul hcast))
  have hBprob : (gammaProductMeasure n α α).real B ≤ Real.exp (-q) :=
    canonical_maximumIndependentSupport_gamma_tail hα C hC hCcompact hCnonempty hCpos
      D hDclosed hD z₀ hEmeas hEpos ht H q hcost
  let G := E \ B
  refine ⟨G, hEmeas.diff hBmeas, ?_, ?_⟩
  · letI : IsProbabilityMeasure (gammaMeasure α α) := isProbabilityMeasure_gammaMeasure hα hα
    letI : IsProbabilityMeasure (gammaProductMeasure n α α) := by
      dsimp [gammaProductMeasure]
      infer_instance
    have hEprob := gammaEffectiveEvent_failure_bound hα hq
      (show 4 * effectiveQ n q ≤ α by linarith)
      (show 4 * effectiveN r q ≤ α by linarith) V hrank
    have hcover : Gᶜ ⊆ Eᶜ ∪ B := by
      intro w hw
      by_cases hwe : w ∈ E
      · right
        by_contra hwb
        exact hw ⟨hwe, hwb⟩
      · exact Or.inl hwe
    calc
      (gammaProductMeasure n α α).real Gᶜ ≤ (gammaProductMeasure n α α).real (Eᶜ ∪ B) :=
        measureReal_mono hcover
      _ ≤ (gammaProductMeasure n α α).real Eᶜ + (gammaProductMeasure n α α).real B :=
        measureReal_union_le _ _
      _ ≤ 3 * Real.exp (-q) := by linarith
  · intro w hw
    have hwpos := hEpos hw.1
    have hkpos := maximumIndependentSupport_pos_of_mem_convexHull C hC hCcompact
      hCnonempty hCpos D hD w hwpos
      (hChull (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).1)
    have hsmall : Real.log (17 / 9 : ℝ) * ((k w - 1 : ℕ) : ℝ) < H + q :=
      lt_of_not_ge (fun hh ↦ hw.2 ⟨hw.1, hh⟩)
    refine ⟨hw.1, hwpos, hkpos, hsmall, ?_⟩
    intro τ hτ₀ hτ v hv hnear
    have hl := gammaEffectiveEvent_fitted_localization hα hQ hN hη hwidthScale
      hαQ hαN hα₀ C hC hCcompact hCnonempty hCpos V hwidth hw.1 v hv τ hτ₀ hτ hnear
    exact ⟨hl.1, hl.2.1, hl.2.2.1, hl.2.2.2.1⟩

theorem effective_dimension_scale_bounds {n r : ℕ} [Nonempty (Fin n)]
    {α q : ℝ} (hq : 1 ≤ q)
    (hscale : 10000000 * ((r : ℝ) + effectiveQ n q) ≤ α) :
    0 < α ∧ 1 ≤ effectiveQ n q ∧ 1 ≤ effectiveN r q ∧
      1024 * effectiveQ n q ≤ α ∧ 2359296 * effectiveN r q ≤ α ∧
      12288 ≤ α ∧ effectiveN r q ≤ 4 * ((r : ℝ) + q) := by
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hn1 : 1 ≤ (n : ℝ) := by
    exact_mod_cast (show 1 ≤ n from Fin.pos_iff_nonempty.mpr inferInstance)
  have hlogn : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
  have hlog5₀ : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog5₁ : Real.log (5 : ℝ) ≤ 4 := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
    norm_num at hh
    exact hh
  have hQ : q ≤ effectiveQ n q := by dsimp [effectiveQ]; linarith
  have hN₀ : q ≤ effectiveN r q := by
    dsimp [effectiveN]
    nlinarith [mul_nonneg hr hlog5₀]
  have hN₁ : effectiveN r q ≤ 4 * ((r : ℝ) + q) := by
    dsimp [effectiveN]
    nlinarith [mul_le_mul_of_nonneg_left hlog5₁ hr]
  have hNQ : effectiveN r q ≤ 4 * ((r : ℝ) + effectiveQ n q) := by linarith
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, hN₁⟩

theorem effective_dimension_support_numeric_bound {r k : ℕ} {q : ℝ}
    (hq : 1 ≤ q) (hk : 0 < k)
    (htail : Real.log (17 / 9 : ℝ) * ((k - 1 : ℕ) : ℝ) <
      1744 * effectiveN r q + 74 + q) :
    (k : ℝ) ≤ 10000000 * ((r : ℝ) + q) := by
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hlog5 : Real.log (5 : ℝ) ≤ 4 := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
    norm_num at hh
    exact hh
  have hN : effectiveN r q ≤ 4 * ((r : ℝ) + q) := by
    dsimp [effectiveN]
    nlinarith [mul_le_mul_of_nonneg_left hlog5 hr]
  have hκ : (1 / 4 : ℝ) ≤ Real.log (17 / 9 : ℝ) := by
    have hh := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 17 / 9 by norm_num)
    norm_num at hh
    linarith
  have hk1 : 1 ≤ k := hk
  rw [Nat.cast_sub hk1] at htail
  norm_num only [Nat.cast_one] at htail
  have hkr : 1 ≤ (k : ℝ) := by exact_mod_cast hk1
  have hh := mul_le_mul_of_nonneg_right hκ (show 0 ≤ (k : ℝ) - 1 by linarith)
  nlinarith

theorem effective_dimension_error_numeric_bound {r : ℕ} {α q τ X Y : ℝ}
    (hα : 0 < α) (hq : 1 ≤ q) (hτ : 0 ≤ τ)
    (hX : α * X ≤ 592 * effectiveN r q + 26 + 13 * α * τ)
    (hY : α * Y ≤ 1152 * effectiveN r q + 48 + 24 * α * τ) :
    X ≤ 10000000 * (((r : ℝ) + q) / α + τ) ∧
    Y ≤ 10000000 * (((r : ℝ) + q) / α + τ) := by
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have hlog5 : Real.log (5 : ℝ) ≤ 4 := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
    norm_num at hh
    exact hh
  have hN : effectiveN r q ≤ 4 * ((r : ℝ) + q) := by
    dsimp [effectiveN]
    nlinarith [mul_le_mul_of_nonneg_left hlog5 hr]
  have hατ : 0 ≤ α * τ := mul_nonneg hα.le hτ
  have heq : α * (10000000 * (((r : ℝ) + q) / α + τ)) =
      10000000 * ((r : ℝ) + q) + 10000000 * (α * τ) := by
    field_simp
  constructor
  · apply (mul_le_mul_iff_right₀ hα).mp
    rw [heq]
    nlinarith
  · apply (mul_le_mul_iff_right₀ hα).mp
    rw [heq]
    nlinarith

/-- Explicit universal constants for the finite-representation version of
effective sparsification. Every approximate-fit conclusion is simultaneous
over `v` and `tau` on the same measurable event. -/
theorem effective_dimension_finite_support
    {n r : ℕ} [Nonempty (Fin n)] {α q η : ℝ}
    (hq : 1 ≤ q) (hη : 0 ≤ η)
    (hscale : 10000000 * ((r : ℝ) + effectiveQ n q) ≤ α)
    (hwidthScale : η * Real.sqrt (α * (n : ℝ) * effectiveQ n q) ≤ 1)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (D : Set (Fin n → ℝ)) (hDclosed : IsClosed D) (hD : D ⊆ C)
    (hChull : C ⊆ convexHull ℝ D)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hrank : Module.finrank ℝ V ≤ r)
    (hwidth : ∀ u ∈ relativeFittedSet C (fittedValueSelection C hCcompact hCnonempty hCpos 1),
      ‖WithLp.toLp 2 u - V.starProjection (WithLp.toLp 2 u)‖ ≤ η) :
    let vhat := fittedValueSelection C hCcompact hCnonempty hCpos
    let v₀ := vhat 1
    ∃ G : Set (Fin n → ℝ), MeasurableSet G ∧
      (gammaProductMeasure n α α).real Gᶜ ≤ 3 * Real.exp (-q) ∧
      ∀ w ∈ G, (∀ i, |w i - 1| ≤ 2 * Real.sqrt (effectiveQ n q / α)) ∧
        w ∈ positiveVectors n ∧
        (maximumIndependentSupport D vhat w : ℝ) ≤ 10000000 * ((r : ℝ) + q) ∧
        0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 (vhat w) ∧
        weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 (vhat w) ≤
          10000000 * ((r : ℝ) + q) / α ∧
        (∑ i, (fittedLogRatio v₀ (vhat w) i) ^ 2) ≤ 10000000 * ((r : ℝ) + q) / α ∧
        ∀ (τ : ℝ), 0 ≤ τ → τ < 1 / 3072 → ∀ v ∈ C,
          weightedLogLikelihood w (vhat w) - τ ≤ weightedLogLikelihood w v →
          0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ∧
          weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ≤
            10000000 * (((r : ℝ) + q) / α + τ) ∧
          (∑ i, (fittedLogRatio v₀ v i) ^ 2) ≤
            10000000 * (((r : ℝ) + q) / α + τ) := by
  have hb := effective_dimension_scale_bounds hq hscale
  obtain ⟨G, hGmeas, hGprob, hG⟩ := effective_dimension_finite_support_common_event hb.1 hq hη
    hwidthScale hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2.1
    C hC hCcompact hCnonempty hCpos D hDclosed hD hChull V hrank hwidth
  refine ⟨G, hGmeas, hGprob, ?_⟩
  intro w hw
  have hh := (hG w hw).2
  have hsupport := effective_dimension_support_numeric_bound hq hh.2.1 hh.2.2.1
  have hexact := hh.2.2.2 0 (by norm_num) (by norm_num)
    (fittedValueSelection C hCcompact hCnonempty hCpos w)
    (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).1 (by simp)
  have herrors := effective_dimension_error_numeric_bound hb.1 hq (show (0 : ℝ) ≤ 0 by norm_num)
    hexact.2.2.1 hexact.2.2.2
  simp only [add_zero, ← mul_div_assoc] at herrors
  refine ⟨(hG w hw).1.1, hh.1, hsupport, hexact.2.1, herrors.1, herrors.2, ?_⟩
  intro τ hτ₀ hτ v hv hnear
  have hloc := hh.2.2.2 τ hτ₀ hτ v hv hnear
  have herr := effective_dimension_error_numeric_bound hb.1 hq hτ₀ hloc.2.2.1 hloc.2.2.2
  exact ⟨hloc.2.1, herr.1, herr.2⟩

end ReweightedNPMLE
