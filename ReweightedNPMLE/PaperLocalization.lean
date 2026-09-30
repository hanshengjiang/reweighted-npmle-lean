import ReweightedNPMLE.FittedLocalization
import ReweightedNPMLE.FittedDeterminantMoment
import ReweightedNPMLE.MeasureExtremeSupport
import Mathlib.Tactic

/-! # The paper's compact radial event and full-law determinant moment

Positivity is redundant in the event definition because the coordinate bound
already forces it. The event below is therefore exactly the paper event,
with `rho = 1/16`, as a closed subset of a compact positive weight box.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace ReweightedNPMLE

def paperRadialEvent {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (η : ℝ) : Set (Fin n → ℝ) :=
  {w | (∀ i, |w i - 1| ≤ 1 / 16) ∧
    ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖ ≤ (1 / 16 : ℝ) / 24 ∧
    η * ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖ ≤ (1 / 16 : ℝ) ^ 2 / 24}

theorem paperRadialEvent_subset_positive {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (η : ℝ) :
    paperRadialEvent V η ⊆ positiveVectors n := by
  intro w hw i
  have hi := neg_le_of_abs_le (hw.1 i)
  linarith

theorem isCompact_paperRadialEvent {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (η : ℝ) :
    IsCompact (paperRadialEvent V η) := by
  have hc : IsClosed {w : Fin n → ℝ | ∀ i, |w i - 1| ≤ 1 / 16} := by
    have heq : {w : Fin n → ℝ | ∀ i, |w i - 1| ≤ 1 / 16} =
        ⋂ i : Fin n, {w : Fin n → ℝ | |w i - 1| ≤ 1 / 16} := by
      ext w
      simp
    rw [heq]
    exact isClosed_iInter fun i ↦ isClosed_le (by fun_prop) continuous_const
  have hproj : Continuous (fun w : Fin n → ℝ ↦
      ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖) := by fun_prop
  have hres : Continuous (fun w : Fin n → ℝ ↦
      η * ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖) := by fun_prop
  have hclosed : IsClosed (paperRadialEvent V η) :=
    hc.inter ((isClosed_le hproj continuous_const).inter
      (isClosed_le hres continuous_const))
  apply (isCompact_Icc : IsCompact (Icc (fun _ : Fin n ↦ (15 / 16 : ℝ))
      (fun _ : Fin n ↦ (17 / 16 : ℝ)))).of_isClosed_subset hclosed
  intro w hw
  constructor <;> intro i <;> have hi := abs_le.mp (hw.1 i) <;> linarith

theorem paper_radial_localization {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hCpos : C ⊆ positiveVectors n)
    (v₀ : Fin n → ℝ) (hv₀ : IsMaxOn C (weightedLogLikelihood 1) v₀)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) {η : ℝ} (hη : 0 ≤ η)
    (hwidth : ∀ u ∈ relativeFittedSet C v₀,
      ‖WithLp.toLp 2 u - V.starProjection (WithLp.toLp 2 u)‖ ≤ η)
    {w : Fin n → ℝ} (hw : w ∈ paperRadialEvent V η)
    {v : Fin n → ℝ} (hv : v ∈ C) {τ : ℝ} (hτ₀ : 0 ≤ τ)
    (hτ : τ < (1 / 16 : ℝ) ^ 2 / 12)
    (hnear : weightedLogLikelihood w v₀ - τ ≤ weightedLogLikelihood w v) :
    let u := relativeFittedVector v₀ v
    let A := ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖
    let E := η * ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖
    Real.sqrt (∑ i, u i ^ 2) < 1 / 16 ∧
    (∑ i, u i ^ 2) ≤ 36 * A ^ 2 + 12 * E + 12 * τ ∧
    (∀ i, |fittedLogRatio v₀ v i| < 1 / 8) ∧
    0 ≤ weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ∧
    weightedLogLikelihood 1 v₀ - weightedLogLikelihood 1 v ≤ 37 * A ^ 2 + 13 * E + 13 * τ ∧
    (∑ i, fittedLogRatio v₀ v i ^ 2) ≤ 72 * A ^ 2 + 24 * E + 24 * τ ∧
    (∑ i, (w i - 1) * fittedLogRatio v₀ v i) ≤ 37 * A ^ 2 + 13 * E + 12 * τ := by
  let u := relativeFittedVector v₀ v
  have hlog := relativeFittedVector_log_one_add v₀ v (hCpos hv₀.1) (hCpos hv)
  have hnear' : -τ ≤ ∑ i, w i * Real.log (1 + u i) := by
    have heq : (∑ i, w i * Real.log (1 + u i)) =
        weightedLogLikelihood w v - weightedLogLikelihood w v₀ := by
      rw [weightedLogLikelihood_sub_eq_logRatio]
      exact congrArg (fun z : Fin n → ℝ ↦ ∑ i, w i * z i) hlog
    rw [heq]
    linarith
  have hr := radial_localization_of_projection (relativeFittedSet C v₀)
    (convex_relativeFittedSet hC v₀) (zero_mem_relativeFittedSet hv₀.1 (hCpos hv₀.1))
    V η hη hwidth w u ⟨v, hv, rfl⟩
    (relativeFittedVector_one_add_pos v₀ v (hCpos hv₀.1) (hCpos hv)) τ hτ₀
    hw.1 hw.2.1 hw.2.2 (relativeFittedSet_firstOrder hC hCpos v₀ hv₀) hτ hnear'
  have hf := fitted_radial_localization hC hCpos v₀ hv₀ V η hη hwidth
    w v hv τ hτ₀ hw.1 hw.2.1 hw.2.2 hτ hnear
  refine ⟨hr.1, hr.2.1, ?_, hf.2⟩
  intro i
  have hui : |u i| < 1 / 16 := (abs_le_sqrt_sum_sq u i).trans_lt hr.1
  have hui' : |u i| < 1 := hui.trans (by norm_num)
  have hl := abs_log_one_add_le hui'
  have hfrac : |u i| / (1 - |u i|) < 1 / 8 := by
    rw [div_lt_iff₀ (by linarith : 0 < 1 - |u i|)]
    linarith
  have hz := congrFun hlog i
  change Real.log (1 + u i) = fittedLogRatio v₀ v i at hz
  rw [← hz]
  exact hl.trans_lt hfrac

theorem canonical_paper_radial_exact_fit {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty) (hCpos : C ⊆ positiveVectors n)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) {η : ℝ} (hη : 0 ≤ η)
    (hwidth : ∀ u ∈ relativeFittedSet C (fittedValueSelection C hCcompact hCnonempty hCpos 1),
      ‖WithLp.toLp 2 u - V.starProjection (WithLp.toLp 2 u)‖ ≤ η)
    {w : Fin n → ℝ} (hw : w ∈ paperRadialEvent V η) :
    let z₀ := fittedLogSelection C hCcompact hCnonempty hCpos 1
    let t := fittedLogDisplacement C hCcompact hCnonempty hCpos z₀ w
    (∀ i, |t i| < 1 / 8) ∧ 0 ≤ (∑ i, (w i - 1) * t i) ∧
      (∑ i, (w i - 1) * t i) ≤
        37 * ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖ ^ 2 +
        13 * (η * ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖) := by
  let v := fittedValueSelection C hCcompact hCnonempty hCpos
  let z₀ := fittedLogSelection C hCcompact hCnonempty hCpos 1
  let t := fittedLogDisplacement C hCcompact hCnonempty hCpos z₀ w
  have hmax := fittedValueSelection_isMax C hCcompact hCnonempty hCpos w
  have hmax₀ := fittedValueSelection_isMax C hCcompact hCnonempty hCpos 1
  have hnear : weightedLogLikelihood w (v 1) - 0 ≤ weightedLogLikelihood w (v w) := by
    simpa only [sub_zero] using hmax.2 (v 1) hmax₀.1
  have hr := paper_radial_localization hC hCpos (v 1) hmax₀ V hη hwidth hw hmax.1
    (τ := 0) (by norm_num) (by norm_num) hnear
  have ht : t = fittedLogRatio (v 1) (v w) := by
    dsimp only [t]
    rw [fittedLogDisplacement_eq C hCcompact hCnonempty hCpos z₀
      (paperRadialEvent_subset_positive V η hw)]
    rfl
  change (∀ i, |t i| < 1 / 8) ∧ 0 ≤ (∑ i, (w i - 1) * t i) ∧
    (∑ i, (w i - 1) * t i) ≤
      37 * ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖ ^ 2 +
      13 * (η * ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖)
  rw [ht]
  refine ⟨hr.2.2.1, ?_, ?_⟩
  · have hid : (∑ i, (w i - 1) * fittedLogRatio (v 1) (v w) i) =
        weightedLogLikelihood w (v w) - weightedLogLikelihood w (v 1) +
          (weightedLogLikelihood 1 (v 1) - weightedLogLikelihood 1 (v w)) := by
      simp only [weightedLogLikelihood, fittedLogRatio, mul_sub, sub_mul,
        Pi.one_apply, one_mul, Finset.sum_sub_distrib]
      ring
    rw [hid]
    exact add_nonneg (by linarith) hr.2.2.2.1
  · simpa only [mul_zero, add_zero] using hr.2.2.2.2.2.2

theorem canonical_maximumExtremeSupport_paper_gamma_moment
    {Θ : Type*} [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {n : ℕ} [Nonempty (Fin n)] {α η : ℝ} (hα : 0 < α) (hη : 0 ≤ η)
    (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty) (hCpos : C ⊆ positiveVectors n)
    (hAC : range A ⊆ C)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hwidth : ∀ u ∈ relativeFittedSet C (fittedValueSelection C hCcompact hCnonempty hCpos 1),
      ‖WithLp.toLp 2 u - V.starProjection (WithLp.toLp 2 u)‖ ≤ η) :
    let v := fittedValueSelection C hCcompact hCnonempty hCpos
    let t := fittedLogDisplacement C hCcompact hCnonempty hCpos
      (fittedLogSelection C hCcompact hCnonempty hCpos 1)
    ∫⁻ w in paperRadialEvent V η, ENNReal.ofReal
        ((17 / 9 : ℝ) ^ (maximumExtremeSupport A v w - 1) *
          Real.exp (-α * ((∑ i, (w i - 1) * t w i) + ∑ i, t w i ^ 2)))
      ∂gammaProductMeasure n α α ≤ 1 := by
  dsimp only
  let v := fittedValueSelection C hCcompact hCnonempty hCpos
  have hstat : maximumExtremeSupport A v = maximumIndependentSupport (range A) v :=
    funext (maximumExtremeSupport_eq_maximumIndependentSupport A hA hC hCpos hAC v
      (fun w _ ↦ fittedValueSelection_isMax C hCcompact hCnonempty hCpos w))
  rw [hstat]
  exact canonical_maximumIndependentSupport_gamma_moment hα C hC hCcompact hCnonempty hCpos
    (range A) (isCompact_range hA).isClosed hAC _
    (isCompact_paperRadialEvent V η).measurableSet (paperRadialEvent_subset_positive V η)
    (fun w hw i ↦ (canonical_paper_radial_exact_fit C hC hCcompact hCnonempty hCpos V hη
      hwidth hw).1 i |>.le)

end ReweightedNPMLE
