import ReweightedNPMLE.FittedContact
import ReweightedNPMLE.RadialLocalization
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

/-!
# Regularity of the fitted-value problem

This file proves the analytic regularity part of the paper's effective-dimension
argument.  Variational inequalities yield a quantitative local Lipschitz bound
for the unique fitted vector and its coordinatewise logarithm.  Mathlib's
Rademacher theorem then gives almost-everywhere differentiability.
-/

open Set MeasureTheory Filter
open scoped BigOperators NNReal

namespace ReweightedNPMLE

/-- A canonical fitted-value maximizer over a nonempty compact positive set.
For positive weights it is the unique fitted vector, but the definition is
available for all weights because existence only uses compactness. -/
noncomputable def fittedValueSelection {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) (w : Fin n → ℝ) : Fin n → ℝ :=
  Classical.choose (exists_fittedValue_maximizer hCcompact hCnonempty hCpos w)

theorem fittedValueSelection_isMax {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) (w : Fin n → ℝ) :
    IsMaxOn C (weightedLogLikelihood w)
      (fittedValueSelection C hCcompact hCnonempty hCpos w) :=
  Classical.choose_spec (exists_fittedValue_maximizer hCcompact hCnonempty hCpos w)

/-- Coordinatewise logarithm of the canonical fitted vector. -/
noncomputable def fittedLogSelection {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ Real.log (fittedValueSelection C hCcompact hCnonempty hCpos w i)

/-- First-order variational inequality at a positive fitted-value maximizer. -/
theorem fitted_maximizer_firstOrder_nonpos {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C)
    (hCpos : C ⊆ positiveVectors n)
    (w v a : Fin n → ℝ) (hv : IsMaxOn C (weightedLogLikelihood w) v)
    (ha : a ∈ C) :
    ∑ i, w i * ((a i - v i) / v i) ≤ 0 := by
  have hraw := likelihoodContactNumerator_le_total_of_isMaxOn
    hC hCpos w v a hv ha
  have hvpos := hCpos hv.1
  unfold likelihoodContactNumerator total at hraw
  have hid : (∑ i, w i * (a i / v i)) - ∑ i, w i =
      ∑ i, w i * ((a i - v i) / v i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(hvpos i).ne']
  rw [← hid]
  linarith

/-- The fitted log-vector is a monotone function of the likelihood weights. -/
theorem fittedLog_monotone {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {s : Set (Fin n → ℝ)}
    (hmax : ∀ w ∈ s, IsMaxOn C (weightedLogLikelihood w) (vhat w)) :
    ∀ w ∈ s, ∀ u ∈ s,
      0 ≤ ∑ i, (w i - u i) *
        (Real.log (vhat w i) - Real.log (vhat u i)) := by
  intro w hw u hu
  have hwu := (hmax w hw).2 (vhat u) (hmax u hu).1
  have huw := (hmax u hu).2 (vhat w) (hmax w hw).1
  unfold weightedLogLikelihood at hwu huw
  calc
    0 ≤ (∑ i, w i * Real.log (vhat w i)) -
        ∑ i, w i * Real.log (vhat u i) := sub_nonneg.mpr hwu
    _ ≤ ((∑ i, w i * Real.log (vhat w i)) -
        ∑ i, w i * Real.log (vhat u i)) +
        ((∑ i, u i * Real.log (vhat u i)) -
        ∑ i, u i * Real.log (vhat w i)) := by linarith
    _ = ∑ i, (w i - u i) *
        (Real.log (vhat w i) - Real.log (vhat u i)) := by
      simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
      ring

/-- Quantitative local Lipschitz bound for fitted values.  On a weight set with
coordinates at least `a`, and a feasible fitted set contained coordinatewise
in `[c,B]`, the constant is `n B²/(ac)` for the product sup norm. -/
theorem fittedValue_lipschitzOn {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C)
    (hCpos : C ⊆ positiveVectors n)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {s : Set (Fin n → ℝ)} {a c B : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hB : 0 < B)
    (hwa : ∀ w ∈ s, ∀ i, a ≤ w i)
    (hvc : ∀ w ∈ s, ∀ i, c ≤ vhat w i)
    (hvB : ∀ w ∈ s, ∀ i, vhat w i ≤ B)
    (hmax : ∀ w ∈ s, IsMaxOn C (weightedLogLikelihood w) (vhat w)) :
    LipschitzOnWith
      ⟨(n : ℝ) * B ^ 2 / (a * c), by positivity⟩ vhat s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro w hw u hu
  let dv : Fin n → ℝ := fun i ↦ vhat w i - vhat u i
  let dw : Fin n → ℝ := fun i ↦ w i - u i
  let S : ℝ := ∑ i, (dv i) ^ 2
  have hwfirst := fitted_maximizer_firstOrder_nonpos hC hCpos
    w (vhat w) (vhat u) (hmax w hw) (hmax u hu).1
  have hufirst := fitted_maximizer_firstOrder_nonpos hC hCpos
    u (vhat u) (vhat w) (hmax u hu) (hmax w hw).1
  have hwfirst' : 0 ≤ ∑ i, w i * (dv i / vhat w i) := by
    have heq : (∑ i, w i * ((vhat u i - vhat w i) / vhat w i)) =
        -(∑ i, w i * (dv i / vhat w i)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp [dv]
      ring
    rw [heq] at hwfirst
    linarith
  have hcompare : 0 ≤ ∑ i,
      (w i / vhat w i - u i / vhat u i) * dv i := by
    have heq : (∑ i, (w i / vhat w i - u i / vhat u i) * dv i) =
        (∑ i, w i * (dv i / vhat w i)) +
          -(∑ i, u i * ((vhat w i - vhat u i) / vhat u i)) := by
      calc
        (∑ i, (w i / vhat w i - u i / vhat u i) * dv i) =
            ∑ i, (w i * (dv i / vhat w i) -
              u i * ((vhat w i - vhat u i) / vhat u i)) := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp [dv]
          ring
        _ = (∑ i, w i * (dv i / vhat w i)) -
            ∑ i, u i * ((vhat w i - vhat u i) / vhat u i) :=
          by rw [Finset.sum_sub_distrib]
        _ = _ := by ring
    rw [heq]
    exact add_nonneg hwfirst' (neg_nonneg.mpr hufirst)
  have hidentity : (∑ i,
      (w i / vhat w i - u i / vhat u i) * dv i) =
      -(∑ i, w i * (dv i) ^ 2 / (vhat w i * vhat u i)) +
        ∑ i, dw i * dv i / vhat u i := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hvw0 : vhat w i ≠ 0 := (lt_of_lt_of_le hc (hvc w hw i)).ne'
    have hvu0 : vhat u i ≠ 0 := (lt_of_lt_of_le hc (hvc u hu i)).ne'
    dsimp [dv, dw]
    field_simp [hvw0, hvu0]
    ring
  have hcurv : (a / B ^ 2) * S ≤
      ∑ i, w i * (dv i) ^ 2 / (vhat w i * vhat u i) := by
    dsimp [S]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hvwpos : 0 < vhat w i := lt_of_lt_of_le hc (hvc w hw i)
    have hvupos : 0 < vhat u i := lt_of_lt_of_le hc (hvc u hu i)
    have hprod : vhat w i * vhat u i ≤ B ^ 2 := by
      rw [pow_two]
      exact mul_le_mul (hvB w hw i) (hvB u hu i)
        hvupos.le (le_trans hvupos.le (hvB u hu i))
    have hcoeff : a / B ^ 2 ≤ w i / (vhat w i * vhat u i) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hB) (mul_pos hvwpos hvupos)]
      calc
        a * (vhat w i * vhat u i) ≤ a * B ^ 2 :=
          mul_le_mul_of_nonneg_left hprod ha.le
        _ ≤ w i * B ^ 2 :=
          mul_le_mul_of_nonneg_right (hwa w hw i) (sq_nonneg B)
    have hsquare : 0 ≤ (dv i) ^ 2 := sq_nonneg _
    convert mul_le_mul_of_nonneg_right hcoeff hsquare using 1 <;> ring
  have hcross : ∑ i, dw i * dv i / vhat u i ≤
      (n : ℝ) / c * ‖w - u‖ * ‖vhat w - vhat u‖ := by
    calc
      ∑ i, dw i * dv i / vhat u i ≤
          ∑ _i : Fin n, (‖w - u‖ * ‖vhat w - vhat u‖ / c) := by
        apply Finset.sum_le_sum
        intro i _
        have hden : c ≤ vhat u i := hvc u hu i
        have hdenpos : 0 < vhat u i := lt_of_lt_of_le hc hden
        have hdw : |dw i| ≤ ‖w - u‖ := by
          simpa [dw, Real.norm_eq_abs] using norm_le_pi_norm (w - u) i
        have hdv : |dv i| ≤ ‖vhat w - vhat u‖ := by
          simpa [dv, Real.norm_eq_abs] using norm_le_pi_norm (vhat w - vhat u) i
        calc
          dw i * dv i / vhat u i ≤ |dw i * dv i / vhat u i| := le_abs_self _
          _ = |dw i| * |dv i| / vhat u i := by
            rw [abs_div, abs_mul, abs_of_pos hdenpos]
          _ ≤ (‖w - u‖ * ‖vhat w - vhat u‖) / vhat u i := by
            gcongr
          _ ≤ (‖w - u‖ * ‖vhat w - vhat u‖) / c := by
            exact div_le_div_of_nonneg_left
              (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hc hden
      _ = (n : ℝ) / c * ‖w - u‖ * ‖vhat w - vhat u‖ := by
        simp [div_eq_mul_inv]
        ring
  have hmain : (a / B ^ 2) * S ≤
      (n : ℝ) / c * ‖w - u‖ * ‖vhat w - vhat u‖ := by
    rw [hidentity] at hcompare
    linarith
  have hSnonneg : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ sq_nonneg (dv i)
  have hnormsqrt : ‖vhat w - vhat u‖ ≤ Real.sqrt S := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)).2
    intro i
    simpa [dv, Real.norm_eq_abs] using abs_le_sqrt_sum_sq dv i
  have hnormsq : ‖vhat w - vhat u‖ ^ 2 ≤ S := by
    nlinarith [Real.sq_sqrt hSnonneg, norm_nonneg (vhat w - vhat u)]
  have hquad : (a / B ^ 2) * ‖vhat w - vhat u‖ ^ 2 ≤
      (n : ℝ) / c * ‖w - u‖ * ‖vhat w - vhat u‖ :=
    (mul_le_mul_of_nonneg_left hnormsq (div_nonneg ha.le (sq_nonneg B))).trans hmain
  change dist (vhat w) (vhat u) ≤
    ((n : ℝ) * B ^ 2 / (a * c)) * dist w u
  rw [dist_eq_norm, dist_eq_norm]
  by_cases hvzero : ‖vhat w - vhat u‖ = 0
  · rw [hvzero]
    exact mul_nonneg
      (div_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg B))
        (mul_nonneg ha.le hc.le)) (norm_nonneg _)
  · have hvpos : 0 < ‖vhat w - vhat u‖ := lt_of_le_of_ne
      (norm_nonneg _) (Ne.symm hvzero)
    have hscaled : a * c * ‖vhat w - vhat u‖ ≤
        (n : ℝ) * B ^ 2 * ‖w - u‖ := by
      have hquad' : a * c * ‖vhat w - vhat u‖ ^ 2 ≤
          (n : ℝ) * B ^ 2 * ‖w - u‖ * ‖vhat w - vhat u‖ := by
        calc
          a * c * ‖vhat w - vhat u‖ ^ 2 =
              (c * B ^ 2) * ((a / B ^ 2) * ‖vhat w - vhat u‖ ^ 2) := by
            field_simp [hB.ne']
          _ ≤ (c * B ^ 2) * ((n : ℝ) / c * ‖w - u‖ *
              ‖vhat w - vhat u‖) :=
            mul_le_mul_of_nonneg_left hquad (by positivity)
          _ = (n : ℝ) * B ^ 2 * ‖w - u‖ * ‖vhat w - vhat u‖ := by
            field_simp [hc.ne']
      apply (mul_le_mul_iff_right₀ hvpos).mp
      simpa only [mul_assoc, mul_left_comm, mul_comm, pow_two] using hquad'
    rw [show (n : ℝ) * B ^ 2 / (a * c) * ‖w - u‖ =
      ((n : ℝ) * B ^ 2 * ‖w - u‖) / (a * c) by ring]
    exact (le_div_iff₀ (mul_pos ha hc)).2 (by simpa [mul_comm] using hscaled)

/-- The logarithm is `c⁻¹`-Lipschitz on `[c,∞)`. -/
theorem abs_log_sub_log_le_div {c x y : ℝ}
    (hc : 0 < c) (hx : c ≤ x) (hy : c ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / c := by
  have hxpos : 0 < x := hc.trans_le hx
  have hypos : 0 < y := hc.trans_le hy
  rcases le_total x y with hxy | hyx
  · have hlog : Real.log y - Real.log x ≤ y / x - 1 := by
      rw [← Real.log_div hypos.ne' hxpos.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hypos hxpos)
    have hfrac : y / x - 1 ≤ (y - x) / c := by
      rw [show y / x - 1 = (y - x) / x by field_simp [hxpos.ne']]
      exact div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hc hx
    calc
      |Real.log x - Real.log y| = Real.log y - Real.log x := by
        rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hxpos hxy))]
        ring
      _ ≤ y / x - 1 := hlog
      _ ≤ (y - x) / c := hfrac
      _ = |x - y| / c := by rw [abs_of_nonpos (sub_nonpos.mpr hxy)]; ring
  · have hlog : Real.log x - Real.log y ≤ x / y - 1 := by
      rw [← Real.log_div hxpos.ne' hypos.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hxpos hypos)
    have hfrac : x / y - 1 ≤ (x - y) / c := by
      rw [show x / y - 1 = (x - y) / y by field_simp [hypos.ne']]
      exact div_le_div_of_nonneg_left (sub_nonneg.mpr hyx) hc hy
    calc
      |Real.log x - Real.log y| = Real.log x - Real.log y := by
        rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hypos hyx))]
      _ ≤ x / y - 1 := hlog
      _ ≤ (x - y) / c := hfrac
      _ = |x - y| / c := by rw [abs_of_nonneg (sub_nonneg.mpr hyx)]

/-- Coordinatewise logarithm preserves Lipschitzness when all coordinates
have a common positive lower bound. -/
theorem coordinateLog_lipschitzOn {n : ℕ} [Nonempty (Fin n)]
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {s : Set (Fin n → ℝ)} {K : ℝ≥0} {c : ℝ}
    (hc : 0 < c) (hvc : ∀ w ∈ s, ∀ i, c ≤ vhat w i)
    (hlip : LipschitzOnWith K vhat s) :
    LipschitzOnWith ⟨(K : ℝ) / c, by positivity⟩
      (fun w i ↦ Real.log (vhat w i)) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro w hw u hu
  rw [dist_eq_norm, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _))).2
  intro i
  calc
    ‖Real.log (vhat w i) - Real.log (vhat u i)‖ =
        |Real.log (vhat w i) - Real.log (vhat u i)| := Real.norm_eq_abs _
    _ ≤ |vhat w i - vhat u i| / c :=
      abs_log_sub_log_le_div hc (hvc w hw i) (hvc u hu i)
    _ ≤ ‖vhat w - vhat u‖ / c := by
      exact div_le_div_of_nonneg_right
        (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (vhat w - vhat u) i) hc.le
    _ ≤ (K : ℝ) * ‖w - u‖ / c := by
      exact div_le_div_of_nonneg_right
        (by simpa [dist_eq_norm] using hlip.dist_le_mul w hw u hu) hc.le
    _ = ((K : ℝ) / c) * ‖w - u‖ := by ring

/-- Quantitative local Lipschitz bound for the fitted log-vector. -/
theorem fittedLog_lipschitzOn {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C)
    (hCpos : C ⊆ positiveVectors n)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {s : Set (Fin n → ℝ)} {a c B : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hB : 0 < B)
    (hwa : ∀ w ∈ s, ∀ i, a ≤ w i)
    (hvc : ∀ w ∈ s, ∀ i, c ≤ vhat w i)
    (hvB : ∀ w ∈ s, ∀ i, vhat w i ≤ B)
    (hmax : ∀ w ∈ s, IsMaxOn C (weightedLogLikelihood w) (vhat w)) :
    LipschitzOnWith
      ⟨((n : ℝ) * B ^ 2 / (a * c)) / c, by positivity⟩
      (fun w i ↦ Real.log (vhat w i)) s := by
  exact coordinateLog_lipschitzOn vhat hc hvc
    (fittedValue_lipschitzOn hC hCpos vhat ha hc hB hwa hvc hvB hmax)

/-- Rademacher regularity for the fitted log-vector on a measurable weight
set.  This is the almost-everywhere differentiability assertion in the
paper's fitted-value regularity lemma. -/
theorem fittedLog_ae_differentiableWithinAt {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C)
    (hCpos : C ⊆ positiveVectors n)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) {a c B : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hB : 0 < B)
    (hwa : ∀ w ∈ s, ∀ i, a ≤ w i)
    (hvc : ∀ w ∈ s, ∀ i, c ≤ vhat w i)
    (hvB : ∀ w ∈ s, ∀ i, vhat w i ≤ B)
    (hmax : ∀ w ∈ s, IsMaxOn C (weightedLogLikelihood w) (vhat w)) :
    ∀ᵐ w ∂(volume.restrict s),
      DifferentiableWithinAt ℝ (fun w i ↦ Real.log (vhat w i)) s w := by
  exact (fittedLog_lipschitzOn hC hCpos vhat ha hc hB
    hwa hvc hvB hmax).ae_differentiableWithinAt hs

/-- Compactness inside the positive orthant gives common positive lower
and upper bounds for every feasible coordinate. -/
theorem exists_uniform_positive_coordinate_bounds {n : ℕ}
    {C : Set (Fin n → ℝ)} (hCcompact : IsCompact C)
    (hCpos : C ⊆ positiveVectors n) :
    ∃ c B : ℝ, 0 < c ∧ 0 < B ∧ ∀ v ∈ C, ∀ i, c ≤ v i ∧ v i ≤ B := by
  let z : (Fin n → ℝ) → (Fin n → ℝ) := fun v i ↦ Real.log (v i)
  have hz : ContinuousOn z C := by
    apply continuousOn_pi.mpr
    intro i
    exact (continuous_apply i).continuousOn.log (fun v hv ↦ (hCpos hv i).ne')
  obtain ⟨M, hMpos, hM⟩ := (hCcompact.image_of_continuousOn hz).isBounded.exists_pos_norm_le
  refine ⟨Real.exp (-M), Real.exp M, Real.exp_pos _, Real.exp_pos _, ?_⟩
  intro v hv i
  have hi : |Real.log (v i)| ≤ M := by
    exact (norm_le_pi_norm (z v) i).trans (hM (z v) ⟨v, hv, rfl⟩)
  rw [abs_le] at hi
  constructor
  · rw [← Real.exp_log (hCpos hv i)]
    exact Real.exp_le_exp.mpr hi.1
  · rw [← Real.exp_log (hCpos hv i)]
    exact Real.exp_le_exp.mpr hi.2

theorem exists_local_positive_weight_lower_bound {n : ℕ}
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    ∃ a : ℝ, 0 < a ∧ ∃ s : Set (Fin n → ℝ),
      s ∈ nhds w ∧ ∀ u ∈ s, ∀ i, a ≤ u i := by
  have hsingle : ({w} : Set (Fin n → ℝ)) ⊆ positiveVectors n := by
    intro v hv
    simpa using (mem_singleton_iff.mp hv ▸ hw)
  obtain ⟨b, B, hb, _, hbound⟩ :=
    exists_uniform_positive_coordinate_bounds isCompact_singleton hsingle
  have hbw : ∀ i, b ≤ w i := fun i ↦ (hbound w (mem_singleton w) i).1
  let s : Set (Fin n → ℝ) := {u | ∀ i, b / 2 < u i}
  refine ⟨b / 2, by positivity, s, ?_, ?_⟩
  · change ∀ᶠ u in nhds w, ∀ i, b / 2 < u i
    rw [Filter.eventually_all]
    intro i
    exact (continuous_apply i).continuousAt.tendsto
      (Ioi_mem_nhds (by linarith [hbw i]))
  · intro u hu i
    exact (hu i).le

theorem isOpen_positiveVectors (n : ℕ) : IsOpen (positiveVectors n) := by
  have heq : positiveVectors n = ⋂ i : Fin n, {w : Fin n → ℝ | 0 < w i} := by
    ext w
    simp [positiveVectors]
  rw [heq]
  exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (continuous_apply i)

theorem canonicalFittedLog_ae_differentiableAt
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) :
    ∀ᵐ w ∂volume, w ∈ positiveVectors n →
      DifferentiableAt ℝ (fittedLogSelection C hCcompact hCnonempty hCpos) w := by
  obtain ⟨c, B, hc, hB, hbound⟩ := exists_uniform_positive_coordinate_bounds hCcompact hCpos
  let s : ℕ → Set (Fin n → ℝ) := fun m ↦ {w | ∀ i, 1 / ((m : ℝ) + 1) < w i}
  have hsopen : ∀ m, IsOpen (s m) := by
    intro m
    have heq : s m = ⋂ i : Fin n, {w : Fin n → ℝ | 1 / ((m : ℝ) + 1) < w i} := by
      ext w
      simp [s]
    rw [heq]
    exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (continuous_apply i)
  have hdiff : ∀ m, ∀ᵐ w ∂volume, w ∈ s m →
      DifferentiableWithinAt ℝ (fittedLogSelection C hCcompact hCnonempty hCpos) (s m) w := by
    intro m
    have hlip := fittedLog_lipschitzOn (s := s m) hC hCpos
      (fittedValueSelection C hCcompact hCnonempty hCpos)
      (show 0 < 1 / ((m : ℝ) + 1) by positivity) hc hB
      (fun w hw i ↦ (hw i).le)
      (fun w _ i ↦ (hbound _ (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).1 i).1)
      (fun w _ i ↦ (hbound _ (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).1 i).2)
      (fun w _ ↦ fittedValueSelection_isMax C hCcompact hCnonempty hCpos w)
    exact hlip.ae_differentiableWithinAt_of_mem
  filter_upwards [ae_all_iff.2 hdiff] with w hw hpos
  have hsingle : ({w} : Set (Fin n → ℝ)) ⊆ positiveVectors n := by
    simpa using hpos
  obtain ⟨a, D, ha, _, hwa⟩ :=
    exists_uniform_positive_coordinate_bounds isCompact_singleton hsingle
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt ha
  have hws : w ∈ s m := fun i ↦ hm.trans_le (hwa w (mem_singleton w) i).1
  exact (hw m hws).differentiableAt ((hsopen m).mem_nhds hws)

theorem canonicalFittedLog_continuousAt
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    {w : Fin n → ℝ} (hw : w ∈ positiveVectors n) :
    ContinuousAt (fittedLogSelection C hCcompact hCnonempty hCpos) w := by
  obtain ⟨c, B, hc, hB, hbound⟩ := exists_uniform_positive_coordinate_bounds hCcompact hCpos
  obtain ⟨a, ha, s, hs, hwa⟩ := exists_local_positive_weight_lower_bound w hw
  have hlip := fittedLog_lipschitzOn (s := s) hC hCpos
    (fittedValueSelection C hCcompact hCnonempty hCpos) ha hc hB hwa
    (fun u _ i ↦ (hbound _ (fittedValueSelection_isMax C hCcompact hCnonempty hCpos u).1 i).1)
    (fun u _ i ↦ (hbound _ (fittedValueSelection_isMax C hCcompact hCnonempty hCpos u).1 i).2)
    (fun u _ ↦ fittedValueSelection_isMax C hCcompact hCnonempty hCpos u)
  exact hlip.continuousOn.continuousAt hs

theorem canonicalFittedLog_continuousOn
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) :
    ContinuousOn (fittedLogSelection C hCcompact hCnonempty hCpos) (positiveVectors n) := by
  intro w hw
  exact (canonicalFittedLog_continuousAt C hC hCcompact hCnonempty hCpos hw).continuousWithinAt

/-- The canonical fitted-log displacement, extended by zero outside the
positive orthant so that it is globally measurable. -/
noncomputable def fittedLogDisplacement {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCcompact : IsCompact C)
    (hCnonempty : C.Nonempty) (hCpos : C ⊆ positiveVectors n)
    (z₀ : Fin n → ℝ) : (Fin n → ℝ) → (Fin n → ℝ) := by
  classical
  exact (positiveVectors n).piecewise
    (fun w ↦ fittedLogSelection C hCcompact hCnonempty hCpos w - z₀) (fun _ ↦ 0)

theorem fittedLogDisplacement_eq {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCcompact : IsCompact C)
    (hCnonempty : C.Nonempty) (hCpos : C ⊆ positiveVectors n)
    (z₀ : Fin n → ℝ) {w : Fin n → ℝ} (hw : w ∈ positiveVectors n) :
    fittedLogDisplacement C hCcompact hCnonempty hCpos z₀ w =
      fittedLogSelection C hCcompact hCnonempty hCpos w - z₀ := by
  classical
  simp [fittedLogDisplacement, hw]

theorem measurable_fittedLogDisplacement
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) (z₀ : Fin n → ℝ) :
    Measurable (fittedLogDisplacement C hCcompact hCnonempty hCpos z₀) := by
  classical
  exact ((canonicalFittedLog_continuousOn C hC hCcompact hCnonempty hCpos).sub
    continuous_const.continuousOn).measurable_piecewise
      continuous_const.continuousOn (isOpen_positiveVectors n).measurableSet

theorem fittedLogDisplacement_hasFDerivAt
    {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCcompact : IsCompact C)
    (hCnonempty : C.Nonempty) (hCpos : C ⊆ positiveVectors n)
    (z₀ : Fin n → ℝ) {w : Fin n → ℝ} (hw : w ∈ positiveVectors n)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fittedLogSelection C hCcompact hCnonempty hCpos) J w) :
    HasFDerivAt (fittedLogDisplacement C hCcompact hCnonempty hCpos z₀) J w := by
  apply (hz.sub_const z₀).congr_of_eventuallyEq
  filter_upwards [(isOpen_positiveVectors n).mem_nhds hw] with q hq
  exact fittedLogDisplacement_eq C hCcompact hCnonempty hCpos z₀ hq

theorem canonicalFittedValue_continuousOn
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) :
    ContinuousOn (fittedValueSelection C hCcompact hCnonempty hCpos) (positiveVectors n) := by
  apply continuousOn_pi.mpr
  intro i
  have hlog := (continuous_apply i).comp_continuousOn
    (canonicalFittedLog_continuousOn C hC hCcompact hCnonempty hCpos)
  apply (Real.continuous_exp.comp_continuousOn hlog).congr
  intro w hw
  exact (Real.exp_log (hCpos (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).1 i)).symm

end ReweightedNPMLE
