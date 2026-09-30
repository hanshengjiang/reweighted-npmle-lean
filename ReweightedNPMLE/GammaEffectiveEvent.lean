import ReweightedNPMLE.GammaProjection
import ReweightedNPMLE.GaussianWidth
import Mathlib.Tactic

/-!
# Common Gamma concentration and localization event

The projected-energy and maximum-coordinate bounds hold jointly with
failure probability at most `2 exp(-q)`.  Explicit scale conditions imply
all radial localization hypotheses and the sharp `alpha E <= 2` width
cost bound.
-/

open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Topology

namespace ReweightedNPMLE

noncomputable def effectiveQ (n : ℕ) (q : ℝ) : ℝ := q + Real.log (2 * (n : ℝ))

noncomputable def effectiveN (r : ℕ) (q : ℝ) : ℝ := (r : ℝ) * Real.log 5 + q

noncomputable def gammaEffectiveEvent {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (r : ℕ) (α q : ℝ) :
    Set (Fin n → ℝ) :=
  {w | (∀ i, |w i - 1| ≤ 2 * Real.sqrt (effectiveQ n q / α)) ∧
    Real.sqrt α * ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖ ≤
      4 * Real.sqrt (effectiveN r q)}

theorem isClosed_gammaEffectiveEvent {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (r : ℕ) (α q : ℝ) :
    IsClosed (gammaEffectiveEvent V r α q) := by
  have hc : IsClosed {w : Fin n → ℝ | ∀ i, |w i - 1| ≤ 2 * Real.sqrt (effectiveQ n q / α)} := by
    have heq : {w : Fin n → ℝ | ∀ i, |w i - 1| ≤ 2 * Real.sqrt (effectiveQ n q / α)} =
        ⋂ i : Fin n, {w : Fin n → ℝ | |w i - 1| ≤ 2 * Real.sqrt (effectiveQ n q / α)} := by
      ext w
      simp
    rw [heq]
    exact isClosed_iInter fun i ↦ isClosed_le (by fun_prop) continuous_const
  have hp : Continuous (fun w : Fin n → ℝ ↦ Real.sqrt α *
      ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖) := by fun_prop
  exact hc.inter (isClosed_le hp continuous_const)

theorem gammaEffectiveEvent_failure_bound {n r : ℕ} [Nonempty (Fin n)]
    {α q : ℝ} (hα : 0 < α) (hq : 1 ≤ q)
    (hαQ : 4 * effectiveQ n q ≤ α) (hαN : 4 * effectiveN r q ≤ α)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hrank : Module.finrank ℝ V ≤ r) :
    (gammaProductMeasure n α α).real (gammaEffectiveEvent V r α q)ᶜ ≤ 2 * Real.exp (-q) := by
  letI : IsProbabilityMeasure (gammaMeasure α α) := isProbabilityMeasure_gammaMeasure hα hα
  letI : IsProbabilityMeasure (gammaProductMeasure n α α) := by
    dsimp [gammaProductMeasure]
    infer_instance
  have hn : 0 < (n : ℝ) := by exact_mod_cast Fin.pos_iff_nonempty.mpr inferInstance
  have hQ : 0 < effectiveQ n q := by
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n from Fin.pos_iff_nonempty.mpr inferInstance)
    have hl : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
    dsimp [effectiveQ]
    linarith
  have hN : 0 < effectiveN r q := by
    have hl : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
    dsimp [effectiveN]
    positivity
  let t := 2 * Real.sqrt (effectiveQ n q / α)
  have htpos : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    have hh : effectiveQ n q / α ≤ 1 / 4 := (div_le_iff₀ hα).mpr (by linarith)
    have hs := Real.sq_sqrt (div_nonneg hQ.le hα.le)
    dsimp [t]
    nlinarith [Real.sqrt_nonneg (effectiveQ n q / α)]
  let E₁ : Set (Fin n → ℝ) := {w | ∃ i, |w i - 1| > t}
  let E₂ : Set (Fin n → ℝ) := {w | 4 * Real.sqrt (effectiveN r q) <
    Real.sqrt α * ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖}
  have h₁ : (gammaProductMeasure n α α).real E₁ ≤ Real.exp (-q) := by
    have hh := gamma_max_coordinate_concentration (n := n) hα htpos ht1
    have hsq : α * t ^ 2 / 4 = effectiveQ n q := by
      dsimp [t]
      rw [mul_pow, Real.sq_sqrt (div_nonneg hQ.le hα.le)]
      field_simp [hα.ne']
      norm_num
    have hneg : -α * t ^ 2 / 4 = -effectiveQ n q := by linarith [hsq]
    have heq : 2 * (n : ℝ) * Real.exp (-effectiveQ n q) = Real.exp (-q) := by
      dsimp [effectiveQ]
      rw [neg_add, Real.exp_add, Real.exp_neg (Real.log (2 * (n : ℝ))),
        Real.exp_log (by positivity : 0 < 2 * (n : ℝ))]
      field_simp
    simpa only [gammaProductMeasure, E₁, hneg, heq] using hh
  have h₂ : (gammaProductMeasure n α α).real E₂ ≤ Real.exp (-q) :=
    gamma_projected_norm_tail_of_finrank hα hN hαN V hrank
  have hcover : (gammaEffectiveEvent V r α q)ᶜ ⊆ E₁ ∪ E₂ := by
    intro w hw
    by_cases hc : ∀ i, |w i - 1| ≤ t
    · right
      exact lt_of_not_ge (fun hp ↦ hw ⟨hc, hp⟩)
    · left
      simpa only [E₁, mem_setOf_eq, not_forall, not_le] using hc
  calc
    (gammaProductMeasure n α α).real (gammaEffectiveEvent V r α q)ᶜ ≤
        (gammaProductMeasure n α α).real (E₁ ∪ E₂) := measureReal_mono hcover
    _ ≤ (gammaProductMeasure n α α).real E₁ + (gammaProductMeasure n α α).real E₂ :=
      measureReal_union_le E₁ E₂
    _ ≤ 2 * Real.exp (-q) := by linarith

theorem gammaEffectiveEvent_localization_bounds {n r : ℕ}
    {α q η : ℝ} (hα : 0 < α) (hQ : 0 ≤ effectiveQ n q) (hN : 0 ≤ effectiveN r q)
    (hη : 0 ≤ η) (hwidthScale : η * Real.sqrt (α * (n : ℝ) * effectiveQ n q) ≤ 1)
    (hαQ : 1024 * effectiveQ n q ≤ α)
    (hαN : 2359296 * effectiveN r q ≤ α) (hα₀ : 12288 ≤ α)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    {w : Fin n → ℝ} (hw : w ∈ gammaEffectiveEvent V r α q) :
    let A := ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖
    let E := η * ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖
    (∀ i, |w i - 1| ≤ 1 / 16) ∧ w ∈ positiveVectors n ∧
    α * A ^ 2 ≤ 16 * effectiveN r q ∧ α * E ≤ 2 ∧
    A ≤ (1 / 16 : ℝ) / 24 ∧ E ≤ (1 / 16 : ℝ) ^ 2 / 24 := by
  let A := ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖
  let X := ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖
  let E := η * X
  let t := 2 * Real.sqrt (effectiveQ n q / α)
  have hradius : t ≤ 1 / 16 := by
    have hdiv : effectiveQ n q / α ≤ 1 / 1024 :=
      (div_le_iff₀ hα).mpr (by linarith)
    have hs := Real.sq_sqrt (div_nonneg hQ hα.le)
    dsimp [t]
    nlinarith [Real.sqrt_nonneg (effectiveQ n q / α)]
  have hw16 : ∀ i, |w i - 1| ≤ 1 / 16 := fun i ↦ (hw.1 i).trans hradius
  have hwpos : w ∈ positiveVectors n := by
    intro i
    have hi := neg_le_of_abs_le (hw16 i)
    linarith
  have hAsq : α * A ^ 2 ≤ 16 * effectiveN r q := by
    have hp := hw.2
    have hsq := mul_le_mul hp hp (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Real.sqrt_nonneg _))
    convert hsq using 1
    · calc
        α * A ^ 2 = (Real.sqrt α) ^ 2 * A ^ 2 := by rw [Real.sq_sqrt hα.le]
        _ = _ := by dsimp [A]; ring
    · rw [show (4 * Real.sqrt (effectiveN r q)) * (4 * Real.sqrt (effectiveN r q)) =
        16 * (Real.sqrt (effectiveN r q)) ^ 2 by ring, Real.sq_sqrt hN]
  have hX : X ≤ Real.sqrt n * t :=
    euclidean_norm_le_sqrt_card_mul (WithLp.toLp 2 (fun i ↦ w i - 1))
      (by dsimp [t]; positivity) (fun i ↦ hw.1 i)
  have hid : α * (Real.sqrt n * t) = 2 * Real.sqrt (α * (n : ℝ) * effectiveQ n q) := by
    dsimp [t]
    rw [Real.sqrt_div hQ, Real.sqrt_mul (mul_nonneg hα.le (Nat.cast_nonneg n)),
      Real.sqrt_mul hα.le]
    calc
      α * (Real.sqrt n * (2 * (Real.sqrt (effectiveQ n q) / Real.sqrt α))) =
          2 * (α / Real.sqrt α) * Real.sqrt n * Real.sqrt (effectiveQ n q) := by ring
      _ = 2 * (Real.sqrt α * Real.sqrt n) * Real.sqrt (effectiveQ n q) := by
        rw [Real.div_sqrt]
        ring
      _ = _ := by ring
  have hEscaled : α * E ≤ 2 := by
    calc
      α * E ≤ η * (α * (Real.sqrt n * t)) := by
        dsimp [E]
        nlinarith [mul_le_mul_of_nonneg_left hX (mul_nonneg hα.le hη)]
      _ = 2 * (η * Real.sqrt (α * (n : ℝ) * effectiveQ n q)) := by rw [hid]; ring
      _ ≤ 2 := by linarith
  have hAlocal : A ≤ (1 / 16 : ℝ) / 24 := by
    have hh : α * A ^ 2 ≤ α * ((1 / 16 : ℝ) / 24) ^ 2 := by
      nlinarith [hαN]
    have hs := (mul_le_mul_iff_right₀ hα).mp hh
    nlinarith [norm_nonneg (V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1)))]
  have hElocal : E ≤ (1 / 16 : ℝ) ^ 2 / 24 := by
    have hh : α * E ≤ α * ((1 / 16 : ℝ) ^ 2 / 24) := by linarith
    exact (mul_le_mul_iff_right₀ hα).mp hh
  exact ⟨hw16, hwpos, hAsq, hEscaled, hAlocal, hElocal⟩

end ReweightedNPMLE
