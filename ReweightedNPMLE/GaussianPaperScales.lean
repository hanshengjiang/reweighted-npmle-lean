import ReweightedNPMLE.GaussianStructural
import ReweightedNPMLE.GaussianNearMLERate
import Mathlib.Tactic

/-!
# Eventual scales for Gaussian exact regularization

The paper's logarithmic effective dimension, balanced Gamma shape, Taylor
rank, and remainder conditions are consequences, rather than assumptions.
Only eventual statements are used: the definitions at small sample sizes
are irrelevant.
-/

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace ReweightedNPMLE

noncomputable def gaussianPaperEffectiveDimension (d n : ℕ) : ℝ :=
  gaussianPaperLogScale n ^ d

noncomputable def gaussianPaperAugmentedDimension (d n : ℕ) : ℝ :=
  gaussianPaperEffectiveDimension d n + Real.log n

noncomputable def gaussianPaperBalancedShape (d n : ℕ) : ℝ :=
  gaussianPaperAugmentedDimension d n * Real.log n

noncomputable def gaussianPaperStructuralTail (b : ℝ) (n : ℕ) : ℝ :=
  (b + 2) * Real.log n

noncomputable def gaussianPaperStructuralRank (d : ℕ) (C : ℝ) (n : ℕ) : ℕ :=
  1 + (gaussianPaperMomentOrder C n + d).choose d

theorem eventually_gaussianPaperAugmentedDimension_pos (d : ℕ) :
    ∀ᶠ n : ℕ in atTop, 0 < gaussianPaperAugmentedDimension d n := by
  filter_upwards [eventually_gaussianPaperLogScale_nonneg_le_log,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with n hs hl
  exact add_pos_of_nonneg_of_pos (pow_nonneg hs.1 d) hl

theorem eventually_gaussianPaperStructuralRank_le (d : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop,
      (gaussianPaperStructuralRank d C n : ℝ) ≤
        (1 + (4 * C + 1) ^ d) * gaussianPaperAugmentedDimension d n := by
  filter_upwards [eventually_gaussianMomentDimension_le_logScale_pow d hC,
    eventually_gaussianPaperLogScale_nonneg_le_log,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with n hk hs hl
  have hchoose : (gaussianPaperMomentOrder C n + d).choose d ≤
      gaussianMomentDimension d (gaussianPaperMomentOrder C n) := by
    rw [gaussianMomentDimension_eq_choose]
    exact Nat.choose_le_choose d (by omega)
  have hc : ((gaussianPaperMomentOrder C n + d).choose d : ℝ) ≤
      (4 * C + 1) ^ d * gaussianPaperLogScale n ^ d := by
    have hcast : ((gaussianPaperMomentOrder C n + d).choose d : ℝ) ≤
        (gaussianMomentDimension d (gaussianPaperMomentOrder C n) : ℝ) := by
      exact_mod_cast hchoose
    exact hcast.trans (by simpa only [mul_pow] using hk)
  have hp : 0 ≤ gaussianPaperLogScale n ^ d := pow_nonneg hs.1 d
  have hcoef : 0 ≤ (4 * C + 1) ^ d := by positivity
  change 1 ≤ Real.log (n : ℝ) at hl
  have hcoeflog := mul_nonneg hcoef (show 0 ≤ Real.log (n : ℝ) by linarith)
  dsimp [gaussianPaperStructuralRank, gaussianPaperAugmentedDimension,
    gaussianPaperEffectiveDimension]
  push_cast
  nlinarith

theorem eventually_effectiveQ_gaussianPaperStructuralTail_le {b : ℝ} (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop,
      effectiveQ n (gaussianPaperStructuralTail b n) ≤ (b + 4) * Real.log n := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (Real.log 2)] with n hn hl
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  change Real.log 2 ≤ Real.log (n : ℝ) at hl
  dsimp [effectiveQ, gaussianPaperStructuralTail]
  rw [Real.log_mul (by norm_num) hn0]
  nlinarith

theorem eventually_gaussianPaperStructural_complexity_le (d : ℕ)
    {C b : ℝ} (hC : 0 < C) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop,
      (gaussianPaperStructuralRank d C n : ℝ) +
        effectiveQ n (gaussianPaperStructuralTail b n) ≤
          (1 + (4 * C + 1) ^ d + (b + 4)) * gaussianPaperAugmentedDimension d n := by
  filter_upwards [eventually_gaussianPaperStructuralRank_le d hC,
    eventually_effectiveQ_gaussianPaperStructuralTail_le hb,
    eventually_gaussianPaperLogScale_nonneg_le_log] with n hr hQ hs
  have hp : 0 ≤ gaussianPaperEffectiveDimension d n := pow_nonneg hs.1 d
  have hlog : Real.log n ≤ gaussianPaperAugmentedDimension d n := by
    dsimp [gaussianPaperAugmentedDimension]
    linarith
  have hQ' := hQ.trans (mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ b + 4))
  nlinarith

theorem eventually_gaussianPaperBalancedShape_scale (d : ℕ)
    {C b : ℝ} (hC : 0 < C) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop,
      10000000 * ((gaussianPaperStructuralRank d C n : ℝ) +
        effectiveQ n (gaussianPaperStructuralTail b n)) ≤ gaussianPaperBalancedShape d n := by
  let A : ℝ := 1 + (4 * C + 1) ^ d + (b + 4)
  filter_upwards [eventually_gaussianPaperStructural_complexity_le d hC hb,
    eventually_gaussianPaperAugmentedDimension_pos d,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
      (10000000 * A)] with n hc hp hl
  calc
    10000000 * ((gaussianPaperStructuralRank d C n : ℝ) +
        effectiveQ n (gaussianPaperStructuralTail b n)) ≤
          10000000 * (A * gaussianPaperAugmentedDimension d n) := by
      exact mul_le_mul_of_nonneg_left hc (by norm_num)
    _ ≤ gaussianPaperBalancedShape d n := by
      change 10000000 * A ≤ Real.log (n : ℝ) at hl
      dsimp [gaussianPaperBalancedShape]
      nlinarith

/-- Polylogarithmic quantities are smaller than every positive power of `n`. -/
theorem isLittleO_gaussianPaperAugmentedDimension_rpow (d : ℕ) {s : ℝ} (hs : 0 < s) :
    gaussianPaperAugmentedDimension d =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ s) := by
  have hpow : (fun n : ℕ ↦ Real.log (n : ℝ) ^ d) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ s) := by
    simpa only [Function.comp_apply, Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (d : ℝ) hs).comp_tendsto
        tendsto_natCast_atTop_atTop
  have hlog : (fun n : ℕ ↦ Real.log (n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ s) := by
    simpa only [Function.comp_apply] using
      (isLittleO_log_rpow_atTop hs).comp_tendsto tendsto_natCast_atTop_atTop
  have heff : gaussianPaperEffectiveDimension d =O[atTop]
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ d) := by
    apply Asymptotics.IsBigO.of_norm_eventuallyLE
    filter_upwards [eventually_gaussianPaperLogScale_nonneg_le_log] with n hn
    have hl : 0 ≤ Real.log (n : ℝ) := hn.1.trans hn.2
    simp only [gaussianPaperEffectiveDimension, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hn.1 d), abs_of_nonneg (pow_nonneg hl d)]
    exact pow_le_pow_left₀ hn.1 hn.2 d
  exact (heff.trans_isLittleO hpow).add hlog

theorem isLittleO_gaussianPaperBalancedShape_rpow (d : ℕ) {s : ℝ} (hs : 0 < s) :
    gaussianPaperBalancedShape d =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ s) := by
  have hdim := isLittleO_gaussianPaperAugmentedDimension_rpow d (half_pos hs)
  have hlog : (fun n : ℕ ↦ Real.log (n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (s / 2)) := by
    simpa only [Function.comp_apply] using
      (isLittleO_log_rpow_atTop (half_pos hs)).comp_tendsto
        tendsto_natCast_atTop_atTop
  have hprod := hdim.mul hlog
  apply hprod.congr' (Eventually.of_forall (fun _ ↦ rfl))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [← Real.rpow_add hn0, add_halves]

/-- The structural remainder is bounded by the previously proved local
moment-matching remainder, after cancelling its harmless factor two. -/
theorem gaussianTaylorResidual_le_momentRelativeError {T S : ℝ}
    (hT : 0 ≤ T) (hS : 0 ≤ S) (n L : ℕ) :
    gaussianTaylorResidual n T S L ≤
      Real.sqrt n * (gaussianMomentRelativeError T S L / 2) := by
  have hA : T * S ≤ T * S + S ^ 2 / 2 := by nlinarith [sq_nonneg S]
  have hexp : Real.exp (2 * T * S + S ^ 2 / 2) ≤
      Real.exp (2 * (T * S + S ^ 2 / 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg S]
  have hpow := pow_le_pow_left₀ (mul_nonneg hT hS) hA (L + 1)
  dsimp [gaussianTaylorResidual, gaussianMomentRelativeError]
  have hfac : (0 : ℝ) < (L + 1).factorial := by positivity
  have hmul := mul_le_mul hexp hpow (by positivity) (by positivity)
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  convert (div_le_div_iff_of_pos_right hfac).mpr hmul using 1 <;> ring

theorem eventually_gaussianTaylorResidual_paper_le (d : ℕ) {C S b : ℝ}
    (hC : 0 < C) (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop,
      gaussianTaylorResidual n (gaussianPaperSampleRadius d S b n) S
          (gaussianPaperMomentOrder C n) ≤
        Real.sqrt n * (n : ℝ) ^ (1 - C / 8 : ℝ) := by
  filter_upwards [eventually_gaussianMomentRelativeError_paper_le d hC hS hb,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 0]
    with n he hl
  have hT : 0 ≤ gaussianPaperSampleRadius d S b n := by
    dsimp [gaussianPaperSampleRadius, gaussianPaperRadiusExponent]
    positivity
  exact (gaussianTaylorResidual_le_momentRelativeError hT hS n _).trans
    (mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg _))

theorem eventually_gaussianPaperBalancedShape_le_rpow (d : ℕ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop, gaussianPaperBalancedShape d n ≤ (n : ℝ) ^ s := by
  filter_upwards [(isLittleO_gaussianPaperBalancedShape_rpow d hs).bound zero_lt_one,
    eventually_gaussianPaperAugmentedDimension_pos d,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 0]
    with n hb hd hl
  have hp : 0 ≤ gaussianPaperBalancedShape d n := by
    exact mul_nonneg hd.le hl
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s), one_mul] using hb

theorem eventually_gaussianPaperStructuralTail_ge_one {b : ℝ} (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ gaussianPaperStructuralTail b n := by
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
    with n hl
  change 1 ≤ Real.log (n : ℝ) at hl
  dsimp [gaussianPaperStructuralTail]
  nlinarith

theorem eventually_effectiveQ_gaussianPaperStructuralTail_le_nat {b : ℝ} (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop, effectiveQ n (gaussianPaperStructuralTail b n) ≤ n := by
  have hsmall : (fun n : ℕ ↦ (b + 4) * Real.log (n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
    exact (Real.isLittleO_log_id_atTop.comp_tendsto
      tendsto_natCast_atTop_atTop).const_mul_left (b + 4)
  filter_upwards [eventually_effectiveQ_gaussianPaperStructuralTail_le hb,
    hsmall.bound zero_lt_one,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 0]
    with n hQ hn hl
  have hp : 0 ≤ (b + 4) * Real.log (n : ℝ) := mul_nonneg (by linarith) hl
  simp only [Real.norm_eq_abs, abs_of_nonneg hp,
    abs_of_nonneg (show (0 : ℝ) ≤ n by positivity), one_mul] at hn
  exact hQ.trans hn

/-- A polynomial upper bound on the Gamma shape suffices for the width
condition, after increasing only the constant in the logarithmic Taylor order.
This includes both the balanced and every arbitrarily tiny regime. -/
theorem eventually_gaussianTaylorResidual_width_scale (d : ℕ) {a C S b : ℝ}
    (ha : 0 ≤ a) (hC : 8 * (a + 4) ≤ C) (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop, ∀ α : ℝ, 0 ≤ α → α ≤ (n : ℝ) ^ a →
      gaussianTaylorResidual n (gaussianPaperSampleRadius d S b n) S
          (gaussianPaperMomentOrder C n) *
        Real.sqrt (α * (n : ℝ) * effectiveQ n (gaussianPaperStructuralTail b n)) ≤ 1 := by
  have hCpos : 0 < C := by linarith
  filter_upwards [eventually_gaussianTaylorResidual_paper_le d hCpos hS hb,
    eventually_effectiveQ_gaussianPaperStructuralTail_le_nat hb,
    eventually_gaussianPaperStructuralTail_ge_one hb,
    eventually_ge_atTop (1 : ℕ)] with n he hQ hq hn
  intro α hα hαbound
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog2n : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
  have hQ0 : 0 ≤ effectiveQ n (gaussianPaperStructuralTail b n) := by
    dsimp [effectiveQ]
    linarith
  have hinside : α * (n : ℝ) * effectiveQ n (gaussianPaperStructuralTail b n) ≤
      (n : ℝ) ^ (a + 2) := by
    calc
      _ ≤ (n : ℝ) ^ a * (n : ℝ) * (n : ℝ) := by gcongr
      _ = (n : ℝ) ^ (a + 2) := by
        rw [show (n : ℝ) ^ a * (n : ℝ) * (n : ℝ) =
          (n : ℝ) ^ a * (n : ℝ) ^ (2 : ℝ) by norm_num [pow_two]; ring,
          ← Real.rpow_add hn0]
  have hsqrt : Real.sqrt (α * (n : ℝ) * effectiveQ n (gaussianPaperStructuralTail b n)) ≤
      (n : ℝ) ^ ((a + 2) / 2) := by
    calc
      _ ≤ Real.sqrt ((n : ℝ) ^ (a + 2)) := Real.sqrt_le_sqrt hinside
      _ = (n : ℝ) ^ ((a + 2) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]
        congr 1
        ring
  calc
    _ ≤ (Real.sqrt n * (n : ℝ) ^ (1 - C / 8 : ℝ)) *
        (n : ℝ) ^ ((a + 2) / 2) :=
      mul_le_mul he hsqrt (Real.sqrt_nonneg _) (by positivity)
    _ = (n : ℝ) ^ ((1 / 2 : ℝ) + (1 - C / 8) + (a + 2) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)

/-- Both scale hypotheses of the Gaussian structural theorem hold at the
paper's balanced shape; no rank or remainder estimate is left as an input. -/
theorem eventually_gaussianPaperBalanced_conditions (d : ℕ) {S b : ℝ}
    (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ gaussianPaperStructuralTail b n ∧
      0 < gaussianPaperBalancedShape d n ∧
      10000000 * ((gaussianPaperStructuralRank d 40 n : ℝ) +
        effectiveQ n (gaussianPaperStructuralTail b n)) ≤ gaussianPaperBalancedShape d n ∧
      gaussianTaylorResidual n (gaussianPaperSampleRadius d S b n) S
          (gaussianPaperMomentOrder 40 n) *
        Real.sqrt (gaussianPaperBalancedShape d n * (n : ℝ) *
          effectiveQ n (gaussianPaperStructuralTail b n)) ≤ 1 := by
  filter_upwards [eventually_gaussianPaperStructuralTail_ge_one hb,
    eventually_gaussianPaperAugmentedDimension_pos d,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0,
    eventually_gaussianPaperBalancedShape_scale d (by norm_num : (0 : ℝ) < 40) hb,
    eventually_gaussianPaperBalancedShape_le_rpow d (show (0 : ℝ) < 1 by norm_num),
    eventually_gaussianTaylorResidual_width_scale d (show (0 : ℝ) ≤ 1 by norm_num)
      (show (8 : ℝ) * (1 + 4) ≤ 40 by norm_num) hS hb]
    with n hq hd hl hscale hαle hwidth
  have hα : 0 < gaussianPaperBalancedShape d n := mul_pos hd hl
  exact ⟨hq, hα, hscale, hwidth _ hα.le (by simpa only [Real.rpow_one] using hαle)⟩

/-- For `alpha = n^(2L+2)`, the paper's scale conditions hold as well.
The Taylor order stays logarithmic; only its fixed constant depends on `L`. -/
theorem eventually_gaussianPaperTiny_conditions (d : ℕ) {S b L : ℝ}
    (hS : 0 ≤ S) (hb : 0 ≤ b) (hL : 0 < L) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ gaussianPaperStructuralTail b n ∧
      10000000 * ((gaussianPaperStructuralRank d (8 * (2 * L + 6)) n : ℝ) +
        effectiveQ n (gaussianPaperStructuralTail b n)) ≤ (n : ℝ) ^ (2 * L + 2) ∧
      gaussianTaylorResidual n (gaussianPaperSampleRadius d S b n) S
          (gaussianPaperMomentOrder (8 * (2 * L + 6)) n) *
        Real.sqrt ((n : ℝ) ^ (2 * L + 2) * (n : ℝ) *
          effectiveQ n (gaussianPaperStructuralTail b n)) ≤ 1 := by
  let C := 8 * (2 * L + 6)
  let A := 1 + (4 * C + 1) ^ d + (b + 4)
  have hC : 0 < C := by dsimp [C]; linarith
  have hA : 0 ≤ 10000000 * A := by dsimp [A]; positivity
  have hsmall := (isLittleO_gaussianPaperAugmentedDimension_rpow d
    (show 0 < 2 * L + 2 by linarith)).const_mul_left (10000000 * A)
  filter_upwards [eventually_gaussianPaperStructuralTail_ge_one hb,
    eventually_gaussianPaperStructural_complexity_le d hC hb,
    hsmall.bound zero_lt_one, eventually_gaussianPaperAugmentedDimension_pos d,
    eventually_gaussianTaylorResidual_width_scale d (show 0 ≤ 2 * L + 2 by linarith)
      (show 8 * ((2 * L + 2) + 4) ≤ C by dsimp [C]; ring_nf; exact le_rfl) hS hb]
    with n hq hc hbound hd hwidth
  have hbound' : 10000000 * A * gaussianPaperAugmentedDimension d n ≤
      (n : ℝ) ^ (2 * L + 2) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA hd.le),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), one_mul] using hbound
  refine ⟨hq, ?_, hwidth _ (Real.rpow_nonneg (Nat.cast_nonneg n) _) le_rfl⟩
  calc
    _ ≤ 10000000 * (A * gaussianPaperAugmentedDimension d n) :=
      mul_le_mul_of_nonneg_left hc (by norm_num)
    _ ≤ (n : ℝ) ^ (2 * L + 2) := by nlinarith

theorem eventually_gaussianPaper_sparse_uniqueness_threshold (d : ℕ) {A : ℝ}
    (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop,
      (2 * Nat.ceil (A * gaussianPaperAugmentedDimension d n)) * (d + 1) ≤ n := by
  have hsmall := (isLittleO_gaussianPaperAugmentedDimension_rpow d
    (show (0 : ℝ) < 1 by norm_num)).const_mul_left (2 * (d + 1 : ℝ) * A)
  filter_upwards [hsmall.bound (show (0 : ℝ) < 1 / 2 by norm_num),
    eventually_gaussianPaperAugmentedDimension_pos d,
    eventually_ge_atTop (4 * (d + 1))] with n hb hd hn
  have hnreal : (4 : ℝ) * (d + 1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 ≤ 2 * (d + 1 : ℝ) * A * gaussianPaperAugmentedDimension d n := by positivity
  have hbound : 2 * (d + 1 : ℝ) * A * gaussianPaperAugmentedDimension d n ≤
      (1 / 2 : ℝ) * n := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hp, Real.rpow_one,
      abs_of_nonneg (show (0 : ℝ) ≤ n by positivity)] using hb
  have hc := (Nat.ceil_lt_add_one (mul_nonneg hA hd.le)).le
  have hm : (2 : ℝ) * (Nat.ceil (A * gaussianPaperAugmentedDimension d n) : ℝ) *
      (d + 1 : ℝ) ≤ n := by
    nlinarith [mul_le_mul_of_nonneg_right hc (show 0 ≤ 2 * (d + 1 : ℝ) by positivity)]
  exact_mod_cast hm

theorem eventually_gaussianPaper_rank_tail_le (d : ℕ) {C b : ℝ}
    (hC : 0 < C) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop,
      (gaussianPaperStructuralRank d C n : ℝ) + gaussianPaperStructuralTail b n ≤
        (1 + (4 * C + 1) ^ d + (b + 4)) * gaussianPaperAugmentedDimension d n := by
  filter_upwards [eventually_gaussianPaperStructural_complexity_le d hC hb,
    eventually_ge_atTop (1 : ℕ)] with n hc hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by linarith)
  dsimp [effectiveQ] at hc
  linarith

theorem eventually_gaussianPaperBalanced_likelihood_bound (d : ℕ) {C b : ℝ}
    (hC : 0 < C) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop,
      10000000 * ((gaussianPaperStructuralRank d C n : ℝ) +
        gaussianPaperStructuralTail b n) / gaussianPaperBalancedShape d n ≤
      (10000000 * (1 + (4 * C + 1) ^ d + (b + 4))) / Real.log n := by
  filter_upwards [eventually_gaussianPaper_rank_tail_le d hC hb,
    eventually_gaussianPaperAugmentedDimension_pos d,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with n hc hd hl
  have hα : 0 < gaussianPaperBalancedShape d n := mul_pos hd hl
  calc
    _ ≤ 10000000 * ((1 + (4 * C + 1) ^ d + (b + 4)) *
        gaussianPaperAugmentedDimension d n) / gaussianPaperBalancedShape d n := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num)) hα.le
    _ = _ := by
      dsimp [gaussianPaperBalancedShape]
      field_simp

theorem eventually_gaussianPaperBalanced_weight_bound (d : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop,
      2 * Real.sqrt (effectiveQ n (gaussianPaperStructuralTail b n) /
        gaussianPaperBalancedShape d n) ≤
      (2 * Real.sqrt (b + 4)) / Real.sqrt (gaussianPaperAugmentedDimension d n) := by
  filter_upwards [eventually_effectiveQ_gaussianPaperStructuralTail_le hb,
    eventually_gaussianPaperAugmentedDimension_pos d,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with n hQ hd hl
  have hα : 0 < gaussianPaperBalancedShape d n := mul_pos hd hl
  have hratio : effectiveQ n (gaussianPaperStructuralTail b n) /
      gaussianPaperBalancedShape d n ≤ (b + 4) / gaussianPaperAugmentedDimension d n := by
    apply (div_le_iff₀ hα).mpr
    convert hQ using 1
    dsimp [gaussianPaperBalancedShape]
    field_simp
  calc
    _ ≤ 2 * Real.sqrt ((b + 4) / gaussianPaperAugmentedDimension d n) := by
      gcongr
    _ = _ := by rw [Real.sqrt_div (by linarith : 0 ≤ b + 4)]; ring

theorem gaussianPaperStructural_failure_bound {n : ℕ} (hn : 0 < n) (b : ℝ) :
    3 * Real.exp (-gaussianPaperStructuralTail b n) = 3 * (n : ℝ) ^ (-(b + 2)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hn0]
  congr 2
  dsimp [gaussianPaperStructuralTail]
  ring

theorem eventually_gaussianPaperAugmentedDimension_le_twice_effective {d : ℕ}
    (hd : 2 ≤ d) :
    ∀ᶠ n : ℕ in atTop,
      gaussianPaperAugmentedDimension d n ≤ 2 * gaussianPaperEffectiveDimension d n := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventually_const_mul_log_log_le_log_rpow (show (0 : ℝ) ≤ 1 by norm_num),
    hlog.eventually_ge_atTop 1, hloglog.eventually_gt_atTop 0,
    tendsto_gaussianPaperLogScale_atTop.eventually_ge_atTop 1]
    with n hsmall hl hll hs
  change 1 ≤ Real.log (n : ℝ) at hl
  change 0 < Real.log (Real.log (n : ℝ)) at hll
  have hroot : Real.log (Real.log (n : ℝ)) ≤ Real.sqrt (Real.log (n : ℝ)) := by
    calc
      _ ≤ Real.log (n : ℝ) ^ (3 / 8 : ℝ) := by simpa only [one_mul] using hsmall
      _ ≤ Real.log (n : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hl (by norm_num)
      _ = _ := (Real.sqrt_eq_rpow _).symm
  have hx0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hroot0 := Real.sqrt_nonneg (Real.log (n : ℝ))
  have hrootsq := Real.sq_sqrt hx0
  have hscale : Real.sqrt (Real.log (n : ℝ)) ≤ gaussianPaperLogScale n := by
    dsimp [gaussianPaperLogScale]
    apply (le_div_iff₀ hll).mpr
    nlinarith [mul_le_mul_of_nonneg_left hroot hroot0]
  have hlogscale : Real.log (n : ℝ) ≤ gaussianPaperLogScale n ^ 2 := by
    nlinarith [sq_nonneg (gaussianPaperLogScale n - Real.sqrt (Real.log (n : ℝ)))]
  have hpow : gaussianPaperLogScale n ^ 2 ≤ gaussianPaperLogScale n ^ d :=
    pow_le_pow_right₀ hs hd
  dsimp [gaussianPaperAugmentedDimension, gaussianPaperEffectiveDimension]
  linarith [hlogscale.trans hpow]

theorem eventually_gaussianPaperAugmentedDimension_one_le_twice_log :
    ∀ᶠ n : ℕ in atTop, gaussianPaperAugmentedDimension 1 n ≤ 2 * Real.log n := by
  filter_upwards [eventually_gaussianPaperLogScale_nonneg_le_log] with n hs
  dsimp [gaussianPaperAugmentedDimension, gaussianPaperEffectiveDimension]
  rw [pow_one]
  linarith [hs.2]

/-- The same common sparsification event already gives the literal
`n^(-L)` coordinate perturbation in the tiny regime. -/
theorem eventually_gaussianPaperTiny_weight_bound {b L : ℝ} (hb : 0 ≤ b) (hL : 0 < L) :
    ∀ᶠ n : ℕ in atTop,
      2 * Real.sqrt (effectiveQ n (gaussianPaperStructuralTail b n) /
        (n : ℝ) ^ (2 * L + 2)) ≤ (n : ℝ) ^ (-L) := by
  filter_upwards [eventually_effectiveQ_gaussianPaperStructuralTail_le_nat hb,
    eventually_ge_atTop (4 : ℕ)] with n hQ hn
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hroot0 := Real.sqrt_nonneg (n : ℝ)
  have hrootsq := Real.sq_sqrt hn0.le
  have hroot2 : 2 ≤ Real.sqrt (n : ℝ) := by nlinarith
  have hrootbound : 2 * Real.sqrt (n : ℝ) ≤ n := by nlinarith
  calc
    _ ≤ 2 * Real.sqrt ((n : ℝ) / (n : ℝ) ^ (2 * L + 2)) := by
      gcongr
    _ = 2 * (Real.sqrt (n : ℝ) / (n : ℝ) ^ (L + 1)) := by
      have hden : Real.sqrt ((n : ℝ) ^ (2 * L + 2)) = (n : ℝ) ^ (L + 1) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]
        congr 1
        ring
      rw [Real.sqrt_div hn0.le, hden]
    _ ≤ (n : ℝ) / (n : ℝ) ^ (L + 1) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hrootbound (Real.rpow_nonneg hn0.le _)
    _ = (n : ℝ) ^ (-L) := by
      calc
        _ = (n : ℝ) ^ (1 - (L + 1)) := by
          simpa only [Real.rpow_one] using (Real.rpow_sub hn0 1 (L + 1)).symm
        _ = _ := by congr 1; ring

end ReweightedNPMLE
