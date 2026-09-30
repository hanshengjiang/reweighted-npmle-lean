import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import ReweightedNPMLE.GaussianNearMLE

/-!
# Explicit entropy arithmetic for the Gaussian near-MLE theorem

This module turns the finite Gaussian-mixture net cardinality appearing in
`GaussianNearMLE` into the binomial and logarithmic bounds used in the
paper's rate calculation.  It is kept separate from the probabilistic
argument so that the remaining asymptotic tuning can use a small, explicit
arithmetic interface.
-/

open scoped ENNReal
open Filter Topology MeasureTheory Set

namespace ReweightedNPMLE

/-- The logarithmic scale used for the paper's Taylor order.  Values at the
finitely many small sample sizes are immaterial to the eventual statements. -/
noncomputable def gaussianPaperLogScale (n : ℕ) : ℝ :=
  Real.log n / Real.log (Real.log n)

/-- Paper Taylor order with an explicit multiplicative constant. -/
noncomputable def gaussianPaperMomentOrder (C : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (C * gaussianPaperLogScale n)

/-- Location mesh used in the paper's finite likelihood net. -/
noncomputable def gaussianPaperEpsilon (n : ℕ) : ℝ :=
  ((n : ℝ) ^ 16)⁻¹

/-- Weight-grid denominator `ceil(k n^16)` from the paper, where `k` is the
moment dimension at the chosen Taylor order. -/
noncomputable def gaussianPaperWeightDenominator
    (d : ℕ) (C : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil ((gaussianMomentDimension d (gaussianPaperMomentOrder C n) : ℝ) *
    (n : ℝ) ^ 16)

/-- The elementary real-variable limit `x / log x → ∞`. -/
theorem tendsto_id_div_log_atTop :
    Filter.Tendsto (fun x : ℝ ↦ x / Real.log x) Filter.atTop Filter.atTop := by
  have hzero : Filter.Tendsto (fun x : ℝ ↦ Real.log x / x)
      Filter.atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < Real.log x / x := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (lt_trans zero_lt_one hx)
  have hwithin : Filter.Tendsto (fun x : ℝ ↦ Real.log x / x)
      Filter.atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hzero, hpos⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  change (Real.log x / x)⁻¹ = x / Real.log x
  rw [inv_div]

/-- The logarithmic Taylor scale diverges. -/
theorem tendsto_gaussianPaperLogScale_atTop :
    Filter.Tendsto gaussianPaperLogScale Filter.atTop Filter.atTop := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  simpa only [gaussianPaperLogScale] using tendsto_id_div_log_atTop.comp hlog

/-- Consequently the ceiling Taylor order diverges for every positive
constant `C`. -/
theorem tendsto_gaussianPaperMomentOrder_atTop {C : ℝ} (hC : 0 < C) :
    Filter.Tendsto (gaussianPaperMomentOrder C) Filter.atTop Filter.atTop := by
  unfold gaussianPaperMomentOrder
  exact tendsto_nat_ceil_atTop.comp
    (tendsto_gaussianPaperLogScale_atTop.const_mul_atTop hC)

/-- Taking the natural ceiling does not alter the asymptotic Taylor scale. -/
theorem tendsto_gaussianPaperMomentOrder_div {C : ℝ} (hC : 0 < C) :
    Filter.Tendsto
      (fun n ↦ (gaussianPaperMomentOrder C n : ℝ) /
        (C * gaussianPaperLogScale n))
      Filter.atTop (𝓝 1) := by
  have hbase : Filter.Tendsto (fun n ↦ C * gaussianPaperLogScale n)
      Filter.atTop Filter.atTop :=
    tendsto_gaussianPaperLogScale_atTop.const_mul_atTop hC
  simpa only [gaussianPaperMomentOrder] using
    (tendsto_nat_ceil_div_atTop (R := ℝ)).comp hbase

/-- Eventually the ceiling order is at most twice its unrounded value. -/
theorem eventually_gaussianPaperMomentOrder_le {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n in Filter.atTop,
      (gaussianPaperMomentOrder C n : ℝ) ≤
        2 * C * gaussianPaperLogScale n := by
  have hratio := tendsto_gaussianPaperMomentOrder_div hC
  have hlt : ∀ᶠ n in Filter.atTop,
      (gaussianPaperMomentOrder C n : ℝ) /
          (C * gaussianPaperLogScale n) < 2 :=
    hratio.eventually_lt_const (by norm_num)
  have hpos : ∀ᶠ n in Filter.atTop,
      0 < C * gaussianPaperLogScale n :=
    (tendsto_gaussianPaperLogScale_atTop.const_mul_atTop hC).eventually_gt_atTop 0
  filter_upwards [hlt, hpos] with n hn hden
  have := (div_lt_iff₀ hden).mp hn
  nlinarith

/-- Eventually `log n / log log n` lies between zero and `log n`. -/
theorem eventually_gaussianPaperLogScale_nonneg_le_log :
    ∀ᶠ n in Filter.atTop,
      0 ≤ gaussianPaperLogScale n ∧
        gaussianPaperLogScale n ≤ Real.log (n : ℝ) := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hlog
  filter_upwards [hlog.eventually_gt_atTop 0,
    hloglog.eventually_ge_atTop 1] with n hn hden
  have hdenpos : 0 < Real.log (Real.log (n : ℝ)) :=
    lt_of_lt_of_le zero_lt_one hden
  constructor
  · exact div_nonneg hn.le hdenpos.le
  · unfold gaussianPaperLogScale
    rw [div_le_iff₀ hdenpos]
    nlinarith

/-- Any fixed multiple of `log log n` is eventually dominated by the
three-eighths power of `log n`. -/
theorem eventually_const_mul_log_log_le_log_rpow
    {D : ℝ} (hD : 0 ≤ D) :
    ∀ᶠ n : ℕ in Filter.atTop,
      D * Real.log (Real.log (n : ℝ)) ≤
        Real.log (n : ℝ) ^ (3 / 8 : ℝ) := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall0 : (fun n : ℕ ↦ Real.log (Real.log (n : ℝ))) =o[Filter.atTop]
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ (3 / 8 : ℝ)) := by
    simpa only [Function.comp_apply] using
      (isLittleO_log_rpow_atTop (show (0 : ℝ) < 3 / 8 by norm_num)).comp_tendsto hlog
  have hsmall := hsmall0.const_mul_left D
  have hbound := hsmall.bound zero_lt_one
  have hloglog : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hlog
  filter_upwards [hbound, hlog.eventually_gt_atTop 0,
    hloglog.eventually_ge_atTop 0] with n hn hlogn hloglogn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hD hloglogn),
    abs_of_nonneg (Real.rpow_nonneg hlogn.le _), one_mul] using hn

/-- Radius exponent used to make the Gaussian sample-radius failure
polynomially small. -/
noncomputable def gaussianPaperRadiusExponent (b : ℝ) (n : ℕ) : ℝ :=
  (b + 4) * Real.log (n : ℝ)

/-- Deterministic sample radius paired with `gaussianPaperRadiusExponent`. -/
noncomputable def gaussianPaperSampleRadius
    (d : ℕ) (S b : ℝ) (n : ℕ) : ℝ :=
  S + Real.sqrt (d : ℝ) * Real.sqrt (2 * gaussianPaperRadiusExponent b n)

/-- Argument of the local exponential Taylor remainder. -/
noncomputable def gaussianPaperTaylorArgument
    (d : ℕ) (S b : ℝ) (n : ℕ) : ℝ :=
  gaussianPaperSampleRadius d S b n * S + S ^ 2 / 2

/-- A fixed coefficient controlling the growing Taylor argument. -/
noncomputable def gaussianPaperTaylorConstant (d : ℕ) (S b : ℝ) : ℝ :=
  3 * S ^ 2 / 2 +
    Real.sqrt (d : ℝ) * Real.sqrt (2 * (b + 4)) * S

theorem gaussianPaperTaylorConstant_nonneg (d : ℕ) {S b : ℝ}
    (hS : 0 ≤ S) (hb : 0 ≤ b) :
    0 ≤ gaussianPaperTaylorConstant d S b := by
  unfold gaussianPaperTaylorConstant
  positivity

/-- At the paper radius, the local Taylor argument grows at most as a fixed
multiple of `sqrt (log n)`. -/
theorem eventually_gaussianPaperTaylorArgument_le
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      gaussianPaperTaylorArgument d S b n ≤
        gaussianPaperTaylorConstant d S b *
          Real.sqrt (Real.log (n : ℝ)) := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop 1] with n hn
  have hb4 : 0 ≤ 2 * (b + 4) := by positivity
  have hsqrtlog : 1 ≤ Real.sqrt (Real.log (n : ℝ)) := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_le_sqrt hn
  have hsqrtd : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hsqrtb : 0 ≤ Real.sqrt (2 * (b + 4)) := Real.sqrt_nonneg _
  have hsqrtlog0 : 0 ≤ Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_nonneg _
  unfold gaussianPaperTaylorArgument gaussianPaperSampleRadius
    gaussianPaperRadiusExponent gaussianPaperTaylorConstant
  rw [show 2 * ((b + 4) * Real.log (n : ℝ)) =
      (2 * (b + 4)) * Real.log (n : ℝ) by ring,
    Real.sqrt_mul hb4]
  nlinarith [sq_nonneg S]

/-- The paper Taylor argument is eventually nonnegative. -/
theorem eventually_gaussianPaperTaylorArgument_nonneg
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      0 ≤ gaussianPaperTaylorArgument d S b n := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop 0] with n hn
  unfold gaussianPaperTaylorArgument gaussianPaperSampleRadius
    gaussianPaperRadiusExponent
  positivity

/-- The paper sample radius is negligible compared with even `n²`; this
coarse form is sufficient for the mesh contribution to the log error. -/
theorem eventually_gaussianPaperSampleRadius_add_le_sq
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      gaussianPaperSampleRadius d S b n + S ≤ (n : ℝ) ^ 2 := by
  let D : ℝ := 2 * S + Real.sqrt (d : ℝ) * Real.sqrt (2 * (b + 4))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop D,
    Filter.eventually_ge_atTop (1 : ℕ)] with n hlogn hDn hn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogle : Real.log (n : ℝ) ≤ (n : ℝ) :=
    (Real.log_le_sub_one_of_pos hnreal).trans (by linarith)
  have hsqrtlog : Real.sqrt (Real.log (n : ℝ)) ≤ (n : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith
  have hsqrtOne : 1 ≤ Real.sqrt (Real.log (n : ℝ)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hlogn
  have hb4 : 0 ≤ 2 * (b + 4) := by positivity
  unfold gaussianPaperSampleRadius gaussianPaperRadiusExponent
  rw [show 2 * ((b + 4) * Real.log (n : ℝ)) =
      (2 * (b + 4)) * Real.log (n : ℝ) by ring,
    Real.sqrt_mul hb4]
  have hsqrtd : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hsqrtb : 0 ≤ Real.sqrt (2 * (b + 4)) := Real.sqrt_nonneg _
  calc
    S + Real.sqrt (d : ℝ) *
          (Real.sqrt (2 * (b + 4)) * Real.sqrt (Real.log (n : ℝ))) + S =
        2 * S + (Real.sqrt (d : ℝ) * Real.sqrt (2 * (b + 4))) *
          Real.sqrt (Real.log (n : ℝ)) := by ring
    _ ≤ D * Real.sqrt (Real.log (n : ℝ)) := by
      dsimp [D]
      nlinarith
    _ ≤ (n : ℝ) * (n : ℝ) := by gcongr
    _ = (n : ℝ) ^ 2 := by ring

/-- The Stirling base for the local Taylor remainder is eventually at most
`(log n)⁻¹ᐟ⁸`. -/
theorem eventually_gaussianPaperStirlingBase_le
    (d : ℕ) {C S b : ℝ} (hC : 0 < C) (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp 1 * gaussianPaperTaylorArgument d S b n /
          ((gaussianPaperMomentOrder C n : ℝ) + 1) ≤
        Real.log (n : ℝ) ^ (-1 / 8 : ℝ) := by
  let D := gaussianPaperTaylorConstant d S b
  have hD : 0 ≤ D := gaussianPaperTaylorConstant_nonneg d hS hb
  have hcoef : 0 ≤ Real.exp 1 * D / C := by positivity
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventually_gaussianPaperTaylorArgument_le d hS hb,
    eventually_gaussianPaperTaylorArgument_nonneg d hS hb,
    eventually_const_mul_log_log_le_log_rpow hcoef,
    hlog.eventually_ge_atTop 1, hloglog.eventually_gt_atTop 0]
      with n hA hA0 hsmall hlogn hloglogn
  let x := Real.log (n : ℝ)
  let y := Real.log x
  let L := gaussianPaperMomentOrder C n
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one hlogn
  have hy : 0 < y := by simpa only [x, y] using hloglogn
  have hceil : C * (x / y) ≤ (L : ℝ) := by
    simpa only [L, gaussianPaperMomentOrder, gaussianPaperLogScale, x, y] using
      (Nat.le_ceil (C * gaussianPaperLogScale n))
  have hscale : 0 < C * (x / y) := mul_pos hC (div_pos hx hy)
  have hden : 0 < (L : ℝ) + 1 := by positivity
  have hnum : 0 ≤ Real.exp 1 * D * Real.sqrt x := by positivity
  have hsmall' : (Real.exp 1 * D / C) * y ≤ x ^ (3 / 8 : ℝ) := by
    simpa only [D, x, y] using hsmall
  calc
    Real.exp 1 * gaussianPaperTaylorArgument d S b n / ((L : ℝ) + 1) ≤
        Real.exp 1 * (D * Real.sqrt x) / ((L : ℝ) + 1) := by
      gcongr
    _ = (Real.exp 1 * D * Real.sqrt x) / ((L : ℝ) + 1) := by ring
    _ ≤ (Real.exp 1 * D * Real.sqrt x) / (C * (x / y)) :=
      div_le_div_of_nonneg_left hnum hscale (by linarith)
    _ = ((Real.exp 1 * D / C) * y) * Real.sqrt x / x := by
      field_simp
      <;> ring
    _ ≤ x ^ (3 / 8 : ℝ) * Real.sqrt x / x := by
      gcongr
    _ = x ^ (-1 / 8 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
      have hsub : x ^ ((3 / 8 : ℝ) + 1 / 2 - 1) =
          x ^ ((3 / 8 : ℝ) + 1 / 2) / x := by
        simpa only [Real.rpow_one] using
          Real.rpow_sub hx ((3 / 8 : ℝ) + 1 / 2) 1
      rw [← hsub]
      norm_num
    _ = Real.log (n : ℝ) ^ (-1 / 8 : ℝ) := rfl

/-- Raising the logarithmic Stirling base to the paper order converts it
into a genuine inverse power of the sample size. -/
theorem eventually_gaussianPaperStirlingPower_le
    {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (Real.log (n : ℝ) ^ (-1 / 8 : ℝ)) ^
          (gaussianPaperMomentOrder C n + 1) ≤
        (n : ℝ) ^ (-C / 8 : ℝ) := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Filter.Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hlog
  filter_upwards [hlog.eventually_gt_atTop 1,
    hloglog.eventually_gt_atTop 0, Filter.eventually_ge_atTop (2 : ℕ)]
      with n hlogn hloglogn hn
  let x := Real.log (n : ℝ)
  let y := Real.log x
  let L := gaussianPaperMomentOrder C n
  have hx : 0 < x := lt_trans zero_lt_one hlogn
  have hy : 0 < y := by simpa only [x, y] using hloglogn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hceil : C * (x / y) ≤ (L : ℝ) := by
    simpa only [L, gaussianPaperMomentOrder, gaussianPaperLogScale, x, y] using
      (Nat.le_ceil (C * gaussianPaperLogScale n))
  have horder : C * x ≤ y * ((L : ℝ) + 1) := by
    have hceil' : C * x / y ≤ (L : ℝ) := by
      convert hceil using 1 <;> ring
    have := (div_le_iff₀ hy).mp hceil'
    nlinarith
  calc
    (x ^ (-1 / 8 : ℝ)) ^ (L + 1) =
        (x ^ (-1 / 8 : ℝ)) ^ (((L + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
    _ = x ^ ((-1 / 8 : ℝ) * ((L : ℝ) + 1)) := by
      rw [Real.rpow_mul hx.le]
      norm_num
    _ = Real.exp (Real.log x *
        ((-1 / 8 : ℝ) * ((L : ℝ) + 1))) :=
      Real.rpow_def_of_pos hx _
    _ ≤ Real.exp (Real.log (n : ℝ) * (-C / 8 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      change y * ((-1 / 8 : ℝ) * ((L : ℝ) + 1)) ≤
        x * (-C / 8 : ℝ)
      nlinarith
    _ = (n : ℝ) ^ (-C / 8 : ℝ) :=
      (Real.rpow_def_of_pos hnreal _).symm

/-- The exponential prefactor in the local Taylor error costs at most one
power of `n`. -/
theorem eventually_exp_two_gaussianPaperTaylorArgument_le
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp (2 * gaussianPaperTaylorArgument d S b n) ≤ n := by
  let D := gaussianPaperTaylorConstant d S b
  have hD : 0 ≤ D := gaussianPaperTaylorConstant_nonneg d hS hb
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gaussianPaperTaylorArgument_le d hS hb,
    hlog.eventually_ge_atTop ((2 * D) ^ 2),
    Filter.eventually_ge_atTop (1 : ℕ)] with n hA hlarge hn
  let x := Real.log (n : ℝ)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htwoD : 2 * D ≤ Real.sqrt x := by
    have hsqrt := Real.sqrt_le_sqrt hlarge
    calc
      2 * D = Real.sqrt ((2 * D) ^ 2) :=
        (Real.sqrt_sq (mul_nonneg (by norm_num) hD)).symm
      _ ≤ Real.sqrt x := by simpa only [x] using hsqrt
  have hsqrt0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt x) ^ 2 = x := by
    apply Real.sq_sqrt
    exact (sq_nonneg (2 * D)).trans hlarge
  have hexp : 2 * gaussianPaperTaylorArgument d S b n ≤ x := by
    have hA' : gaussianPaperTaylorArgument d S b n ≤ D * Real.sqrt x := by
      simpa only [D, x] using hA
    nlinarith
  calc
    Real.exp (2 * gaussianPaperTaylorArgument d S b n) ≤ Real.exp x :=
      Real.exp_le_exp.mpr hexp
    _ = (n : ℝ) := by
      dsimp [x]
      exact Real.exp_log hnreal

/-- The Gaussian moment dimension is always nonzero. -/
theorem gaussianMomentDimension_pos (d L : ℕ) :
    0 < gaussianMomentDimension d L := by
  change 0 < Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ)
  rw [finrank_monomialFeature]
  exact Nat.choose_pos (by omega)

/-- The moment dimension has precisely the polylogarithmic order required by
the paper, in an explicit eventual inequality. -/
theorem eventually_gaussianMomentDimension_le_logScale_pow
    (d : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n in Filter.atTop,
      (gaussianMomentDimension d (gaussianPaperMomentOrder C n) : ℝ) ≤
        ((4 * C + 1) * gaussianPaperLogScale n) ^ d := by
  filter_upwards [eventually_gaussianPaperMomentOrder_le hC,
    tendsto_gaussianPaperLogScale_atTop.eventually_gt_atTop (d : ℝ)]
      with n hm hs
  let L := gaussianPaperMomentOrder C n
  have hkNat : gaussianMomentDimension d L ≤ (2 * L + d) ^ d := by
    change Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) ≤ _
    rw [finrank_monomialFeature]
    exact Nat.choose_le_pow _ _
  have hkReal : (gaussianMomentDimension d L : ℝ) ≤
      (((2 * L + d : ℕ) : ℝ) ^ d) := by exact_mod_cast hkNat
  have hscale : 0 ≤ gaussianPaperLogScale n := by
    exact (Nat.cast_nonneg d).trans hs.le
  have hbase : (2 * L + d : ℝ) ≤
      (4 * C + 1) * gaussianPaperLogScale n := by
    change 2 * (L : ℝ) + d ≤ _
    nlinarith
  calc
    (gaussianMomentDimension d L : ℝ) ≤
        (((2 * L + d : ℕ) : ℝ) ^ d) := hkReal
    _ = (2 * (L : ℝ) + d) ^ d := by push_cast; rfl
    _ ≤ ((4 * C + 1) * gaussianPaperLogScale n) ^ d :=
      pow_le_pow_left₀ (by positivity) hbase d

/-- A coarser log-power form, convenient for entropy estimates. -/
theorem eventually_gaussianMomentDimension_le_log_pow
    (d : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n in Filter.atTop,
      (gaussianMomentDimension d (gaussianPaperMomentOrder C n) : ℝ) ≤
        (4 * C + 1) ^ d * Real.log (n : ℝ) ^ d := by
  filter_upwards [eventually_gaussianMomentDimension_le_logScale_pow d hC,
    eventually_gaussianPaperLogScale_nonneg_le_log] with n hk hs
  calc
    (gaussianMomentDimension d (gaussianPaperMomentOrder C n) : ℝ) ≤
        ((4 * C + 1) * gaussianPaperLogScale n) ^ d := hk
    _ = (4 * C + 1) ^ d * gaussianPaperLogScale n ^ d := by rw [mul_pow]
    _ ≤ (4 * C + 1) ^ d * Real.log (n : ℝ) ^ d := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hs.1 hs.2 d) (by positivity)

/-- In particular, the polylogarithmic moment dimension is eventually at
most the sample size (with room for two rounding slots). -/
theorem eventually_gaussianMomentDimension_add_two_le
    (d : ℕ) {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n in Filter.atTop,
      (gaussianMomentDimension d (gaussianPaperMomentOrder C n) : ℝ) + 2 ≤ n := by
  let A : ℝ := (4 * C + 1) ^ d
  have hsmall0 : (fun n : ℕ ↦ Real.log (n : ℝ) ^ d) =o[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ)) := by
    simpa only [Function.comp_apply, id_eq] using
      (Real.isLittleO_pow_log_id_atTop.comp_tendsto
        tendsto_natCast_atTop_atTop)
  have hsmall : (fun n : ℕ ↦ A * Real.log (n : ℝ) ^ d) =o[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ)) := hsmall0.const_mul_left A
  have hhalf := hsmall.bound (show (0 : ℝ) < 1 / 2 by norm_num)
  filter_upwards [eventually_gaussianMomentDimension_le_log_pow d hC,
    hhalf, Filter.eventually_ge_atTop (4 : ℕ)] with n hk hnsmall hnfour
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hlogpow : 0 ≤ Real.log (n : ℝ) ^ d := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA hlogpow),
    abs_of_nonneg hn0] at hnsmall
  have hnfourReal : (4 : ℝ) ≤ n := by exact_mod_cast hnfour
  dsimp [A] at hnsmall
  nlinarith

theorem gaussianPaperEpsilon_pos {n : ℕ} (hn : 0 < n) :
    0 < gaussianPaperEpsilon n := by
  unfold gaussianPaperEpsilon
  positivity

theorem gaussianPaperWeightDenominator_pos
    (d : ℕ) (C : ℝ) {n : ℕ} (hn : 0 < n) :
    0 < gaussianPaperWeightDenominator d C n := by
  unfold gaussianPaperWeightDenominator
  apply Nat.ceil_pos.mpr
  exact mul_pos (by
      exact_mod_cast (gaussianMomentDimension_pos d
        (gaussianPaperMomentOrder C n)))
    (pow_pos (by exact_mod_cast hn) 16)

/-- Ceiling bounds for the paper's weight grid. -/
theorem gaussianPaperWeightDenominator_bounds
    (d : ℕ) (C : ℝ) {n : ℕ} (hn : 0 < n) :
    (gaussianMomentDimension d (gaussianPaperMomentOrder C n) : ℝ) *
          (n : ℝ) ^ 16 ≤ gaussianPaperWeightDenominator d C n ∧
      (gaussianPaperWeightDenominator d C n : ℝ) <
        (gaussianMomentDimension d (gaussianPaperMomentOrder C n) : ℝ) *
            (n : ℝ) ^ 16 + 1 := by
  have hbase : 0 ≤
      (gaussianMomentDimension d (gaussianPaperMomentOrder C n) : ℝ) *
        (n : ℝ) ^ 16 := by positivity
  unfold gaussianPaperWeightDenominator
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one hbase⟩

/-- Simplex rounding contributes at most `2 n⁻¹⁶`; the moment dimension
cancels from the choice `M = ceil(k n^16)`. -/
theorem gaussianPaper_weight_rounding_le
    (d : ℕ) (C : ℝ) {n : ℕ} (hn : 0 < n) :
    2 * gaussianMomentDimension d (gaussianPaperMomentOrder C n) /
        gaussianPaperWeightDenominator d C n ≤
      2 / (n : ℝ) ^ 16 := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hMreal : (0 : ℝ) < gaussianPaperWeightDenominator d C n := by
    exact_mod_cast gaussianPaperWeightDenominator_pos d C hn
  have hceil := (gaussianPaperWeightDenominator_bounds d C hn).1
  rw [div_le_div_iff₀ hMreal (pow_pos hnreal 16)]
  nlinarith

theorem eventually_gaussianPaper_weightTerm_le
    (d : ℕ) {C S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp (2 * gaussianPaperTaylorArgument d S b n) *
          (2 * gaussianMomentDimension d (gaussianPaperMomentOrder C n) /
            gaussianPaperWeightDenominator d C n) ≤
        2 / (n : ℝ) ^ 15 := by
  filter_upwards [eventually_exp_two_gaussianPaperTaylorArgument_le d hS hb,
    Filter.eventually_ge_atTop (1 : ℕ)] with n hexp hn
  have hnpos : 0 < n := by omega
  have hround := gaussianPaper_weight_rounding_le d C hnpos
  calc
    Real.exp (2 * gaussianPaperTaylorArgument d S b n) *
        (2 * gaussianMomentDimension d (gaussianPaperMomentOrder C n) /
          gaussianPaperWeightDenominator d C n) ≤
        (n : ℝ) * (2 / (n : ℝ) ^ 16) := by gcongr
    _ = 2 / (n : ℝ) ^ 15 := by field_simp

/-- With the paper denominator, even the exponentially weighted simplex
rounding term is eventually below one half. -/
theorem eventually_gaussianPaper_weightSmall
    (d : ℕ) {C S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp (2 * gaussianPaperTaylorArgument d S b n) *
          (2 * gaussianMomentDimension d (gaussianPaperMomentOrder C n) /
            gaussianPaperWeightDenominator d C n) ≤ 1 / 2 := by
  filter_upwards [eventually_exp_two_gaussianPaperTaylorArgument_le d hS hb,
    Filter.eventually_ge_atTop (2 : ℕ)] with n hexp hn
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnTwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hround := gaussianPaper_weight_rounding_le d C hnpos
  have hpow : (2 : ℝ) ^ 15 ≤ (n : ℝ) ^ 15 :=
    pow_le_pow_left₀ (by norm_num) hnTwo 15
  calc
    Real.exp (2 * gaussianPaperTaylorArgument d S b n) *
        (2 * gaussianMomentDimension d (gaussianPaperMomentOrder C n) /
          gaussianPaperWeightDenominator d C n) ≤
        (n : ℝ) * (2 / (n : ℝ) ^ 16) := by gcongr
    _ = 2 / (n : ℝ) ^ 15 := by
      field_simp
    _ ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (pow_pos hnreal 15) (by norm_num)]
      norm_num at hpow ⊢
      linarith

/-- A convenient consequence of Stirling's global lower bound.  It is the
factorial estimate used for both Taylor remainders in the Gaussian net. -/
theorem pow_div_factorial_le_stirling {x : ℝ} (hx : 0 ≤ x)
    {m : ℕ} (hm : 0 < m) :
    x ^ m / (m.factorial : ℝ) ≤
      (Real.exp 1 * x / m) ^ m := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * m) := by
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have hpi := Real.pi_gt_three
    have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hbase : 0 ≤ (m : ℝ) / Real.exp 1 := by positivity
  have hden : ((m : ℝ) / Real.exp 1) ^ m ≤ (m.factorial : ℝ) := by
    calc
      ((m : ℝ) / Real.exp 1) ^ m ≤
          Real.sqrt (2 * Real.pi * m) * ((m : ℝ) / Real.exp 1) ^ m :=
        le_mul_of_one_le_left (pow_nonneg hbase _) hsqrt
      _ ≤ (m.factorial : ℝ) := Stirling.le_factorial_stirling m
  calc
    x ^ m / (m.factorial : ℝ) ≤
        x ^ m / (((m : ℝ) / Real.exp 1) ^ m) :=
      div_le_div_of_nonneg_left (pow_nonneg hx _)
        (pow_pos (div_pos hmreal (Real.exp_pos 1)) _) hden
    _ = (Real.exp 1 * x / m) ^ m := by
      rw [← div_pow]
      congr 1
      field_simp

/-- Stirling remainder bound with a user-supplied upper bound on the base. -/
theorem pow_div_factorial_le_pow {x ρ : ℝ} (hx : 0 ≤ x)
    {m : ℕ} (hm : 0 < m) (hρ : Real.exp 1 * x / m ≤ ρ) :
    x ^ m / (m.factorial : ℝ) ≤ ρ ^ m := by
  exact (pow_div_factorial_le_stirling hx hm).trans
    (pow_le_pow_left₀ (by positivity) hρ m)

/-- The moment dimension in the Gaussian net is exactly the number of
monomials of total degree at most `2 * L`. -/
theorem gaussianMomentDimension_eq_choose (d L : ℕ) :
    gaussianMomentDimension d L = (2 * L + d).choose d := by
  exact finrank_monomialFeature d (2 * L)

/-- Elementary polynomial upper bound for the moment dimension. -/
theorem gaussianMomentDimension_le_pow (d L : ℕ) :
    gaussianMomentDimension d L ≤ (2 * L + d) ^ d := by
  rw [gaussianMomentDimension_eq_choose]
  exact Nat.choose_le_pow _ _

/-- The global moment-matching error with its factorial eliminated by the
effective Stirling bound. -/
theorem gaussianMomentHellingerError_le_stirling {S : ℝ} (hS : 0 ≤ S)
    (L : ℕ) :
    gaussianMomentHellingerError S L ≤
      (4 * Real.exp (S ^ 2) *
        (Real.exp 1 * S ^ 2 / (2 * L + 1)) ^ (2 * L + 1)) ^
          (1 / 2 : ℝ) := by
  unfold gaussianMomentHellingerError
  have hratio :
      (S ^ 2) ^ (2 * L + 1) / ((2 * L + 1).factorial : ℝ) ≤
        (Real.exp 1 * S ^ 2 / (2 * L + 1)) ^ (2 * L + 1) := by
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
      Nat.cast_mul, Nat.cast_ofNat] using
      (pow_div_factorial_le_stirling (sq_nonneg S)
        (Nat.zero_lt_succ (2 * L)))
  have hinside :
      4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (2 * L + 1) /
          ((2 * L + 1).factorial : ℝ)) ≤
        4 * Real.exp (S ^ 2) *
          (Real.exp 1 * S ^ 2 / (2 * L + 1)) ^ (2 * L + 1) := by
    calc
      4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (2 * L + 1) /
          ((2 * L + 1).factorial : ℝ)) =
          (4 * Real.exp (S ^ 2)) *
            ((S ^ 2) ^ (2 * L + 1) /
              ((2 * L + 1).factorial : ℝ)) := by ring
      _ ≤ (4 * Real.exp (S ^ 2)) *
          (Real.exp 1 * S ^ 2 / (2 * L + 1)) ^ (2 * L + 1) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  exact hinside

/-- The local relative-density Taylor error with its factorial eliminated by
the effective Stirling bound. -/
theorem gaussianMomentRelativeError_le_stirling {T S : ℝ}
    (hA : 0 ≤ T * S + S ^ 2 / 2) (L : ℕ) :
    gaussianMomentRelativeError T S L ≤
      2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
          (Real.exp 1 * (T * S + S ^ 2 / 2) / (L + 1)) ^ (L + 1) := by
  unfold gaussianMomentRelativeError
  have hratio :
      (T * S + S ^ 2 / 2) ^ (L + 1) / ((L + 1).factorial : ℝ) ≤
        (Real.exp 1 * (T * S + S ^ 2 / 2) / (L + 1)) ^ (L + 1) := by
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
      (pow_div_factorial_le_stirling hA (Nat.zero_lt_succ L))
  exact mul_le_mul_of_nonneg_left hratio (by positivity)

/-- Explicit inverse-power bound for the local relative-density Taylor
error.  Choosing `C > 8` makes the exponent negative. -/
theorem eventually_gaussianMomentRelativeError_paper_le
    (d : ℕ) {C S b : ℝ} (hC : 0 < C) (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      gaussianMomentRelativeError (gaussianPaperSampleRadius d S b n) S
          (gaussianPaperMomentOrder C n) ≤
        2 * (n : ℝ) ^ (1 - C / 8 : ℝ) := by
  filter_upwards [eventually_gaussianPaperTaylorArgument_nonneg d hS hb,
    eventually_gaussianPaperStirlingBase_le d hC hS hb,
    eventually_gaussianPaperStirlingPower_le hC,
    eventually_exp_two_gaussianPaperTaylorArgument_le d hS hb,
    Filter.eventually_ge_atTop (1 : ℕ)]
      with n hA0 hbase hpower hexp hn
  let A := gaussianPaperTaylorArgument d S b n
  let L := gaussianPaperMomentOrder C n
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbase0 : 0 ≤ Real.exp 1 * A / ((L : ℝ) + 1) := by positivity
  have hpowBase :
      (Real.exp 1 * A / ((L : ℝ) + 1)) ^ (L + 1) ≤
        (Real.log (n : ℝ) ^ (-1 / 8 : ℝ)) ^ (L + 1) := by
    apply pow_le_pow_left₀ hbase0
    simpa only [A, L] using hbase
  have hstirling := gaussianMomentRelativeError_le_stirling hA0 L
  calc
    gaussianMomentRelativeError (gaussianPaperSampleRadius d S b n) S L ≤
        2 * Real.exp (2 * A) *
          (Real.exp 1 * A / ((L : ℝ) + 1)) ^ (L + 1) := by
      simpa only [A, L, gaussianPaperTaylorArgument] using hstirling
    _ ≤ 2 * Real.exp (2 * A) *
        (Real.log (n : ℝ) ^ (-1 / 8 : ℝ)) ^ (L + 1) := by
      gcongr
    _ ≤ 2 * (n : ℝ) *
        (Real.log (n : ℝ) ^ (-1 / 8 : ℝ)) ^ (L + 1) := by
      gcongr
    _ ≤ 2 * (n : ℝ) * (n : ℝ) ^ (-C / 8 : ℝ) := by
      gcongr
    _ = 2 * (n : ℝ) ^ (1 - C / 8 : ℝ) := by
      calc
        2 * (n : ℝ) * (n : ℝ) ^ (-C / 8 : ℝ) =
            2 * ((n : ℝ) * (n : ℝ) ^ (-C / 8 : ℝ)) := by ring
        _ = 2 * ((n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-C / 8 : ℝ)) := by
          rw [Real.rpow_one]
        _ = 2 * (n : ℝ) ^ ((1 : ℝ) + (-C / 8 : ℝ)) := by
          rw [Real.rpow_add hnreal]
        _ = 2 * (n : ℝ) ^ (1 - C / 8 : ℝ) := by ring_nf

/-- Numerical specialization used in the final theorem. -/
theorem eventually_gaussianMomentRelativeError_256_le
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      gaussianMomentRelativeError (gaussianPaperSampleRadius d S b n) S
          (gaussianPaperMomentOrder 256 n) ≤ 2 / (n : ℝ) ^ 31 := by
  filter_upwards [eventually_gaussianMomentRelativeError_paper_le d
    (show (0 : ℝ) < 256 by norm_num) hS hb] with n hn
  convert hn using 1
  norm_num [Real.rpow_neg_natCast, zpow_neg, div_eq_mul_inv]
  rfl

/-- The global moment-matching Hellinger error inherits the same inverse
power before taking its square root. -/
theorem eventually_gaussianMomentHellingerError_paper_le
    {C S : ℝ} (hC : 0 < C) (hS : 0 ≤ S) :
    ∀ᶠ n : ℕ in Filter.atTop,
      gaussianMomentHellingerError S (gaussianPaperMomentOrder C n) ≤
        (4 * Real.exp (S ^ 2) * (n : ℝ) ^ (-C / 8 : ℝ)) ^
          (1 / 2 : ℝ) := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gaussianPaperStirlingBase_le 0 hC hS
      (show (0 : ℝ) ≤ 0 by norm_num),
    eventually_gaussianPaperStirlingPower_le hC,
    hlog.eventually_ge_atTop 1] with n hbase hpower hlogn
  let L := gaussianPaperMomentOrder C n
  let A := gaussianPaperTaylorArgument 0 S 0 n
  let ρ := Real.log (n : ℝ) ^ (-1 / 8 : ℝ)
  have hA : S ^ 2 ≤ A := by
    dsimp [A, gaussianPaperTaylorArgument, gaussianPaperSampleRadius,
      gaussianPaperRadiusExponent]
    simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul, add_zero]
    nlinarith [sq_nonneg S]
  have hcompare :
      Real.exp 1 * S ^ 2 / ((2 * L + 1 : ℕ) : ℝ) ≤
        Real.exp 1 * A / ((L : ℝ) + 1) := by
    calc
      Real.exp 1 * S ^ 2 / ((2 * L + 1 : ℕ) : ℝ) ≤
          Real.exp 1 * S ^ 2 / ((L : ℝ) + 1) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact_mod_cast (show L + 1 ≤ 2 * L + 1 by omega)
      _ ≤ Real.exp 1 * A / ((L : ℝ) + 1) := by
        gcongr
  have hbase' :
      Real.exp 1 * S ^ 2 / ((2 * L + 1 : ℕ) : ℝ) ≤ ρ :=
    hcompare.trans (by simpa only [A, L, ρ] using hbase)
  have hbase0 : 0 ≤
      Real.exp 1 * S ^ 2 / ((2 * L + 1 : ℕ) : ℝ) := by positivity
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := by
    dsimp [ρ]
    exact Real.rpow_le_one_of_one_le_of_nonpos hlogn (by norm_num)
  have hbasePow :
      (Real.exp 1 * S ^ 2 / ((2 * L + 1 : ℕ) : ℝ)) ^ (2 * L + 1) ≤
        ρ ^ (2 * L + 1) := pow_le_pow_left₀ hbase0 hbase' _
  have hdegree : ρ ^ (2 * L + 1) ≤ ρ ^ (L + 1) := by
    exact pow_le_pow_of_le_one hρ0 hρ1 (by omega)
  have hρpower : ρ ^ (L + 1) ≤ (n : ℝ) ^ (-C / 8 : ℝ) := by
    simpa only [ρ, L] using hpower
  have hstirling := gaussianMomentHellingerError_le_stirling hS L
  calc
    gaussianMomentHellingerError S L ≤
        (4 * Real.exp (S ^ 2) *
          (Real.exp 1 * S ^ 2 / ((2 * L + 1 : ℕ) : ℝ)) ^
            (2 * L + 1)) ^ (1 / 2 : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using
        hstirling
    _ ≤ (4 * Real.exp (S ^ 2) * (n : ℝ) ^ (-C / 8 : ℝ)) ^
        (1 / 2 : ℝ) := by
      apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
      gcongr
      exact hbasePow.trans (hdegree.trans hρpower)

/-- At the fixed order constant used below, the global Hellinger remainder
is eventually smaller than `1/n`. -/
theorem eventually_gaussianMomentHellingerError_256_le_inv
    {S : ℝ} (hS : 0 ≤ S) :
    ∀ᶠ n : ℕ in Filter.atTop,
      gaussianMomentHellingerError S (gaussianPaperMomentOrder 256 n) ≤
        1 / (n : ℝ) := by
  let A := 4 * Real.exp (S ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  filter_upwards [eventually_gaussianMomentHellingerError_paper_le
      (show (0 : ℝ) < 256 by norm_num) hS,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop A,
    Filter.eventually_ge_atTop (1 : ℕ)] with n hglobal hAn hn
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hA30 : A ≤ (n : ℝ) ^ 30 := by
    calc
      A ≤ (n : ℝ) := hAn
      _ = (n : ℝ) ^ 1 := by ring
      _ ≤ (n : ℝ) ^ 30 := pow_le_pow_right₀ hnOne (by omega)
  have hinside : A * (n : ℝ) ^ (-256 / 8 : ℝ) ≤
      1 / (n : ℝ) ^ 2 := by
    have hneg : (n : ℝ) ^ (-256 / 8 : ℝ) = 1 / (n : ℝ) ^ 32 := by
      norm_num [Real.rpow_neg_natCast, zpow_neg, div_eq_mul_inv]
      rfl
    rw [hneg]
    calc
      A * (1 / (n : ℝ) ^ 32) ≤
          (n : ℝ) ^ 30 * (1 / (n : ℝ) ^ 32) := by gcongr
      _ = 1 / (n : ℝ) ^ 2 := by field_simp
  calc
    gaussianMomentHellingerError S (gaussianPaperMomentOrder 256 n) ≤
        (A * (n : ℝ) ^ (-256 / 8 : ℝ)) ^ (1 / 2 : ℝ) := by
      simpa only [A] using hglobal
    _ ≤ (1 / (n : ℝ) ^ 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hinside (by norm_num)
    _ = 1 / (n : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      have hsquare : 1 / (n : ℝ) ^ 2 = (1 / (n : ℝ)) ^ 2 := by
        field_simp
      rw [hsquare, Real.sqrt_sq (by positivity)]

theorem eventually_gaussianMomentRelativeError_256_le_half
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      gaussianMomentRelativeError (gaussianPaperSampleRadius d S b n) S
          (gaussianPaperMomentOrder 256 n) ≤ 1 / 2 := by
  filter_upwards [eventually_gaussianMomentRelativeError_256_le d hS hb,
    Filter.eventually_ge_atTop (2 : ℕ)] with n hrel hn
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (4 : ℝ) ≤ (n : ℝ) ^ 31 := by
    calc
      (4 : ℝ) ≤ 2 ^ 31 := by norm_num
      _ ≤ (n : ℝ) ^ 31 := pow_le_pow_left₀ (by norm_num) hnreal 31
  exact hrel.trans (by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 31) (by norm_num)]
    linarith)

/-- The direct (non-entropy) squared-Hellinger approximation error is only
`O(1/n)` and hence is lower order than the displayed paper rate. -/
theorem eventually_gaussianNetHellingerSqError_256_le
    (d : ℕ) {S : ℝ} (hS : 0 ≤ S) :
    ∀ᶠ n : ℕ in Filter.atTop,
      gaussianNetHellingerSqError d (gaussianPaperMomentOrder 256 n)
          (gaussianPaperWeightDenominator d 256 n) S
          (gaussianPaperEpsilon n) ≤ 11 / (n : ℝ) := by
  filter_upwards [eventually_gaussianMomentHellingerError_256_le_inv hS,
    Filter.eventually_ge_atTop (1 : ℕ)] with n hglobal hn
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hround := gaussianPaper_weight_rounding_le d (256 : ℝ) hnpos
  have hpow16 : (n : ℝ) ≤ (n : ℝ) ^ 16 := by
    calc
      (n : ℝ) = (n : ℝ) ^ 1 := by ring
      _ ≤ (n : ℝ) ^ 16 := pow_le_pow_right₀ hnOne (by omega)
  have hpow32 : (n : ℝ) ≤ (n : ℝ) ^ 32 := by
    calc
      (n : ℝ) = (n : ℝ) ^ 1 := by ring
      _ ≤ (n : ℝ) ^ 32 := pow_le_pow_right₀ hnOne (by omega)
  have heps : gaussianPaperEpsilon n ^ 2 ≤ 1 / (n : ℝ) := by
    have heq : gaussianPaperEpsilon n ^ 2 = 1 / (n : ℝ) ^ 32 := by
      unfold gaussianPaperEpsilon
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_left (by norm_num) hnreal hpow32
  have hround' :
      4 * (2 * gaussianMomentDimension d (gaussianPaperMomentOrder 256 n) /
          gaussianPaperWeightDenominator d 256 n) ≤ 8 / (n : ℝ) := by
    calc
      4 * (2 * gaussianMomentDimension d (gaussianPaperMomentOrder 256 n) /
          gaussianPaperWeightDenominator d 256 n) ≤
          4 * (2 / (n : ℝ) ^ 16) :=
        mul_le_mul_of_nonneg_left hround (by norm_num)
      _ = 8 / (n : ℝ) ^ 16 := by ring
      _ ≤ 8 / (n : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) hnreal hpow16
  unfold gaussianNetHellingerSqError
  calc
    2 * gaussianMomentHellingerError S (gaussianPaperMomentOrder 256 n) +
        gaussianPaperEpsilon n ^ 2 +
        4 * (2 * gaussianMomentDimension d (gaussianPaperMomentOrder 256 n) /
          gaussianPaperWeightDenominator d 256 n) ≤
      2 * (1 / (n : ℝ)) + 1 / (n : ℝ) + 8 / (n : ℝ) :=
        add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left hglobal (by norm_num)) heps)
          hround'
    _ = 11 / (n : ℝ) := by ring

/-- The fully explicit paper net has total log-density error at most `1/n`,
which is the small-error hypothesis needed by the finite likelihood test. -/
theorem eventually_gaussianNetLogError_256
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) * gaussianNetLogError d (gaussianPaperMomentOrder 256 n)
        (gaussianPaperWeightDenominator d 256 n)
        (gaussianPaperSampleRadius d S b n) S (gaussianPaperEpsilon n) ≤ 1 := by
  filter_upwards [eventually_gaussianPaperSampleRadius_add_le_sq d hS hb,
    eventually_gaussianPaper_weightTerm_le d (C := (256 : ℝ)) hS hb,
    eventually_gaussianMomentRelativeError_256_le d hS hb,
    Filter.eventually_ge_atTop (2 : ℕ)] with n hT hweight hrel hn
  let T := gaussianPaperSampleRadius d S b n
  let L := gaussianPaperMomentOrder 256 n
  let M := gaussianPaperWeightDenominator d 256 n
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnTwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmesh : (T + S) * gaussianPaperEpsilon n ≤ 1 / (n : ℝ) ^ 14 := by
    unfold gaussianPaperEpsilon
    calc
      (T + S) * ((n : ℝ) ^ 16)⁻¹ ≤
          (n : ℝ) ^ 2 * ((n : ℝ) ^ 16)⁻¹ := by
        gcongr
      _ = 1 / (n : ℝ) ^ 14 := by field_simp
  have hδ : gaussianNetLogError d L M T S (gaussianPaperEpsilon n) ≤
      1 / (n : ℝ) ^ 14 + 4 / (n : ℝ) ^ 15 +
        4 / (n : ℝ) ^ 31 := by
    unfold gaussianNetLogError
    have hweight' : Real.exp (2 * (T * S + S ^ 2 / 2)) *
        (2 * gaussianMomentDimension d L / M) ≤ 2 / (n : ℝ) ^ 15 := by
      simpa only [T, L, M, gaussianPaperTaylorArgument] using hweight
    have hrel' : gaussianMomentRelativeError T S L ≤ 2 / (n : ℝ) ^ 31 := by
      simpa only [T, L] using hrel
    have hweightTwo :
        2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
            (2 * gaussianMomentDimension d L / M) ≤
          2 * (2 / (n : ℝ) ^ 15) := by
      calc
        2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
            (2 * gaussianMomentDimension d L / M) =
          2 * (Real.exp (2 * (T * S + S ^ 2 / 2)) *
            (2 * gaussianMomentDimension d L / M)) := by ring
        _ ≤ 2 * (2 / (n : ℝ) ^ 15) :=
          mul_le_mul_of_nonneg_left hweight' (by norm_num)
    have hrelTwo : 2 * gaussianMomentRelativeError T S L ≤
        2 * (2 / (n : ℝ) ^ 31) :=
      mul_le_mul_of_nonneg_left hrel' (by norm_num)
    calc
      (T + S) * gaussianPaperEpsilon n +
          2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
            (2 * gaussianMomentDimension d L / M) +
          2 * gaussianMomentRelativeError T S L ≤
        1 / (n : ℝ) ^ 14 + 2 * (2 / (n : ℝ) ^ 15) +
          2 * (2 / (n : ℝ) ^ 31) :=
        add_le_add (add_le_add hmesh hweightTwo) hrelTwo
      _ = 1 / (n : ℝ) ^ 14 + 4 / (n : ℝ) ^ 15 +
          4 / (n : ℝ) ^ 31 := by ring
  have h13pow : (2 : ℝ) ≤ (n : ℝ) ^ 13 := by
    calc
      (2 : ℝ) ≤ 2 ^ 13 := by norm_num
      _ ≤ (n : ℝ) ^ 13 := pow_le_pow_left₀ (by norm_num) hnTwo 13
  have h14pow : (16 : ℝ) ≤ (n : ℝ) ^ 14 := by
    calc
      (16 : ℝ) ≤ 2 ^ 14 := by norm_num
      _ ≤ (n : ℝ) ^ 14 := pow_le_pow_left₀ (by norm_num) hnTwo 14
  have h30pow : (16 : ℝ) ≤ (n : ℝ) ^ 30 := by
    calc
      (16 : ℝ) ≤ 2 ^ 30 := by norm_num
      _ ≤ (n : ℝ) ^ 30 := pow_le_pow_left₀ (by norm_num) hnTwo 30
  have h13 : 1 / (n : ℝ) ^ 13 ≤ 1 / 2 := by
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h13pow
  have h14 : 4 / (n : ℝ) ^ 14 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (pow_pos hnreal 14) (by norm_num)]
    nlinarith
  have h30 : 4 / (n : ℝ) ^ 30 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (pow_pos hnreal 30) (by norm_num)]
    nlinarith
  calc
    (n : ℝ) * gaussianNetLogError d L M T S (gaussianPaperEpsilon n) ≤
        (n : ℝ) * (1 / (n : ℝ) ^ 14 + 4 / (n : ℝ) ^ 15 +
          4 / (n : ℝ) ^ 31) := mul_le_mul_of_nonneg_left hδ hnreal.le
    _ = 1 / (n : ℝ) ^ 13 + 4 / (n : ℝ) ^ 14 +
        4 / (n : ℝ) ^ 30 := by field_simp
    _ ≤ 1 := by linarith

/-- The coordinate-cell count is bounded by its unfloored real expression.
This is the location-net entropy estimate before taking logarithms. -/
theorem boundedLocationCellCount_cast_le (d : ℕ) {S ε : ℝ}
    (hS : 0 ≤ S) (hε : 0 < ε) :
    (boundedLocationCellCount d S ε : ℝ) ≤
      2 * S * ((d : ℝ) + 2) / ε + 1 := by
  have hw : 0 < boundedLocationCellWidth d ε :=
    boundedLocationCellWidth_pos d hε
  have hx : 0 ≤ 2 * S / boundedLocationCellWidth d ε := by positivity
  unfold boundedLocationCellCount
  push_cast
  calc
    (Nat.floor (2 * S / boundedLocationCellWidth d ε) : ℝ) + 1 ≤
        2 * S / boundedLocationCellWidth d ε + 1 := by
      gcongr
      exact Nat.floor_le hx
    _ = 2 * S * ((d : ℝ) + 2) / ε + 1 := by
      unfold boundedLocationCellWidth
      field_simp

/-- Exact logarithm of the explicit Gaussian net cardinality. -/
theorem log_gaussianNetCardBound (d L M : ℕ) (S ε : ℝ) :
    Real.log (gaussianNetCardBound d L M S ε : ℝ) =
      ((d * (gaussianMomentDimension d L + 1) : ℕ) : ℝ) *
          Real.log (boundedLocationCellCount d S ε : ℝ) +
        (gaussianMomentDimension d L : ℝ) * Real.log ((M : ℝ) + 1) := by
  let c := boundedLocationCellCount d S ε
  let k := gaussianMomentDimension d L
  have hc : c ≠ 0 := by
    dsimp [c, boundedLocationCellCount]
    omega
  have hM : (M : ℝ) + 1 ≠ 0 := by positivity
  rw [gaussianNetCardBound]
  push_cast
  rw [Real.log_mul (pow_ne_zero _ (pow_ne_zero _ (mod_cast hc)))
      (pow_ne_zero _ hM), Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- A convenient monotone form of the net entropy bound.  The parameters
`C` and `N` may subsequently be replaced by simple powers of the sample
size. -/
theorem log_gaussianNetCardBound_le (d L M : ℕ) {S ε C N : ℝ}
    (hC : 1 ≤ C)
    (hcell : (boundedLocationCellCount d S ε : ℝ) ≤ C)
    (hN : 1 ≤ N) (hgrid : (M : ℝ) + 1 ≤ N) :
    Real.log (gaussianNetCardBound d L M S ε : ℝ) ≤
      ((d * (gaussianMomentDimension d L + 1) : ℕ) : ℝ) * Real.log C +
        (gaussianMomentDimension d L : ℝ) * Real.log N := by
  rw [log_gaussianNetCardBound]
  have hcpos : 0 < (boundedLocationCellCount d S ε : ℝ) := by
    unfold boundedLocationCellCount
    positivity
  have hMpos : 0 < (M : ℝ) + 1 := by positivity
  have hlogcell : Real.log (boundedLocationCellCount d S ε : ℝ) ≤
      Real.log C := Real.log_le_log hcpos hcell
  have hloggrid : Real.log ((M : ℝ) + 1) ≤ Real.log N :=
    Real.log_le_log hMpos hgrid
  gcongr

/-- The explicit net constructed with the paper's choices has the claimed
entropy order `(log n)^(d+1)/(log log n)^d`.  This is stated as an eventual
finite-sample inequality with a displayed constant. -/
theorem eventually_log_gaussianNetCardBound_paper_le
    (d : ℕ) {C S : ℝ} (hC : 0 < C) (hS : 0 ≤ S) :
    ∀ᶠ n in Filter.atTop,
      Real.log (gaussianNetCardBound d (gaussianPaperMomentOrder C n)
        (gaussianPaperWeightDenominator d C n) S
        (gaussianPaperEpsilon n) : ℝ) ≤
      17 * ((d : ℝ) + 1) * ((4 * C + 1) ^ d + 1) *
        gaussianPaperLogScale n ^ d * Real.log (n : ℝ) := by
  let A : ℝ := 2 * S * ((d : ℝ) + 2) + 1
  have hAevent : ∀ᶠ n : ℕ in Filter.atTop, A ≤ n := by
    exact tendsto_natCast_atTop_atTop.eventually_ge_atTop A
  filter_upwards [hAevent,
    eventually_gaussianMomentDimension_add_two_le d hC,
    eventually_gaussianMomentDimension_le_logScale_pow d hC,
    tendsto_gaussianPaperLogScale_atTop.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop (2 : ℕ)] with n hAn hkTwo hkScale hscale hnTwo
  let L := gaussianPaperMomentOrder C n
  let M := gaussianPaperWeightDenominator d C n
  let k := gaussianMomentDimension d L
  have hn : 0 < n := lt_of_lt_of_le (by omega) hnTwo
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnPowOne : (1 : ℝ) ≤ (n : ℝ) ^ 16 := one_le_pow₀ hnOne
  have heps : 0 < gaussianPaperEpsilon n := gaussianPaperEpsilon_pos hn
  have hcell0 := boundedLocationCellCount_cast_le d hS heps
  have hcellFormula :
      2 * S * ((d : ℝ) + 2) / gaussianPaperEpsilon n + 1 =
        2 * S * ((d : ℝ) + 2) * (n : ℝ) ^ 16 + 1 := by
    unfold gaussianPaperEpsilon
    field_simp
  have hcell : (boundedLocationCellCount d S (gaussianPaperEpsilon n) : ℝ) ≤
      (n : ℝ) ^ 17 := by
    calc
      (boundedLocationCellCount d S (gaussianPaperEpsilon n) : ℝ) ≤
          2 * S * ((d : ℝ) + 2) / gaussianPaperEpsilon n + 1 := hcell0
      _ = 2 * S * ((d : ℝ) + 2) * (n : ℝ) ^ 16 + 1 := hcellFormula
      _ ≤ A * (n : ℝ) ^ 16 := by
        dsimp [A]
        nlinarith [sq_nonneg ((n : ℝ) ^ 8)]
      _ ≤ (n : ℝ) * (n : ℝ) ^ 16 :=
        mul_le_mul_of_nonneg_right hAn (pow_nonneg hnreal.le _)
      _ = (n : ℝ) ^ 17 := by ring
  have hMupper := (gaussianPaperWeightDenominator_bounds d C hn).2
  have hkTwo' : (k : ℝ) + 2 ≤ n := by simpa only [k, L] using hkTwo
  have hgrid : (M : ℝ) + 1 ≤ (n : ℝ) ^ 17 := by
    calc
      (M : ℝ) + 1 ≤ (k : ℝ) * (n : ℝ) ^ 16 + 2 := by
        dsimp [M, k, L] at hMupper ⊢
        linarith
      _ ≤ ((k : ℝ) + 2) * (n : ℝ) ^ 16 := by
        nlinarith
      _ ≤ (n : ℝ) * (n : ℝ) ^ 16 :=
        mul_le_mul_of_nonneg_right hkTwo' (pow_nonneg hnreal.le _)
      _ = (n : ℝ) ^ 17 := by ring
  have hpowerOne : (1 : ℝ) ≤ (n : ℝ) ^ 17 := one_le_pow₀ hnOne
  have hraw := log_gaussianNetCardBound_le d L M
    hpowerOne hcell hpowerOne hgrid
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnOne
  rw [Real.log_pow] at hraw
  push_cast at hraw
  have hraw' :
      Real.log (gaussianNetCardBound d L M S (gaussianPaperEpsilon n) : ℝ) ≤
        17 * ((d : ℝ) + 1) * ((k : ℝ) + 1) * Real.log (n : ℝ) := by
    calc
      Real.log (gaussianNetCardBound d L M S (gaussianPaperEpsilon n) : ℝ) ≤
          (d * (k + 1)) * (17 * Real.log (n : ℝ)) +
            k * (17 * Real.log (n : ℝ)) := hraw
      _ ≤ 17 * ((d : ℝ) + 1) * ((k : ℝ) + 1) * Real.log (n : ℝ) := by
        nlinarith
  have hkScale' : (k : ℝ) ≤
      (4 * C + 1) ^ d * gaussianPaperLogScale n ^ d := by
    simpa only [k, L, mul_pow] using hkScale
  have hscalePow : (1 : ℝ) ≤ gaussianPaperLogScale n ^ d :=
    one_le_pow₀ hscale
  have hkOne : (k : ℝ) + 1 ≤
      ((4 * C + 1) ^ d + 1) * gaussianPaperLogScale n ^ d := by
    nlinarith [show 0 ≤ (4 * C + 1) ^ d by positivity]
  calc
    Real.log (gaussianNetCardBound d (gaussianPaperMomentOrder C n)
        (gaussianPaperWeightDenominator d C n) S
        (gaussianPaperEpsilon n) : ℝ) =
        Real.log (gaussianNetCardBound d L M S (gaussianPaperEpsilon n) : ℝ) := rfl
    _ ≤ 17 * ((d : ℝ) + 1) * ((k : ℝ) + 1) * Real.log (n : ℝ) := hraw'
    _ ≤ 17 * ((d : ℝ) + 1) * ((4 * C + 1) ^ d + 1) *
        gaussianPaperLogScale n ^ d * Real.log (n : ℝ) := by
      calc
        17 * ((d : ℝ) + 1) * ((k : ℝ) + 1) * Real.log (n : ℝ) =
            (17 * ((d : ℝ) + 1) * Real.log (n : ℝ)) * ((k : ℝ) + 1) := by ring
        _ ≤ (17 * ((d : ℝ) + 1) * Real.log (n : ℝ)) *
            (((4 * C + 1) ^ d + 1) * gaussianPaperLogScale n ^ d) :=
          mul_le_mul_of_nonneg_left hkOne (by positivity)
        _ = 17 * ((d : ℝ) + 1) * ((4 * C + 1) ^ d + 1) *
            gaussianPaperLogScale n ^ d * Real.log (n : ℝ) := by ring

/-- Explicit entropy coefficient at the fixed Taylor constant `256`. -/
noncomputable def gaussianPaperEntropyConstant (d : ℕ) : ℝ :=
  17 * ((d : ℝ) + 1) * ((1025 : ℝ) ^ d + 1)

/-- Displayed constant in the final Hellinger-rate theorem. -/
noncomputable def gaussianPaperRateConstant (d : ℕ) (b : ℝ) : ℝ :=
  22 + 4 * (gaussianPaperEntropyConstant d + b + 4)

/-- All non-entropy approximation terms can be absorbed in the same
`(log n / log log n)^d log n / n` rate. -/
theorem eventually_gaussianNearMLE_threshold_256_le
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      2 * gaussianNetHellingerSqError d (gaussianPaperMomentOrder 256 n)
          (gaussianPaperWeightDenominator d 256 n) S
          (gaussianPaperEpsilon n) +
        4 * (Real.log (gaussianNetCardBound d
            (gaussianPaperMomentOrder 256 n)
            (gaussianPaperWeightDenominator d 256 n) S
            (gaussianPaperEpsilon n) : ℝ) +
          (b + 2) * Real.log (n : ℝ) + 2) / n ≤
      gaussianPaperRateConstant d b * gaussianPaperLogScale n ^ d *
        Real.log (n : ℝ) / n := by
  filter_upwards [eventually_gaussianNetHellingerSqError_256_le d hS,
    eventually_log_gaussianNetCardBound_paper_le d
      (show (0 : ℝ) < 256 by norm_num) hS,
    tendsto_gaussianPaperLogScale_atTop.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    Filter.eventually_ge_atTop (1 : ℕ)] with n hnet hent hscale hlog hn
  let E := gaussianPaperEntropyConstant d
  let q := gaussianPaperLogScale n ^ d * Real.log (n : ℝ)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog' : (1 : ℝ) ≤ Real.log (n : ℝ) := by
    simpa only [Function.comp_apply] using hlog
  have hscalePow : (1 : ℝ) ≤ gaussianPaperLogScale n ^ d :=
    one_le_pow₀ hscale
  have hq : 1 ≤ q := by
    dsimp [q]
    have hmul := mul_le_mul hscalePow hlog' (by norm_num)
      (show (0 : ℝ) ≤ gaussianPaperLogScale n ^ d by positivity)
    simpa only [one_mul] using hmul
  have hent' : Real.log (gaussianNetCardBound d
      (gaussianPaperMomentOrder 256 n)
      (gaussianPaperWeightDenominator d 256 n) S
      (gaussianPaperEpsilon n) : ℝ) ≤ E * q := by
    dsimp [E, q, gaussianPaperEntropyConstant]
    norm_num at hent ⊢
    convert hent using 1 <;> ring
  have hB : (b + 2) * Real.log (n : ℝ) + 2 ≤ (b + 4) * q := by
    calc
      (b + 2) * Real.log (n : ℝ) + 2 ≤
          (b + 4) * Real.log (n : ℝ) := by nlinarith
      _ ≤ (b + 4) * q := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp [q]
        have hlog0 : 0 ≤ Real.log (n : ℝ) := le_trans zero_le_one hlog'
        have := mul_le_mul_of_nonneg_right hscalePow hlog0
        simpa only [one_mul] using this
  have hsum : Real.log (gaussianNetCardBound d
      (gaussianPaperMomentOrder 256 n)
      (gaussianPaperWeightDenominator d 256 n) S
      (gaussianPaperEpsilon n) : ℝ) +
      (b + 2) * Real.log (n : ℝ) + 2 ≤ (E + b + 4) * q := by
    calc
      Real.log (gaussianNetCardBound d
          (gaussianPaperMomentOrder 256 n)
          (gaussianPaperWeightDenominator d 256 n) S
          (gaussianPaperEpsilon n) : ℝ) +
          (b + 2) * Real.log (n : ℝ) + 2 ≤ E * q + (b + 4) * q := by
        linarith
      _ = (E + b + 4) * q := by ring
  have hnetTwo : 2 * gaussianNetHellingerSqError d
      (gaussianPaperMomentOrder 256 n)
      (gaussianPaperWeightDenominator d 256 n) S
      (gaussianPaperEpsilon n) ≤ 22 / (n : ℝ) := by
    calc
      2 * gaussianNetHellingerSqError d (gaussianPaperMomentOrder 256 n)
          (gaussianPaperWeightDenominator d 256 n) S
          (gaussianPaperEpsilon n) ≤ 2 * (11 / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hnet (by norm_num)
      _ = 22 / (n : ℝ) := by ring
  calc
    2 * gaussianNetHellingerSqError d (gaussianPaperMomentOrder 256 n)
          (gaussianPaperWeightDenominator d 256 n) S
          (gaussianPaperEpsilon n) +
        4 * (Real.log (gaussianNetCardBound d
            (gaussianPaperMomentOrder 256 n)
            (gaussianPaperWeightDenominator d 256 n) S
            (gaussianPaperEpsilon n) : ℝ) +
          (b + 2) * Real.log (n : ℝ) + 2) / n ≤
      22 / (n : ℝ) + 4 * ((E + b + 4) * q) / n := by
        exact add_le_add hnetTwo
          (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsum (by norm_num)) hnreal.le)
    _ = (22 + 4 * (E + b + 4) * q) / (n : ℝ) := by ring
    _ ≤ (22 * q + 4 * (E + b + 4) * q) / (n : ℝ) := by
      apply div_le_div_of_nonneg_right _ hnreal.le
      nlinarith
    _ = gaussianPaperRateConstant d b * gaussianPaperLogScale n ^ d *
        Real.log (n : ℝ) / n := by
      dsimp [gaussianPaperRateConstant, E, q]
      ring

/-- Polynomial form of the two failure probabilities generated by the
sample-radius and likelihood-test calibrations. -/
theorem gaussianPaper_failure_bound (d n : ℕ) {b : ℝ} (hb : 0 ≤ b)
    (hn : 1 ≤ n) :
    2 * (n : ℝ) * d * Real.exp (-gaussianPaperRadiusExponent b n) +
        Real.exp (-(b + 2) * Real.log (n : ℝ) - 1) ≤
      (2 * (d : ℝ) + 1) * (n : ℝ) ^ (-(b + 2)) := by
  let x : ℝ := n
  have hx : 0 < x := by dsimp [x]; exact_mod_cast (show 0 < n by omega)
  have hxOne : 1 ≤ x := by dsimp [x]; exact_mod_cast hn
  have hR : Real.exp (-gaussianPaperRadiusExponent b n) =
      x ^ (-(b + 4)) := by
    rw [Real.rpow_def_of_pos hx]
    unfold gaussianPaperRadiusExponent
    dsimp [x]
    congr 1
    ring
  have hB : Real.exp (-(b + 2) * Real.log (n : ℝ) - 1) =
      x ^ (-(b + 2)) * Real.exp (-1) := by
    rw [show -(b + 2) * Real.log (n : ℝ) - 1 =
        Real.log x * (-(b + 2)) + (-1) by dsimp [x]; ring,
      Real.exp_add, ← Real.rpow_def_of_pos hx]
  have hshift : x * x ^ (-(b + 4)) ≤ x ^ (-(b + 2)) := by
    calc
      x * x ^ (-(b + 4)) = x ^ (1 : ℝ) * x ^ (-(b + 4)) := by
        rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + (-(b + 4))) :=
        (Real.rpow_add hx _ _).symm
      _ = x ^ (-(b + 3)) := by congr 1 <;> ring
      _ ≤ x ^ (-(b + 2)) :=
        Real.rpow_le_rpow_of_exponent_le hxOne (by linarith)
  have hexpone : Real.exp (-1) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show (-1 : ℝ) ≤ 0 by norm_num)
  rw [hR, hB]
  calc
    2 * (n : ℝ) * d * x ^ (-(b + 4)) +
        x ^ (-(b + 2)) * Real.exp (-1) =
      (2 * (d : ℝ)) * (x * x ^ (-(b + 4))) +
        x ^ (-(b + 2)) * Real.exp (-1) := by dsimp [x]; ring
    _ ≤ (2 * (d : ℝ)) * x ^ (-(b + 2)) +
        x ^ (-(b + 2)) * 1 := by gcongr
    _ = (2 * (d : ℝ) + 1) * (n : ℝ) ^ (-(b + 2)) := by
      dsimp [x]
      ring

/-- Paper-rate specialization of the uniform compact Gaussian-mixture
near-MLE theorem.  Uniformly over every mixing law supported on `K`, every
likelihood maximizer up to additive error one has squared Hellinger loss of
order
`(log n / log log n)^d * log n / n`
outside an event of polynomially small probability. -/
theorem compactGaussianMixture_uniform_nearMLE_paper_rate
    {d : ℕ} (hd : 0 < d)
    (K : Set (Point d)) (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ Gstar : ProbabilityMeasure K,
      (Measure.pi (fun _ : Fin n ↦ volume.withDensity (fun y ↦
        ENNReal.ofReal (compactGaussianMixtureDensity Gstar y)))).real
          {x | ∃ G : ProbabilityMeasure K,
            (∑ i, Real.log (compactGaussianMixtureDensity Gstar (x i))) - 1 ≤
                ∑ i, Real.log (compactGaussianMixtureDensity G (x i)) ∧
            gaussianPaperRateConstant d b * gaussianPaperLogScale n ^ d *
                Real.log (n : ℝ) / n <
              hellingerSq volume (compactGaussianMixtureDensity G)
                (compactGaussianMixtureDensity Gstar)} ≤
        (2 * (d : ℝ) + 1) * (n : ℝ) ^ (-(b + 2)) := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gaussianMomentRelativeError_256_le_half d hS hb,
    eventually_gaussianPaper_weightSmall d (C := (256 : ℝ)) hS hb,
    eventually_gaussianNetLogError_256 d hS hb,
    eventually_gaussianNearMLE_threshold_256_le d hS hb,
    hlog.eventually_gt_atTop 0, Filter.eventually_ge_atTop (1 : ℕ)]
      with n hrelative hweight hnδ hthreshold hlogn hn
  intro Gstar
  let L := gaussianPaperMomentOrder 256 n
  let M := gaussianPaperWeightDenominator d 256 n
  let ε := gaussianPaperEpsilon n
  let R := gaussianPaperRadiusExponent b n
  let B := (b + 2) * Real.log (n : ℝ)
  let T := gaussianPaperSampleRadius d S b n
  let rate := gaussianPaperRateConstant d b * gaussianPaperLogScale n ^ d *
    Real.log (n : ℝ) / n
  have hnpos : 0 < n := by omega
  have hε : 0 < ε := by
    dsimp [ε]
    exact gaussianPaperEpsilon_pos hnpos
  have hR : 0 < R := by
    dsimp [R, gaussianPaperRadiusExponent]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hM : 0 < M := by
    dsimp [M]
    exact gaussianPaperWeightDenominator_pos d 256 hnpos
  have hrelative' : gaussianMomentRelativeError T S L ≤ 1 / 2 := by
    simpa only [T, L] using hrelative
  have hweight' : Real.exp (2 * (T * S + S ^ 2 / 2)) *
      (2 * gaussianMomentDimension d L / M) ≤ 1 / 2 := by
    simpa only [T, L, M, gaussianPaperTaylorArgument] using hweight
  have hnδ' : (n : ℝ) * gaussianNetLogError d L M T S ε ≤ 1 := by
    simpa only [T, L, M, ε] using hnδ
  have hthreshold' :
      2 * gaussianNetHellingerSqError d L M S ε +
          4 * (Real.log (gaussianNetCardBound d L M S ε : ℝ) + B + 2) / n ≤
        rate := by
    simpa only [L, M, ε, B, rate] using hthreshold
  have hmain :=
    compactGaussianMixture_uniform_nearMLE_bad_event_bound_fully_tuned
      (d := d) (L := L) (M := M) (n := n) hnpos K hKcompact hKnonempty
      hS hε hR hB hKbound hM hrelative' hweight' Gstar hnδ'
  let ν : Measure (Point d) := volume.withDensity (fun y ↦
    ENNReal.ofReal (compactGaussianMixtureDensity Gstar y))
  letI : IsProbabilityMeasure ν := IsProbabilityMeasure.mk (by
    dsimp [ν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal
        (compactGaussianMixtureDensity_integrable Gstar)
        (Filter.Eventually.of_forall fun x ↦
          (compactGaussianMixtureDensity_pos Gstar x).le),
      integral_compactGaussianMixtureDensity]
    norm_num)
  let μ : Measure (Fin n → Point d) := Measure.pi (fun _ : Fin n ↦ ν)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  let badRate : Set (Fin n → Point d) :=
    {x | ∃ G : ProbabilityMeasure K,
      (∑ i, Real.log (compactGaussianMixtureDensity Gstar (x i))) - 1 ≤
          ∑ i, Real.log (compactGaussianMixtureDensity G (x i)) ∧
      rate < hellingerSq volume (compactGaussianMixtureDensity G)
        (compactGaussianMixtureDensity Gstar)}
  let badRaw : Set (Fin n → Point d) :=
    {x | ∃ G : ProbabilityMeasure K,
      (∑ i, Real.log (compactGaussianMixtureDensity Gstar (x i))) - 1 ≤
          ∑ i, Real.log (compactGaussianMixtureDensity G (x i)) ∧
      2 * gaussianNetHellingerSqError d L M S ε +
          4 * (Real.log (gaussianNetCardBound d L M S ε : ℝ) + B + 2) / n <
        hellingerSq volume (compactGaussianMixtureDensity G)
          (compactGaussianMixtureDensity Gstar)}
  have hsubset : badRate ⊆ badRaw := by
    intro x hx
    rcases hx with ⟨G, hnear, hbad⟩
    exact ⟨G, hnear, lt_of_le_of_lt hthreshold' hbad⟩
  have hmain' : μ.real badRaw ≤
      2 * (n : ℝ) * d * Real.exp (-R) + Real.exp (-B - 1) := by
    simpa only [μ, ν, badRaw, L, M, ε, R, B, T,
      gaussianPaperSampleRadius] using hmain
  have hfailure :
      2 * (n : ℝ) * d * Real.exp (-R) + Real.exp (-B - 1) ≤
        (2 * (d : ℝ) + 1) * (n : ℝ) ^ (-(b + 2)) := by
      simpa only [R, B, neg_mul] using gaussianPaper_failure_bound d n hb hn
  change μ.real badRate ≤
    (2 * (d : ℝ) + 1) * (n : ℝ) ^ (-(b + 2))
  exact (measureReal_mono hsubset (by finiteness)).trans (hmain'.trans hfailure)

end ReweightedNPMLE
