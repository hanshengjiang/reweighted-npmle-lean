import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! # Kernel-checked logarithm enclosures for numerical reports

Range reduction by powers of two makes the atanh-series logarithm bounds
rapidly convergent. All endpoints are finite arithmetic expressions; no
floating-point logarithm is trusted by the proofs.
-/

open scoped BigOperators

namespace ReweightedNPMLE.NumericalStudy

def numericalLogUnitLowerRat (q : ℚ) (N : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range N,
    ((q - 1) / (q + 1)) ^ (2 * i + 1) / (2 * i + 1)

def numericalLogUnitErrorRat (q : ℚ) (N : ℕ) : ℚ :=
  2 * ((q - 1) / (q + 1)) ^ (2 * N + 1) /
    (1 - ((q - 1) / (q + 1)) ^ 2)

noncomputable def numericalLogUnitLower (q : ℝ) (N : ℕ) : ℝ :=
  2 * ∑ i ∈ Finset.range N,
    ((q - 1) / (q + 1)) ^ (2 * i + 1) / (2 * i + 1)

noncomputable def numericalLogUnitError (q : ℝ) (N : ℕ) : ℝ :=
  2 * ((q - 1) / (q + 1)) ^ (2 * N + 1) /
    (1 - ((q - 1) / (q + 1)) ^ 2)

theorem numerical_log_unit_enclosure {q : ℝ} (hq : 1 ≤ q) (N : ℕ) :
    numericalLogUnitLower q N ≤ Real.log q ∧
    Real.log q ≤ numericalLogUnitLower q N + numericalLogUnitError q N := by
  let y := (q - 1) / (q + 1)
  have hden : 0 < q + 1 := by linarith
  have hy0 : 0 ≤ y := div_nonneg (sub_nonneg.mpr hq) hden.le
  have hy1 : y < 1 := (div_lt_one hden).mpr (by linarith)
  have hyden : 1 - y ≠ 0 := by linarith
  have heq : (1 + y) / (1 - y) = q := by
    dsimp only [y] at *
    field_simp [hden.ne']
    <;> ring
  have hl := Real.sum_range_le_log_div hy0 hy1 N
  have hu := Real.log_div_le_sum_range_add hy0 hy1 N
  rw [heq] at hl hu
  dsimp only [numericalLogUnitLower, numericalLogUnitError]
  dsimp only [y] at hl hu
  constructor
  · linarith
  · rw [mul_div_assoc]
    linarith

noncomputable def numericalLogLower (q : ℝ) (k N : ℕ) : ℝ :=
  k * numericalLogUnitLower 2 N + numericalLogUnitLower (q / 2 ^ k) N

noncomputable def numericalLogError (q : ℝ) (k N : ℕ) : ℝ :=
  k * numericalLogUnitError 2 N + numericalLogUnitError (q / 2 ^ k) N

def numericalLogLowerRat (q : ℚ) (k N : ℕ) : ℚ :=
  k * numericalLogUnitLowerRat 2 N + numericalLogUnitLowerRat (q / 2 ^ k) N

def numericalLogErrorRat (q : ℚ) (k N : ℕ) : ℚ :=
  k * numericalLogUnitErrorRat 2 N + numericalLogUnitErrorRat (q / 2 ^ k) N

@[simp] theorem numericalLogUnitLowerRat_cast (q : ℚ) (N : ℕ) :
    (numericalLogUnitLowerRat q N : ℝ) = numericalLogUnitLower q N := by
  simp [numericalLogUnitLowerRat, numericalLogUnitLower]

@[simp] theorem numericalLogUnitErrorRat_cast (q : ℚ) (N : ℕ) :
    (numericalLogUnitErrorRat q N : ℝ) = numericalLogUnitError q N := by
  simp [numericalLogUnitErrorRat, numericalLogUnitError]

@[simp] theorem numericalLogLowerRat_cast (q : ℚ) (k N : ℕ) :
    (numericalLogLowerRat q k N : ℝ) = numericalLogLower q k N := by
  simp [numericalLogLowerRat, numericalLogLower]

@[simp] theorem numericalLogErrorRat_cast (q : ℚ) (k N : ℕ) :
    (numericalLogErrorRat q k N : ℝ) = numericalLogError q k N := by
  simp [numericalLogErrorRat, numericalLogError]

theorem numerical_log_power_two_enclosure {q : ℝ} (k N : ℕ)
    (hq : 2 ^ k ≤ q) :
    numericalLogLower q k N ≤ Real.log q ∧
    Real.log q ≤ numericalLogLower q k N + numericalLogError q k N := by
  have hp : 0 < (2 : ℝ) ^ k := by positivity
  have hqpos : 0 < q := hp.trans_le hq
  have hunit : 1 ≤ q / 2 ^ k := (le_div_iff₀ hp).mpr (by simpa using hq)
  have htwo := numerical_log_unit_enclosure (q := 2) (by norm_num) N
  have hx := numerical_log_unit_enclosure hunit N
  have heq : Real.log q = k * Real.log 2 + Real.log (q / 2 ^ k) := by
    rw [Real.log_div hqpos.ne' hp.ne', Real.log_pow]
    ring
  rw [heq]
  dsimp only [numericalLogLower, numericalLogError]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left htwo.1 (Nat.cast_nonneg k : (0 : ℝ) ≤ k),
    mul_le_mul_of_nonneg_left htwo.2 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

structure NumericalLogCertificate where
  argument : ℚ
  inverse : Bool
  exponent : Nat
  lower : ℚ
  upper : ℚ

def numericalLogAdjustedArgument (c : NumericalLogCertificate) : ℚ :=
  if c.inverse then c.argument⁻¹ else c.argument

def numericalLogCertificateValid (c : NumericalLogCertificate) : Bool :=
  let q := numericalLogAdjustedArgument c
  let l := numericalLogLowerRat q c.exponent 12
  let e := numericalLogErrorRat q c.exponent 12
  decide (0 < c.argument ∧ 2 ^ c.exponent ≤ q ∧
    if c.inverse then c.lower ≤ -(l + e) ∧ -l ≤ c.upper
    else c.lower ≤ l ∧ l + e ≤ c.upper)

theorem numerical_log_certificate_enclosure (c : NumericalLogCertificate)
    (hc : numericalLogCertificateValid c = true) :
    (c.lower : ℝ) ≤ Real.log (c.argument : ℝ) ∧
    Real.log (c.argument : ℝ) ≤ (c.upper : ℝ) := by
  have h : 0 < c.argument ∧ 2 ^ c.exponent ≤ numericalLogAdjustedArgument c ∧
      if c.inverse then
        c.lower ≤ -(numericalLogLowerRat (numericalLogAdjustedArgument c) c.exponent 12 +
          numericalLogErrorRat (numericalLogAdjustedArgument c) c.exponent 12) ∧
        -numericalLogLowerRat (numericalLogAdjustedArgument c) c.exponent 12 ≤ c.upper
      else
        c.lower ≤ numericalLogLowerRat (numericalLogAdjustedArgument c) c.exponent 12 ∧
        numericalLogLowerRat (numericalLogAdjustedArgument c) c.exponent 12 +
          numericalLogErrorRat (numericalLogAdjustedArgument c) c.exponent 12 ≤ c.upper := by
    simpa only [numericalLogCertificateValid, decide_eq_true_eq] using hc
  have hscale : (2 : ℝ) ^ c.exponent ≤ (numericalLogAdjustedArgument c : ℝ) := by
    exact_mod_cast h.2.1
  have hb := numerical_log_power_two_enclosure c.exponent 12 hscale
  cases hi : c.inverse
  · simp [numericalLogAdjustedArgument, hi] at h hb
    have hlo : (c.lower : ℝ) ≤ numericalLogLower c.argument c.exponent 12 := by
      have hh : (c.lower : ℝ) ≤ (numericalLogLowerRat c.argument c.exponent 12 : ℝ) := by
        exact_mod_cast h.2.2.1
      simpa only [numericalLogLowerRat_cast] using hh
    have hup : numericalLogLower c.argument c.exponent 12 +
        numericalLogError c.argument c.exponent 12 ≤ (c.upper : ℝ) := by
      have hh : ((numericalLogLowerRat c.argument c.exponent 12 +
          numericalLogErrorRat c.argument c.exponent 12 : ℚ) : ℝ) ≤ (c.upper : ℝ) := by
        exact_mod_cast h.2.2.2
      simpa using hh
    exact ⟨hlo.trans hb.1, hb.2.trans hup⟩
  · simp [numericalLogAdjustedArgument, hi] at h hb
    have hlo : (c.lower : ℝ) ≤
        -(numericalLogLower (c.argument⁻¹ : ℚ) c.exponent 12 +
          numericalLogError (c.argument⁻¹ : ℚ) c.exponent 12) := by
      have hh : (c.lower : ℝ) ≤ ((-(numericalLogLowerRat c.argument⁻¹ c.exponent 12 +
          numericalLogErrorRat c.argument⁻¹ c.exponent 12) : ℚ) : ℝ) := by
        have hq : c.lower ≤ -(numericalLogLowerRat c.argument⁻¹ c.exponent 12 +
            numericalLogErrorRat c.argument⁻¹ c.exponent 12) := by
          linarith [h.2.2.1]
        exact_mod_cast hq
      simpa using hh
    have hup : -numericalLogLower (c.argument⁻¹ : ℚ) c.exponent 12 ≤ (c.upper : ℝ) := by
      have hh : ((-numericalLogLowerRat c.argument⁻¹ c.exponent 12 : ℚ) : ℝ) ≤
          (c.upper : ℝ) := by
        exact_mod_cast h.2.2.2
      simpa using hh
    simp only [Rat.cast_inv] at hlo hup
    constructor <;> linarith

end ReweightedNPMLE.NumericalStudy
