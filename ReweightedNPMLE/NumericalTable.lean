import ReweightedNPMLE.GeneratedNumericalData
import Mathlib.Tactic

/-! # Exact source-data certificates for the printed numerical table

The 48 mean entries are compared with exact rational CSV means, and the 42
parenthesized standard errors with the exact squared Monte Carlo standard
errors. Every comparison uses half the last displayed decimal unit. This
certifies reporting precision without asserting that rounded numbers are
literal bounds, and without a floating-point oracle or `native_decide`.
-/

open scoped Topology

namespace ReweightedNPMLE.NumericalStudy

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def meanEntryCertified (r : String × ℚ × ℚ × ℚ) : Bool :=
  decide (|r.2.1 - r.2.2.1| ≤ r.2.2.2)

private def seEntryCertified (r : String × ℚ × ℚ × ℚ) : Bool :=
  decide (0 ≤ r.2.2.1 - r.2.2.2 ∧
    (r.2.2.1 - r.2.2.2) ^ 2 ≤ r.2.1 ∧ r.2.1 ≤ (r.2.2.1 + r.2.2.2) ^ 2)

def numericalSampleMean (xs : List ℚ) : ℚ := xs.sum / xs.length

def numericalSampleStandardErrorSq (xs : List ℚ) : ℚ :=
  (xs.map (fun x ↦ (x - numericalSampleMean xs) ^ 2)).sum /
    ((xs.length : ℚ) * ((xs.length : ℚ) - 1))

private def meanMatchesRawSample
    (r : (String × List ℚ) × (String × ℚ × ℚ × ℚ)) : Bool :=
  decide (r.1.1 = r.2.1 ∧ numericalSampleMean r.1.2 = r.2.2.1)

private def seMatchesRawSample (r : String × ℚ × ℚ × ℚ) : Bool :=
  match tableRawSamples.find? (fun t ↦ decide (t.1 = r.1)) with
  | none => false
  | some t => decide (numericalSampleStandardErrorSq t.2 = r.2.1)

theorem numerical_table_raw_sample_cell_count : tableRawSamples.length = 48 := by decide

theorem numerical_table_all_means_recomputed_from_raw_samples :
    (tableRawSamples.zip tableMeanCertificates).all meanMatchesRawSample = true := by
  norm_num [tableRawSamples, tableMeanCertificates, meanMatchesRawSample,
    numericalSampleMean]

theorem numerical_table_all_standard_errors_recomputed_from_raw_samples :
    tableStandardErrorSqCertificates.all seMatchesRawSample = true := by
  simp [tableStandardErrorSqCertificates, seMatchesRawSample, tableRawSamples]
  norm_num [numericalSampleStandardErrorSq, numericalSampleMean]

theorem numerical_table_entry_counts :
    tableMeanCertificates.length = 48 ∧ tableStandardErrorSqCertificates.length = 42 := by
  decide

theorem numerical_table_all_means_certified :
    tableMeanCertificates.all meanEntryCertified = true := by
  norm_num [tableMeanCertificates, meanEntryCertified]

theorem numerical_table_all_standard_errors_sq_certified :
    tableStandardErrorSqCertificates.all seEntryCertified = true := by
  norm_num [tableStandardErrorSqCertificates, seEntryCertified]

/-- Squared interval checks certify the actual square-root standard error. -/
theorem sqrt_standard_error_rounding_of_sq_bounds
    {v s ε : ℝ} (hlo : 0 ≤ s - ε) (hl : (s - ε) ^ 2 ≤ v)
    (hu : v ≤ (s + ε) ^ 2) (hε : 0 ≤ ε) : |Real.sqrt v - s| ≤ ε := by
  have hv : 0 ≤ v := (sq_nonneg _).trans hl
  have hupper : Real.sqrt v ≤ s + ε := by
    have hs : 0 ≤ s + ε := by linarith
    simpa only [Real.sqrt_sq hs] using Real.sqrt_le_sqrt hu
  have hlower : s - ε ≤ Real.sqrt v := Real.le_sqrt_of_sq_le hl
  rw [abs_le]
  constructor <;> linarith

theorem numerical_table_mean_precision {r : String × ℚ × ℚ × ℚ}
    (hr : r ∈ tableMeanCertificates) :
    |r.2.1 - r.2.2.1| ≤ r.2.2.2 := by
  have h := List.all_eq_true.mp numerical_table_all_means_certified r hr
  simpa only [meanEntryCertified, decide_eq_true_eq] using h

theorem numerical_table_standard_error_precision {r : String × ℚ × ℚ × ℚ}
    (hr : r ∈ tableStandardErrorSqCertificates) :
    |Real.sqrt (r.2.1 : ℝ) - (r.2.2.1 : ℝ)| ≤ (r.2.2.2 : ℝ) := by
  have h := List.all_eq_true.mp numerical_table_all_standard_errors_sq_certified r hr
  have hq : 0 ≤ r.2.2.1 - r.2.2.2 ∧
      (r.2.2.1 - r.2.2.2) ^ 2 ≤ r.2.1 ∧ r.2.1 ≤ (r.2.2.1 + r.2.2.2) ^ 2 := by
    simpa only [seEntryCertified, decide_eq_true_eq] using h
  have hε : 0 ≤ r.2.2.2 := by
    have hEntries : tableStandardErrorSqCertificates.all (fun t ↦ decide (0 ≤ t.2.2.2)) = true := by
      norm_num [tableStandardErrorSqCertificates]
    simpa only [decide_eq_true_eq] using List.all_eq_true.mp hEntries r hr
  apply sqrt_standard_error_rounding_of_sq_bounds
  · exact_mod_cast hq.1
  · exact_mod_cast hq.2.1
  · exact_mod_cast hq.2.2
  · exact_mod_cast hε

end ReweightedNPMLE.NumericalStudy
