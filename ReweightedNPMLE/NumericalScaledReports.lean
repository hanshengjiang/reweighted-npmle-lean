import ReweightedNPMLE.GeneratedNumericalData
import Mathlib.Tactic

/-! # Certified logarithms and log-scaled numerical cell statistics -/

namespace ReweightedNPMLE.NumericalStudy

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

theorem numerical_sample_size_log_certificates_valid :
    numericalSampleSizeLogCertificates.all numericalLogCertificateValid = true := by
  norm_num (config := { maxSteps := 10000000 })
    [numericalSampleSizeLogCertificates, numericalLogCertificateValid,
      numericalLogAdjustedArgument, numericalLogLowerRat, numericalLogErrorRat,
      numericalLogUnitLowerRat, numericalLogUnitErrorRat, Finset.sum_range_succ]

theorem numerical_sample_size_log_enclosure {c : NumericalLogCertificate}
    (hc : c ∈ numericalSampleSizeLogCertificates) :
    (c.lower : ℝ) ≤ Real.log (c.argument : ℝ) ∧
    Real.log (c.argument : ℝ) ≤ (c.upper : ℝ) := by
  exact numerical_log_certificate_enclosure c
    (List.all_eq_true.mp numerical_sample_size_log_certificates_valid c hc)

def numericalSampleSizeCertificate (n : ℕ) : NumericalLogCertificate :=
  let index := if n = 200 then 0 else if n = 250 then 1 else
    if n = 500 then 2 else if n = 1000 then 3 else 4
  numericalSampleSizeLogCertificates.getD index ⟨1, false, 0, 0, 0⟩

private def scaledCellLogCertified (r : Nat × ℚ × ℚ) : Bool :=
  let c := numericalSampleSizeCertificate r.1
  decide (c.argument = (r.1 : ℚ)) && numericalLogCertificateValid c

theorem numerical_scaled_cells_logs_certified :
    numericalScaledCells.all scaledCellLogCertified = true := by
  norm_num (config := { maxSteps := 10000000 })
    [numericalScaledCells, scaledCellLogCertified, numericalSampleSizeCertificate,
      numericalSampleSizeLogCertificates, numericalLogCertificateValid,
      numericalLogAdjustedArgument, numericalLogLowerRat, numericalLogErrorRat,
      numericalLogUnitLowerRat, numericalLogUnitErrorRat, Finset.sum_range_succ]

theorem numerical_scaled_cell_log_enclosure {r : Nat × ℚ × ℚ}
    (hr : r ∈ numericalScaledCells) :
    ((numericalSampleSizeCertificate r.1).lower : ℝ) ≤ Real.log (r.1 : ℝ) ∧
    Real.log (r.1 : ℝ) ≤ ((numericalSampleSizeCertificate r.1).upper : ℝ) := by
  have h := List.all_eq_true.mp numerical_scaled_cells_logs_certified r hr
  have hh : (numericalSampleSizeCertificate r.1).argument = (r.1 : ℚ) ∧
      numericalLogCertificateValid (numericalSampleSizeCertificate r.1) = true := by
    simpa only [scaledCellLogCertified, Bool.and_eq_true, decide_eq_true_eq] using h
  have hb := numerical_log_certificate_enclosure _ hh.2
  simpa only [hh.1, Rat.cast_natCast] using hb

private def scaledCellRangeCertified (r : Nat × ℚ × ℚ) : Bool :=
  let c := numericalSampleSizeCertificate r.1
  decide (0 ≤ r.2.1 ∧ 0 ≤ r.2.2 ∧
    505 / 2000 ≤ r.2.1 * c.lower ∧ r.2.1 * c.upper ≤ 1065 / 2000 ∧
    479 / 1000 ≤ r.2.2 * c.lower ∧ r.2.2 * c.upper ≤ 928 / 1000)

theorem numerical_scaled_cell_rational_range_checks :
    numericalScaledCells.all scaledCellRangeCertified = true := by
  norm_num [numericalScaledCells, scaledCellRangeCertified, numericalSampleSizeCertificate,
    numericalSampleSizeLogCertificates]

noncomputable def numericalScaledLikelihood (r : Nat × ℚ × ℚ) : ℝ :=
  (r.2.1 : ℝ) * Real.log (r.1 : ℝ)

noncomputable def numericalScaledLogfit (r : Nat × ℚ × ℚ) : ℝ :=
  (r.2.2 : ℝ) * Real.log (r.1 : ℝ)

theorem numerical_scaled_cell_real_ranges {r : Nat × ℚ × ℚ}
    (hr : r ∈ numericalScaledCells) :
    505 / 2000 ≤ numericalScaledLikelihood r ∧ numericalScaledLikelihood r ≤ 1065 / 2000 ∧
    479 / 1000 ≤ numericalScaledLogfit r ∧ numericalScaledLogfit r ≤ 928 / 1000 := by
  have h := List.all_eq_true.mp numerical_scaled_cell_rational_range_checks r hr
  have hq : 0 ≤ r.2.1 ∧ 0 ≤ r.2.2 ∧
      505 / 2000 ≤ r.2.1 * (numericalSampleSizeCertificate r.1).lower ∧
      r.2.1 * (numericalSampleSizeCertificate r.1).upper ≤ 1065 / 2000 ∧
      479 / 1000 ≤ r.2.2 * (numericalSampleSizeCertificate r.1).lower ∧
      r.2.2 * (numericalSampleSizeCertificate r.1).upper ≤ 928 / 1000 := by
    simpa only [scaledCellRangeCertified, decide_eq_true_eq] using h
  have hp1 : (0 : ℝ) ≤ r.2.1 := by exact_mod_cast hq.1
  have hp2 : (0 : ℝ) ≤ r.2.2 := by exact_mod_cast hq.2.1
  have hb := numerical_scaled_cell_log_enclosure hr
  have hl1 := mul_le_mul_of_nonneg_left hb.1 hp1
  have hu1 := mul_le_mul_of_nonneg_left hb.2 hp1
  have hl2 := mul_le_mul_of_nonneg_left hb.1 hp2
  have hu2 := mul_le_mul_of_nonneg_left hb.2 hp2
  have hbq1 : (505 : ℝ) / 2000 ≤ (r.2.1 : ℝ) * (numericalSampleSizeCertificate r.1).lower := by
    simpa using (Rat.cast_le (K := ℝ)).2 hq.2.2.1
  have hbq2 : (r.2.1 : ℝ) * (numericalSampleSizeCertificate r.1).upper ≤ (1065 : ℝ) / 2000 := by
    simpa using (Rat.cast_le (K := ℝ)).2 hq.2.2.2.1
  have hbq3 : (479 : ℝ) / 1000 ≤ (r.2.2 : ℝ) * (numericalSampleSizeCertificate r.1).lower := by
    simpa using (Rat.cast_le (K := ℝ)).2 hq.2.2.2.2.1
  have hbq4 : (r.2.2 : ℝ) * (numericalSampleSizeCertificate r.1).upper ≤ (928 : ℝ) / 1000 := by
    simpa using (Rat.cast_le (K := ℝ)).2 hq.2.2.2.2.2
  exact ⟨hbq1.trans hl1, hu1.trans hbq2, hbq3.trans hl2, hu2.trans hbq4⟩

theorem numerical_scaled_extremum_witness_rational_checks :
    let a := numericalScaledCells.getD 5 (0, 0, 0)
    let b := numericalScaledCells.getD 0 (0, 0, 0)
    a.2.1 * (numericalSampleSizeCertificate a.1).upper ≤ (507 : ℚ) / 2000 ∧
    (1063 : ℚ) / 2000 ≤ b.2.1 * (numericalSampleSizeCertificate b.1).lower ∧
    a.2.2 * (numericalSampleSizeCertificate a.1).upper ≤ (959 : ℚ) / 2000 ∧
    (1855 : ℚ) / 2000 ≤ b.2.2 * (numericalSampleSizeCertificate b.1).lower := by
  norm_num [numericalScaledCells, numericalSampleSizeCertificate, numericalSampleSizeLogCertificates]

noncomputable def numericalScaledMinimum (f : Nat × ℚ × ℚ → ℝ) : ℝ :=
  (numericalScaledCells.map f).foldr min (f (numericalScaledCells.getD 0 (0, 0, 0)))

noncomputable def numericalScaledMaximum (f : Nat × ℚ × ℚ → ℝ) : ℝ :=
  (numericalScaledCells.map f).foldr max (f (numericalScaledCells.getD 0 (0, 0, 0)))

private theorem foldr_min_lower_bound (xs : List ℝ) (L b : ℝ)
    (hb : L ≤ b) (hx : ∀ x ∈ xs, L ≤ x) : L ≤ xs.foldr min b := by
  induction xs with
  | nil => exact hb
  | cons a xs ih =>
    exact le_min (hx a (by simp)) (ih (fun x h ↦ hx x (by simp [h])))

private theorem foldr_max_upper_bound (xs : List ℝ) (U b : ℝ)
    (hb : b ≤ U) (hx : ∀ x ∈ xs, x ≤ U) : xs.foldr max b ≤ U := by
  induction xs with
  | nil => exact hb
  | cons a xs ih =>
    exact max_le (hx a (by simp)) (ih (fun x h ↦ hx x (by simp [h])))

private theorem scaled_extrema_precision_of_bounds
    (f : Nat × ℚ × ℚ → ℝ) (l u ε : ℝ)
    (hall : ∀ r ∈ numericalScaledCells, l - ε ≤ f r ∧ f r ≤ u + ε)
    (hlo : f (numericalScaledCells.getD 5 (0, 0, 0)) ≤ l + ε)
    (hhi : u - ε ≤ f (numericalScaledCells.getD 0 (0, 0, 0))) :
    |numericalScaledMinimum f - l| ≤ ε ∧ |numericalScaledMaximum f - u| ≤ ε := by
  have hm0 : numericalScaledCells.getD 0 (0, 0, 0) ∈ numericalScaledCells := by
    norm_num [numericalScaledCells]
  have hm5 : numericalScaledCells.getD 5 (0, 0, 0) ∈ numericalScaledCells := by
    norm_num [numericalScaledCells]
  have hmap0 : f (numericalScaledCells.getD 0 (0, 0, 0)) ∈ numericalScaledCells.map f :=
    List.mem_map.mpr ⟨_, hm0, rfl⟩
  have hmap5 : f (numericalScaledCells.getD 5 (0, 0, 0)) ∈ numericalScaledCells.map f :=
    List.mem_map.mpr ⟨_, hm5, rfl⟩
  have hminlo := foldr_min_lower_bound (numericalScaledCells.map f) (l - ε)
    (f (numericalScaledCells.getD 0 (0, 0, 0))) (hall _ hm0).1 (by
      intro x hx
      rcases List.mem_map.mp hx with ⟨r, hr, rfl⟩
      exact (hall r hr).1)
  have hmaxhi := foldr_max_upper_bound (numericalScaledCells.map f) (u + ε)
    (f (numericalScaledCells.getD 0 (0, 0, 0))) (hall _ hm0).2 (by
      intro x hx
      rcases List.mem_map.mp hx with ⟨r, hr, rfl⟩
      exact (hall r hr).2)
  have hminhi := List.min_le_of_le' (f (numericalScaledCells.getD 0 (0, 0, 0))) hmap5 hlo
  have hmaxlo := List.le_max_of_le' (f (numericalScaledCells.getD 0 (0, 0, 0))) hmap0 hhi
  change l - ε ≤ numericalScaledMinimum f at hminlo
  change numericalScaledMaximum f ≤ u + ε at hmaxhi
  change numericalScaledMinimum f ≤ l + ε at hminhi
  change u - ε ≤ numericalScaledMaximum f at hmaxlo
  constructor <;> rw [abs_le] <;> constructor <;> linarith

theorem numerical_scaled_likelihood_and_logfit_extrema_printed_precision :
    (|numericalScaledMinimum numericalScaledLikelihood - 253 / 1000| ≤ 1 / 2000 ∧
      |numericalScaledMaximum numericalScaledLikelihood - 532 / 1000| ≤ 1 / 2000) ∧
    (|numericalScaledMinimum numericalScaledLogfit - 479 / 1000| ≤ 1 / 2000 ∧
      |numericalScaledMaximum numericalScaledLogfit - 928 / 1000| ≤ 1 / 2000) := by
  let a := numericalScaledCells.getD 5 (0, 0, 0)
  let b := numericalScaledCells.getD 0 (0, 0, 0)
  have ha : a ∈ numericalScaledCells := by norm_num [a, numericalScaledCells]
  have hb : b ∈ numericalScaledCells := by norm_num [b, numericalScaledCells]
  have hap : (0 : ℝ) ≤ a.2.1 := by norm_num [a, numericalScaledCells]
  have haqp : (0 : ℝ) ≤ a.2.2 := by norm_num [a, numericalScaledCells]
  have hbp : (0 : ℝ) ≤ b.2.1 := by norm_num [b, numericalScaledCells]
  have hbqp : (0 : ℝ) ≤ b.2.2 := by norm_num [b, numericalScaledCells]
  have hal := numerical_scaled_cell_log_enclosure ha
  have hbl := numerical_scaled_cell_log_enclosure hb
  have hw := numerical_scaled_extremum_witness_rational_checks
  change a.2.1 * (numericalSampleSizeCertificate a.1).upper ≤ (507 : ℚ) / 2000 ∧
    (1063 : ℚ) / 2000 ≤ b.2.1 * (numericalSampleSizeCertificate b.1).lower ∧
    a.2.2 * (numericalSampleSizeCertificate a.1).upper ≤ (959 : ℚ) / 2000 ∧
    (1855 : ℚ) / 2000 ≤ b.2.2 * (numericalSampleSizeCertificate b.1).lower at hw
  have h1 : numericalScaledLikelihood a ≤ 507 / 2000 := by
    exact (mul_le_mul_of_nonneg_left hal.2 hap).trans
      (by simpa using (Rat.cast_le (K := ℝ)).2 hw.1)
  have h2 : 1063 / 2000 ≤ numericalScaledLikelihood b := by
    calc
      (1063 : ℝ) / 2000 ≤ (b.2.1 : ℝ) * (numericalSampleSizeCertificate b.1).lower := by
        simpa using (Rat.cast_le (K := ℝ)).2 hw.2.1
      _ ≤ numericalScaledLikelihood b := mul_le_mul_of_nonneg_left hbl.1 hbp
  have h3 : numericalScaledLogfit a ≤ 959 / 2000 := by
    exact (mul_le_mul_of_nonneg_left hal.2 haqp).trans
      (by simpa using (Rat.cast_le (K := ℝ)).2 hw.2.2.1)
  have h4 : 1855 / 2000 ≤ numericalScaledLogfit b := by
    calc
      (1855 : ℝ) / 2000 ≤ (b.2.2 : ℝ) * (numericalSampleSizeCertificate b.1).lower := by
        simpa using (Rat.cast_le (K := ℝ)).2 hw.2.2.2
      _ ≤ numericalScaledLogfit b := mul_le_mul_of_nonneg_left hbl.1 hbqp
  constructor
  · apply scaled_extrema_precision_of_bounds
    · intro r hr
      have h := numerical_scaled_cell_real_ranges hr
      constructor <;> linarith [h.1, h.2.1]
    · change numericalScaledLikelihood a ≤ _
      linarith
    · change _ ≤ numericalScaledLikelihood b
      linarith
  · apply scaled_extrema_precision_of_bounds
    · intro r hr
      have h := numerical_scaled_cell_real_ranges hr
      constructor <;> linarith [h.2.2.1, h.2.2.2]
    · change numericalScaledLogfit a ≤ _
      linarith
    · change _ ≤ numericalScaledLogfit b
      linarith

/-- The scaled likelihood maximum rounds to `0.532` but exceeds it literally. -/
theorem numerical_scaled_likelihood_literal_upper_bound_refuted :
    (532 : ℝ) / 1000 < numericalScaledLikelihood (numericalScaledCells.getD 0 (0, 0, 0)) := by
  let b := numericalScaledCells.getD 0 (0, 0, 0)
  have hb : b ∈ numericalScaledCells := by norm_num [b, numericalScaledCells]
  have hp : (0 : ℝ) ≤ b.2.1 := by norm_num [b, numericalScaledCells]
  have hq : (532 : ℚ) / 1000 < b.2.1 * (numericalSampleSizeCertificate b.1).lower := by
    norm_num [b, numericalScaledCells, numericalSampleSizeCertificate, numericalSampleSizeLogCertificates]
  have hh : (532 : ℝ) / 1000 < (b.2.1 : ℝ) * (numericalSampleSizeCertificate b.1).lower := by
    simpa using (Rat.cast_lt (K := ℝ)).2 hq
  exact hh.trans_le (mul_le_mul_of_nonneg_left (numerical_scaled_cell_log_enclosure hb).1 hp)

end ReweightedNPMLE.NumericalStudy
