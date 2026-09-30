import ReweightedNPMLE.GeneratedNumericalSummarySamples
import ReweightedNPMLE.NumericalReports
import ReweightedNPMLE.NumericalScaledReports
import ReweightedNPMLE.NumericalStudy
import ReweightedNPMLE.NumericalRealSummaryArithmetic

/-! # Whole-design summaries recomputed from raw Monte Carlo draws

The source artifact contains all 920 paired replications, not precomputed
means. The equalities below connect their arithmetic to the reporting and
log-scaled certificates. They certify reports about recorded data, not the
accuracy of floating-point density integration or optimization.
-/

namespace ReweightedNPMLE.NumericalStudy

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def numericalSummaryInputLengths (c : NumericalSummaryCell) : List Nat :=
  [c.ordinaryRisk.length, c.balancedRisk.length, c.tinyRisk.length, c.bbRisk.length,
   c.ordinarySupport.length, c.balancedSupport.length, c.tinySupport.length,
   c.bbSupport.length, c.balancedHellinger.length, c.tinyHellinger.length,
   c.balancedGap.length, c.bbGap.length, c.balancedLogfit.length]

theorem numerical_summary_raw_cell_and_replication_counts :
    SummaryData.cells.length = 11 ∧
      (SummaryData.cells.map (fun c ↦ c.replications.length)).sum = 920 := by
  norm_num [SummaryData.cells]

theorem numerical_summary_raw_design_matches :
    SummaryData.cells.map (fun c ↦
      (c.scenario, c.dimension, c.sampleSize, c.replications.length)) =
        numericalDesignCounts := by
  norm_num [SummaryData.cells, numericalDesignCounts]

theorem numerical_summary_all_replications_and_lengths_checked :
    SummaryData.cells.all (fun c ↦
      decide (c.replications = List.range c.replications.length) &&
        (numericalSummaryInputLengths c).all
          (fun n ↦ decide (n = c.replications.length))) = true := by
  norm_num [SummaryData.cells, numericalSummaryInputLengths] <;> decide

def numericalSummaryBalancedRiskRatio (c : NumericalSummaryCell) : ℚ :=
  numericalSampleMean c.balancedRisk / numericalSampleMean c.ordinaryRisk

def numericalSummaryTinyRiskRatio (c : NumericalSummaryCell) : ℚ :=
  numericalSampleMean c.tinyRisk / numericalSampleMean c.ordinaryRisk

def numericalSummaryBBRiskRatio (c : NumericalSummaryCell) : ℚ :=
  numericalSampleMean c.bbRisk / numericalSampleMean c.ordinaryRisk

def numericalSummarySupportDifference (c : NumericalSummaryCell) : ℚ :=
  numericalSampleMean (c.balancedSupport.map (fun n ↦ (n : ℚ))) -
    numericalSampleMean (c.ordinarySupport.map (fun n ↦ (n : ℚ)))

theorem numerical_summary_ordinary_risk_means_positive :
    SummaryData.cells.all (fun c ↦ decide (0 < numericalSampleMean c.ordinaryRisk)) =
      true := by
  norm_num [SummaryData.cells, numericalSampleMean]

theorem numerical_summary_balanced_risk_ratios_recomputed :
    SummaryData.cells.map numericalSummaryBalancedRiskRatio = balancedRiskRatios := by
  norm_num [SummaryData.cells, numericalSummaryBalancedRiskRatio,
    numericalSampleMean, balancedRiskRatios]

theorem numerical_summary_tiny_risk_ratios_recomputed :
    SummaryData.cells.map numericalSummaryTinyRiskRatio = tinyRiskRatios := by
  norm_num [SummaryData.cells, numericalSummaryTinyRiskRatio,
    numericalSampleMean, tinyRiskRatios]

theorem numerical_summary_bb_risk_ratios_recomputed :
    SummaryData.cells.map numericalSummaryBBRiskRatio = bbRiskRatios := by
  norm_num [SummaryData.cells, numericalSummaryBBRiskRatio,
    numericalSampleMean, bbRiskRatios]

theorem numerical_summary_support_differences_recomputed :
    SummaryData.cells.map numericalSummarySupportDifference =
      balancedMeanSupportDifferences := by
  norm_num [SummaryData.cells, numericalSummarySupportDifference,
    numericalSampleMean, balancedMeanSupportDifferences]

theorem numerical_summary_balanced_hellinger_means_recomputed :
    SummaryData.cells.map (fun c ↦ numericalSampleMean c.balancedHellinger) =
      balancedMeanHellingerToOrdinary := by
  norm_num [SummaryData.cells, numericalSampleMean, balancedMeanHellingerToOrdinary]

theorem numerical_summary_tiny_hellinger_means_recomputed :
    SummaryData.cells.map (fun c ↦ numericalSampleMean c.tinyHellinger) =
      tinyMeanHellingerToOrdinary := by
  norm_num [SummaryData.cells, numericalSampleMean, tinyMeanHellingerToOrdinary]

theorem numerical_summary_balanced_likelihood_means_recomputed :
    SummaryData.cells.map (fun c ↦ numericalSampleMean c.balancedGap) =
      balancedMeanOrdinaryLoglikGap := by
  norm_num [SummaryData.cells, numericalSampleMean, balancedMeanOrdinaryLoglikGap]

theorem numerical_summary_bb_likelihood_means_recomputed :
    SummaryData.cells.map (fun c ↦ numericalSampleMean c.bbGap) =
      bbMeanOrdinaryLoglikGap := by
  norm_num [SummaryData.cells, numericalSampleMean, bbMeanOrdinaryLoglikGap]

theorem numerical_summary_logfit_means_recomputed :
    SummaryData.cells.map (fun c ↦ numericalSampleMean c.balancedLogfit) =
      balancedMeanLogfitSqSum := by
  norm_num [SummaryData.cells, numericalSampleMean, balancedMeanLogfitSqSum]

def numericalSummarySupportTriples (c : NumericalSummaryCell) : List (Nat × Nat × Nat) :=
  c.ordinarySupport.zip (c.balancedSupport.zip c.tinySupport)

theorem numerical_summary_support_pairs_recomputed :
    (SummaryData.cells.map numericalSummarySupportTriples).flatten = supportTriples := by
  norm_num [SummaryData.cells, numericalSummarySupportTriples, supportTriples]

theorem numerical_summary_raw_tiny_same_support_all :
    (SummaryData.cells.map numericalSummarySupportTriples).flatten.all
      (fun r ↦ r.1 = r.2.2) = true := by
  rw [numerical_summary_support_pairs_recomputed]
  exact tiny_same_support_all

theorem numerical_summary_raw_balanced_same_support_count :
    ((SummaryData.cells.map numericalSummarySupportTriples).flatten.filter
      (fun r ↦ r.1 = r.2.1)).length = 831 := by
  rw [numerical_summary_support_pairs_recomputed]
  exact balanced_same_support_count

/-- The exact same printed ranges, now with samples computed from raw draws. -/
def numericalRawSummaryRangeReports : List NumericalRangeReport :=
  [⟨"balanced risk ratio", SummaryData.cells.map numericalSummaryBalancedRiskRatio,
      1001 / 1000, 1020 / 1000, 1 / 2000, 1 / 2000⟩,
   ⟨"tiny risk ratio", SummaryData.cells.map numericalSummaryTinyRiskRatio,
      999985 / 1000000, 1000018 / 1000000, 1 / 2000000, 1 / 2000000⟩,
   ⟨"BB risk ratio", SummaryData.cells.map numericalSummaryBBRiskRatio,
      160 / 100, 219 / 100, 1 / 200, 1 / 200⟩,
   ⟨"balanced H2 to ordinary",
      SummaryData.cells.map (fun c ↦ numericalSampleMean c.balancedHellinger),
      831 / 100000000, 176 / 1000000, 1 / 200000000, 1 / 2000000⟩,
   ⟨"tiny H2 to ordinary",
      SummaryData.cells.map (fun c ↦ numericalSampleMean c.tinyHellinger),
      143 / 1000000000000000, 960 / 1000000000000,
      1 / 2000000000000000, 1 / 2000000000000⟩,
   ⟨"balanced likelihood loss",
      SummaryData.cells.map (fun c ↦ numericalSampleMean c.balancedGap),
      345 / 10000, 964 / 10000, 1 / 20000, 1 / 20000⟩,
   ⟨"BB likelihood loss", SummaryData.cells.map (fun c ↦ numericalSampleMean c.bbGap),
      214 / 100, 786 / 100, 1 / 200, 1 / 200⟩,
   ⟨"balanced support difference", SummaryData.cells.map numericalSummarySupportDifference,
      -125 / 1000, 25 / 1000, 0, 0⟩]

theorem numerical_summary_raw_range_reports_match :
    numericalRawSummaryRangeReports = numericalRangeReports := by
  simp only [numericalRawSummaryRangeReports,
    numerical_summary_balanced_risk_ratios_recomputed,
    numerical_summary_tiny_risk_ratios_recomputed,
    numerical_summary_bb_risk_ratios_recomputed,
    numerical_summary_support_differences_recomputed,
    numerical_summary_balanced_hellinger_means_recomputed,
    numerical_summary_tiny_hellinger_means_recomputed,
    numerical_summary_balanced_likelihood_means_recomputed,
    numerical_summary_bb_likelihood_means_recomputed]
  norm_num [numericalRangeReports]

theorem numerical_summary_raw_range_extrema_printed_precision {r : NumericalRangeReport}
    (hr : r ∈ numericalRawSummaryRangeReports) :
    |numericalSampleMinimum r.samples - r.lower| ≤ r.lowerTolerance ∧
      |numericalSampleMaximum r.samples - r.upper| ≤ r.upperTolerance := by
  exact numerical_range_extrema_precision
    (numerical_summary_raw_range_reports_match ▸ hr)

theorem numerical_summary_raw_literal_range_results :
    numericalRawSummaryRangeReports.map
      (fun r ↦ r.samples.all (fun x ↦ decide (r.lower ≤ x ∧ x ≤ r.upper))) =
        [false, false, false, false, true, false, false, true] := by
  rw [numerical_summary_raw_range_reports_match]
  exact numerical_range_literal_interpretation_results

theorem numerical_summary_raw_balanced_average_risk_ratio_precision :
    |numericalSampleMean (SummaryData.cells.map numericalSummaryBalancedRiskRatio) -
      (1013 : ℚ) / 1000| ≤ 1 / 2000 := by
  rw [numerical_summary_balanced_risk_ratios_recomputed]
  exact balanced_average_risk_ratio_printed_precision

def numericalRawSummaryScaledCells : List (Nat × ℚ × ℚ) :=
  SummaryData.cells.map (fun c ↦
    (c.sampleSize, numericalSampleMean c.balancedGap,
      numericalSampleMean c.balancedLogfit))

theorem numerical_summary_raw_scaled_cells_recomputed :
    numericalRawSummaryScaledCells = numericalScaledCells := by
  norm_num [numericalRawSummaryScaledCells, SummaryData.cells, numericalSampleMean,
    numericalScaledCells]

theorem numerical_summary_actual_real_risk_ratios (c : NumericalSummaryCell) :
    numericalRealSampleMean c.balancedRisk / numericalRealSampleMean c.ordinaryRisk =
      (numericalSummaryBalancedRiskRatio c : ℝ) ∧
    numericalRealSampleMean c.tinyRisk / numericalRealSampleMean c.ordinaryRisk =
      (numericalSummaryTinyRiskRatio c : ℝ) ∧
    numericalRealSampleMean c.bbRisk / numericalRealSampleMean c.ordinaryRisk =
      (numericalSummaryBBRiskRatio c : ℝ) := by
  simp [numerical_real_sample_mean_eq_cast, numericalSummaryBalancedRiskRatio,
    numericalSummaryTinyRiskRatio, numericalSummaryBBRiskRatio]

theorem numerical_summary_actual_real_scaled_ranges {c : NumericalSummaryCell}
    (hc : c ∈ SummaryData.cells) :
    505 / 2000 ≤ numericalRealSampleMean c.balancedGap * Real.log (c.sampleSize : ℝ) ∧
      numericalRealSampleMean c.balancedGap * Real.log (c.sampleSize : ℝ) ≤ 1065 / 2000 ∧
    479 / 1000 ≤ numericalRealSampleMean c.balancedLogfit * Real.log (c.sampleSize : ℝ) ∧
      numericalRealSampleMean c.balancedLogfit * Real.log (c.sampleSize : ℝ) ≤ 928 / 1000 := by
  have hm : (c.sampleSize, numericalSampleMean c.balancedGap,
      numericalSampleMean c.balancedLogfit) ∈ numericalScaledCells := by
    rw [← numerical_summary_raw_scaled_cells_recomputed]
    exact List.mem_map.mpr ⟨c, hc, rfl⟩
  simpa [numericalScaledLikelihood, numericalScaledLogfit,
    numerical_real_sample_mean_eq_cast] using numerical_scaled_cell_real_ranges hm

/-- The abstract's 2.1 percent comparison concerns ratios of cell means. -/
theorem numerical_summary_actual_balanced_risk_within_2p1_percent
    {c : NumericalSummaryCell} (hc : c ∈ SummaryData.cells) :
    |numericalRealSampleMean c.balancedRisk /
      numericalRealSampleMean c.ordinaryRisk - 1| ≤ 21 / 1000 := by
  have hm : numericalSummaryBalancedRiskRatio c ∈ balancedRiskRatios := by
    rw [← numerical_summary_balanced_risk_ratios_recomputed]
    exact List.mem_map.mpr ⟨c, hc, rfl⟩
  have h := List.all_eq_true.mp balanced_risk_ratio_range_certified _ hm
  change decide (1 ≤ numericalSummaryBalancedRiskRatio c ∧
    numericalSummaryBalancedRiskRatio c ≤ 1021 / 1000) = true at h
  have hq : 1 ≤ numericalSummaryBalancedRiskRatio c ∧
      numericalSummaryBalancedRiskRatio c ≤ 1021 / 1000 := by
    simpa using h
  rw [(numerical_summary_actual_real_risk_ratios c).1]
  exact numerical_real_ratio_within_2p1_percent hq.1 hq.2

noncomputable def numericalRawSummaryScaledMinimum
    (f : Nat × ℚ × ℚ → ℝ) : ℝ :=
  (numericalRawSummaryScaledCells.map f).foldr min
    (f (numericalRawSummaryScaledCells.getD 0 (0, 0, 0)))

noncomputable def numericalRawSummaryScaledMaximum
    (f : Nat × ℚ × ℚ → ℝ) : ℝ :=
  (numericalRawSummaryScaledCells.map f).foldr max
    (f (numericalRawSummaryScaledCells.getD 0 (0, 0, 0)))

theorem numerical_summary_raw_scaled_extrema_printed_precision :
    (|numericalRawSummaryScaledMinimum numericalScaledLikelihood - 253 / 1000| ≤ 1 / 2000 ∧
      |numericalRawSummaryScaledMaximum numericalScaledLikelihood - 532 / 1000| ≤ 1 / 2000) ∧
    (|numericalRawSummaryScaledMinimum numericalScaledLogfit - 479 / 1000| ≤ 1 / 2000 ∧
      |numericalRawSummaryScaledMaximum numericalScaledLogfit - 928 / 1000| ≤ 1 / 2000) := by
  simpa only [numericalRawSummaryScaledMinimum, numericalRawSummaryScaledMaximum,
    numerical_summary_raw_scaled_cells_recomputed, numericalScaledMinimum,
    numericalScaledMaximum] using
      numerical_scaled_likelihood_and_logfit_extrema_printed_precision

end ReweightedNPMLE.NumericalStudy
