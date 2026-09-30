import ReweightedNPMLE.NumericalTable

/-! # Exact reporting-precision and path-quantile certificates

Rounded extrema are certified as rounded extrema, not as literal interval
bounds. The failed literal interpretations are also explicitly checked.
Path quantiles use the linear interpolation convention of the study script.
Their sorted samples are checked against raw CSV samples by permutations of
all 30 draw indices; ordering and every displayed quantile are verified in Lean.
-/

namespace ReweightedNPMLE.NumericalStudy

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def numericalSampleMinimum (xs : List ℚ) : ℚ := xs.foldr min (xs.headD 0)

def numericalSampleMaximum (xs : List ℚ) : ℚ := xs.foldr max (xs.headD 0)

private def rangeReportRounded (r : NumericalRangeReport) : Bool :=
  decide (|numericalSampleMinimum r.samples - r.lower| ≤ r.lowerTolerance ∧
    |numericalSampleMaximum r.samples - r.upper| ≤ r.upperTolerance)

private def rangeReportLiteral (r : NumericalRangeReport) : Bool :=
  r.samples.all (fun x ↦ decide (r.lower ≤ x ∧ x ≤ r.upper))

theorem numerical_range_report_count : numericalRangeReports.length = 8 := by decide

theorem numerical_range_all_rounded_extrema_certified :
    numericalRangeReports.all rangeReportRounded = true := by
  norm_num [numericalRangeReports, rangeReportRounded, numericalSampleMinimum,
    numericalSampleMaximum, balancedRiskRatios, tinyRiskRatios, bbRiskRatios,
    balancedMeanHellingerToOrdinary, tinyMeanHellingerToOrdinary,
    balancedMeanOrdinaryLoglikGap, bbMeanOrdinaryLoglikGap,
    balancedMeanSupportDifferences, List.foldr, min_def, max_def]

/-- Six printed ranges are not literal bounds. The tiny H² and support
difference ranges are literal bounds. The order is the source report order. -/
theorem numerical_range_literal_interpretation_results :
    numericalRangeReports.map rangeReportLiteral =
      [false, false, false, false, true, false, false, true] := by
  norm_num [numericalRangeReports, rangeReportLiteral, balancedRiskRatios,
    tinyRiskRatios, bbRiskRatios, balancedMeanHellingerToOrdinary,
    tinyMeanHellingerToOrdinary, balancedMeanOrdinaryLoglikGap,
    bbMeanOrdinaryLoglikGap, balancedMeanSupportDifferences]

theorem numerical_range_extrema_precision {r : NumericalRangeReport}
    (hr : r ∈ numericalRangeReports) :
    |numericalSampleMinimum r.samples - r.lower| ≤ r.lowerTolerance ∧
    |numericalSampleMaximum r.samples - r.upper| ≤ r.upperTolerance := by
  have h := List.all_eq_true.mp numerical_range_all_rounded_extrema_certified r hr
  simpa only [rangeReportRounded, decide_eq_true_eq] using h

theorem balanced_average_risk_ratio_printed_precision :
    |numericalSampleMean balancedRiskRatios - (1013 : ℚ) / 1000| ≤ 1 / 2000 := by
  norm_num [numericalSampleMean, balancedRiskRatios]

theorem balanced_same_support_percentage_printed_precision :
    |(831 : ℚ) / 920 * 100 - 903 / 10| ≤ 1 / 20 := by norm_num

theorem path_slopes_printed_precision :
    (pathMedianLogLogSlopes.zip
      [(-503 : ℚ) / 1000, -1016 / 1000, -1016 / 1000, -1012 / 1000]).all
      (fun r ↦ decide (|r.1 - r.2| ≤ 1 / 2000)) = true := by
  norm_num [pathMedianLogLogSlopes]

private def pathPermutationValid (r : NumericalPathReport) : Bool :=
  decide (r.permutation.insertionSort (fun a b ↦ a ≤ b) = List.range 30)

private def pathSorted (r : NumericalPathReport) : Bool :=
  decide (r.sortedSamples.Pairwise (fun a b ↦ a ≤ b))

private def pathMatchesRawSample
    (r : (String × List ℚ) × NumericalPathReport) : Bool :=
  decide (r.1.1 = r.2.label ∧
    r.2.permutation.map (fun i ↦ r.1.2.getD i 0) = r.2.sortedSamples)

/-- Linear interpolation at `(N-1)q`, the recorded quantile convention. -/
def numericalPathQuantile (r : NumericalPathReport) : ℚ :=
  let scaled := (r.sortedSamples.length - 1) * r.quantileNumerator
  let index := scaled / r.quantileDenominator
  let fraction : ℚ := ((scaled % r.quantileDenominator : ℕ) : ℚ) /
    (r.quantileDenominator : ℚ)
  (1 - fraction) * r.sortedSamples.getD index 0 +
    fraction * r.sortedSamples.getD (index + 1) 0

private def pathQuantileCertified (r : NumericalPathReport) : Bool :=
  decide (|numericalPathQuantile r - r.printed| ≤ r.tolerance)

theorem numerical_path_report_counts :
    pathRawSamples.length = 12 ∧ numericalPathReports.length = 12 ∧
    pathRawSamples.all (fun r ↦ decide (r.2.length = 30)) = true := by
  norm_num [pathRawSamples, numericalPathReports]

theorem numerical_path_all_sorting_permutations_valid :
    numericalPathReports.all pathPermutationValid = true := by decide

theorem numerical_path_all_samples_sorted :
    numericalPathReports.all pathSorted = true := by
  norm_num (config := { maxSteps := 10000000 })
    [numericalPathReports, pathSorted, List.pairwise_cons]

theorem numerical_path_all_sorted_samples_match_raw_samples :
    (pathRawSamples.zip numericalPathReports).all pathMatchesRawSample = true := by
  norm_num [pathRawSamples, numericalPathReports, pathMatchesRawSample]

theorem numerical_path_all_printed_quantiles_certified :
    numericalPathReports.all pathQuantileCertified = true := by
  norm_num [numericalPathReports, pathQuantileCertified, numericalPathQuantile]

theorem numerical_path_index_permutation {r : NumericalPathReport}
    (hr : r ∈ numericalPathReports) : r.permutation.Perm (List.range 30) := by
  have h := List.all_eq_true.mp numerical_path_all_sorting_permutations_valid r hr
  have heq : r.permutation.insertionSort (fun a b ↦ a ≤ b) = List.range 30 := by
    simpa only [pathPermutationValid, decide_eq_true_eq] using h
  exact heq ▸ (List.perm_insertionSort (fun a b ↦ a ≤ b) r.permutation).symm

theorem numerical_path_quantile_printed_precision {r : NumericalPathReport}
    (hr : r ∈ numericalPathReports) :
    |numericalPathQuantile r - r.printed| ≤ r.tolerance := by
  have h := List.all_eq_true.mp numerical_path_all_printed_quantiles_certified r hr
  simpa only [pathQuantileCertified, decide_eq_true_eq] using h

end ReweightedNPMLE.NumericalStudy
