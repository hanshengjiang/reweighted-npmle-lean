import ReweightedNPMLE.NumericalReports

/-! # Raw numerical diagnostics and experiment bookkeeping

The diagnostic inequalities below use recorded rational residuals, not
precomputed pass/fail flags. The all-fit maximum `1.86e-6` is an upward
decimal-unit bound (it is not nearest rounding); this convention is explicit.
-/

namespace ReweightedNPMLE.NumericalStudy

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def rawFitPasses (r : Nat × ℚ × ℚ × Bool) : Bool :=
  r.2.2.2 && decide (r.2.1 ≤ 186 / 100000000 ∧ -1 / 10000 ≤ r.2.2.1)

def numericalRawKKTMaximum : ℚ :=
  numericalSampleMaximum (numericalRawFitDiagnostics.map (fun r ↦ r.2.1))

def numericalRawOneDimensionalKKTMaximum : ℚ :=
  numericalSampleMaximum
    ((numericalRawFitDiagnostics.filter (fun r ↦ r.1 == 1)).map (fun r ↦ r.2.1))

theorem numerical_raw_diagnostic_fit_count : numericalRawFitDiagnostics.length = 4160 := by decide

theorem numerical_all_raw_fit_diagnostics_pass :
    numericalRawFitDiagnostics.all rawFitPasses = true := by
  norm_num (config := { maxSteps := 10000000 })
    [numericalRawFitDiagnostics, rawFitPasses]

theorem numerical_maximum_KKT_upward_decimal_bound :
    (185 : ℚ) / 100000000 < numericalRawKKTMaximum ∧
    numericalRawKKTMaximum ≤ 186 / 100000000 := by
  norm_num (config := { maxSteps := 10000000 })
    [numericalRawKKTMaximum, numericalRawFitDiagnostics, numericalSampleMaximum,
      List.foldr, max_def]

theorem numerical_one_dimensional_KKT_printed_precision :
    |numericalRawOneDimensionalKKTMaximum - (484 : ℚ) / 1000000000| ≤
      1 / 2000000000 := by
  norm_num (config := { maxSteps := 10000000 })
    [numericalRawOneDimensionalKKTMaximum, numericalRawFitDiagnostics,
      numericalSampleMaximum, List.foldr, max_def]

theorem numerical_multistart_maxima_printed_precision :
    |numericalSampleMaximum ((multistartDiagnostics.take 10).map (fun r ↦ r.2.1)) -
      (79 : ℚ) / 100000000000000000| ≤ 1 / 200000000000000000 ∧
    |numericalSampleMaximum ((multistartDiagnostics.drop 10).map (fun r ↦ r.2.1)) -
      (37 : ℚ) / 100000000000000| ≤ 1 / 200000000000000 := by
  norm_num [multistartDiagnostics, numericalSampleMaximum, List.foldr, max_def]

theorem numerical_design_replications_exact :
    numericalDesignCounts =
      [("square_2d", 2, 250, 40), ("square_2d", 2, 500, 40),
       ("square_2d", 2, 1000, 40),
       ("three_point_1d", 1, 200, 100), ("three_point_1d", 1, 500, 100),
       ("three_point_1d", 1, 1000, 100), ("three_point_1d", 1, 2000, 100),
       ("uniform_1d", 1, 200, 100), ("uniform_1d", 1, 500, 100),
       ("uniform_1d", 1, 1000, 100), ("uniform_1d", 1, 2000, 100)] := by decide

theorem numerical_path_alpha_and_draw_counts :
    numericalPathDrawGroups.length = 16 ∧
    numericalPathDrawGroups.all (fun r ↦ decide (r.2 = List.range 30)) = true := by decide

theorem numerical_path_recorded_balanced_alpha_precision :
    |numericalPathBalancedAlpha - (5976 : ℚ) / 100| ≤ 1 / 200 := by
  norm_num [numericalPathBalancedAlpha]

theorem numerical_path_ordinary_risk_precision :
    |numericalPathOrdinaryRisk - (2662 : ℚ) / 1000000| ≤ 1 / 2000000 := by
  norm_num [numericalPathOrdinaryRisk]

theorem numerical_path_balanced_support_counts :
    ((pathRawSamples.getD 4 ("", [])).2.filter (fun x ↦ decide (x = 3))).length = 28 ∧
    ((pathRawSamples.getD 4 ("", [])).2.filter (fun x ↦ decide (x = 4))).length = 2 := by
  norm_num [pathRawSamples]

/-- The unqualified all-balanced-draws claim in the source paper is false. -/
theorem numerical_path_balanced_all_three_refuted :
    (pathRawSamples.getD 4 ("", [])).2.all (fun x ↦ decide (x = 3)) = false := by
  norm_num [pathRawSamples]

theorem numerical_path_tiny_all_draws_support_three :
    (pathRawSamples.getD 8 ("", [])).2.all (fun x ↦ decide (x = 3)) = true := by
  norm_num [pathRawSamples]

end ReweightedNPMLE.NumericalStudy
