import ReweightedNPMLE.GeneratedNumericalRegressionData
import Mathlib.Data.List.GetD
import ReweightedNPMLE.NumericalLeastSquares

/-! # Regression coefficients certified from raw path draws

Every response is the median of 30 recorded samples. Reordering, sorting,
logarithm bounds and interval evaluation of the full least-squares expression
are checked in Lean, without trusting the previously recorded JSON slopes.
-/

open scoped BigOperators

namespace ReweightedNPMLE.NumericalStudy

set_option maxRecDepth 100000
set_option autoImplicit false
set_option maxHeartbeats 10000000

private def regressionPermutationValid (p : NumericalRegressionPoint) : Bool :=
  decide (p.permutation.insertionSort (fun a b ↦ a ≤ b) = List.range 30)

private def regressionSourceValid (p : NumericalRegressionPoint) : Bool :=
  decide (p.rawSamples.length = 30 ∧
    p.permutation.map (fun i ↦ p.rawSamples.getD i 0) = p.sortedSamples ∧
    p.sortedSamples.IsChain (fun a b ↦ a ≤ b) ∧
    10 ≤ p.alpha ∧ p.xLog.argument = p.alpha ∧
    p.yLog.argument = numericalRegressionMedian p)

private def regressionLogsValid (p : NumericalRegressionPoint) : Bool :=
  numericalLogCertificateValid p.xLog && numericalLogCertificateValid p.yLog

theorem numerical_regression_dataset_counts :
    RegressionData.datasets.length = 4 ∧
    RegressionData.datasets.all (fun d ↦ decide (d.points.length = 14)) = true := by decide

theorem numerical_regression_all_eligible_alphas_used :
    RegressionData.datasets.all (fun d ↦
      decide (d.points.map (fun p ↦ p.alpha) = RegressionData.eligibleAlphas)) = true := by
  norm_num [RegressionData.datasets, RegressionData.eligibleAlphas]

theorem numerical_regression_metric_and_printed_values_exact :
    RegressionData.datasets.map (fun d ↦ (d.metric, d.printed)) =
      [("weight_max_deviation", (-503 : ℚ) / 1000),
       ("hellinger_to_ordinary", -1016 / 1000),
       ("ordinary_loglik_gap", -1016 / 1000),
       ("logfit_sq_sum", -1012 / 1000)] := by
  norm_num [RegressionData.datasets]

theorem numerical_regression_all_sorting_permutations_valid :
    RegressionData.datasets.all (fun d ↦ d.points.all regressionPermutationValid) = true := by decide

theorem numerical_regression_all_raw_source_checks :
    RegressionData.datasets.all (fun d ↦ d.points.all regressionSourceValid) = true := by
  norm_num (config := { maxSteps := 10000000 })
    [RegressionData.datasets, regressionSourceValid, numericalRegressionMedian,
      List.isChain_cons_cons]

theorem numerical_regression_all_log_certificates_valid :
    RegressionData.datasets.all (fun d ↦ d.points.all regressionLogsValid) = true := by
  norm_num (config := { maxSteps := 10000000 })
    [RegressionData.datasets, regressionLogsValid, numericalLogCertificateValid,
      numericalLogAdjustedArgument, numericalLogLowerRat, numericalLogErrorRat,
      numericalLogUnitLowerRat, numericalLogUnitErrorRat, Finset.sum_range_succ]

theorem numerical_regression_fallback_log_certificate_valid :
    numericalLogCertificateValid numericalRegressionFallbackCertificate = true := by
  norm_num [numericalRegressionFallbackCertificate, numericalLogCertificateValid,
    numericalLogAdjustedArgument, numericalLogLowerRat, numericalLogErrorRat,
    numericalLogUnitLowerRat, numericalLogUnitErrorRat, Finset.sum_range_succ]

theorem numerical_regression_variable_log_certificate_valid
    {d : NumericalRegressionDataset} (hd : d ∈ RegressionData.datasets) (i : Nat) :
    numericalLogCertificateValid (numericalRegressionCertificate d i) = true := by
  have h := List.all_eq_true.mp numerical_regression_all_log_certificates_valid d hd
  cases hp : d.points[i / 2]? with
  | none =>
    simpa only [numericalRegressionCertificate, hp] using
      numerical_regression_fallback_log_certificate_valid
  | some p =>
    have hm := List.mem_of_getElem? hp
    have hh := List.all_eq_true.mp h p hm
    have hxy : numericalLogCertificateValid p.xLog = true ∧
        numericalLogCertificateValid p.yLog = true := by
      simpa only [regressionLogsValid, Bool.and_eq_true] using hh
    by_cases hi : i % 2 = 0
    · simpa only [numericalRegressionCertificate, hp, hi, ↓reduceIte] using hxy.1
    · simpa only [numericalRegressionCertificate, hp, hi, ↓reduceIte] using hxy.2

theorem numerical_regression_variable_enclosures
    {d : NumericalRegressionDataset} (hd : d ∈ RegressionData.datasets) (i : Nat) :
    (numericalRegressionIntervals d i).Contains (numericalRegressionValues d i) := by
  exact numerical_log_certificate_enclosure _
    (numerical_regression_variable_log_certificate_valid hd i)

private def regressionIntervalEvaluationValid (d : NumericalRegressionDataset) : Bool :=
  decide ((numericalOLSExpression d.points.length).enclosure (numericalRegressionIntervals d) =
    some d.slopeEnclosure)

theorem numerical_regression_all_interval_evaluations_checked :
    RegressionData.datasets.all regressionIntervalEvaluationValid = true := by
  norm_num (config := { maxSteps := 10000000 })
    [RegressionData.datasets, regressionIntervalEvaluationValid, numericalOLSExpression,
      numericalExprSum, NumericalExpr.enclosure, numericalRegressionIntervals,
      numericalRegressionCertificate, NumericalInterval.point, NumericalInterval.add,
      NumericalInterval.sub, NumericalInterval.mul, NumericalInterval.inv,
      numericalRegressionFallbackCertificate, List.getElem?_cons]

theorem numerical_regression_actual_expression_enclosed
    {d : NumericalRegressionDataset} (hd : d ∈ RegressionData.datasets) :
    d.slopeEnclosure.Contains ((numericalOLSExpression d.points.length).eval
      (numericalRegressionValues d)) := by
  have h := List.all_eq_true.mp numerical_regression_all_interval_evaluations_checked d hd
  have he : (numericalOLSExpression d.points.length).enclosure (numericalRegressionIntervals d) =
      some d.slopeEnclosure := by
    simpa only [regressionIntervalEvaluationValid, decide_eq_true_eq] using h
  exact numerical_expression_enclosure_sound _ _ _
    (numerical_regression_variable_enclosures hd) he

private def regressionPrintedPrecisionValid (d : NumericalRegressionDataset) : Bool :=
  decide (d.printed - 1 / 2000 ≤ d.slopeEnclosure.lower ∧
    d.slopeEnclosure.upper ≤ d.printed + 1 / 2000)

theorem numerical_regression_all_printed_precisions_checked :
    RegressionData.datasets.all regressionPrintedPrecisionValid = true := by
  norm_num [RegressionData.datasets, regressionPrintedPrecisionValid]

theorem numerical_regression_real_slopes_printed_precision
    {d : NumericalRegressionDataset} (hd : d ∈ RegressionData.datasets) :
    |(numericalOLSExpression d.points.length).eval (numericalRegressionValues d) -
      (d.printed : ℝ)| ≤ 1 / 2000 := by
  have hb := numerical_regression_actual_expression_enclosed hd
  have h := List.all_eq_true.mp numerical_regression_all_printed_precisions_checked d hd
  have hq : d.printed - 1 / 2000 ≤ d.slopeEnclosure.lower ∧
      d.slopeEnclosure.upper ≤ d.printed + 1 / 2000 := by
    simpa only [regressionPrintedPrecisionValid, decide_eq_true_eq] using h
  have hl : (d.printed : ℝ) - 1 / 2000 ≤ (d.slopeEnclosure.lower : ℝ) := by
    simpa using (Rat.cast_le (K := ℝ)).2 hq.1
  have hu : (d.slopeEnclosure.upper : ℝ) ≤ (d.printed : ℝ) + 1 / 2000 := by
    simpa using (Rat.cast_le (K := ℝ)).2 hq.2
  rw [abs_le]
  constructor <;> linarith [hb.1, hb.2]

private theorem map_getD_range (xs : List ℚ) (fallback : ℚ) :
    (List.range xs.length).map (fun i ↦ xs.getD i fallback) = xs := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_map, List.getElem_range]
  exact List.getD_eq_getElem xs fallback hj

theorem numerical_regression_raw_sorting_properties
    {d : NumericalRegressionDataset} (hd : d ∈ RegressionData.datasets)
    {p : NumericalRegressionPoint} (hp : p ∈ d.points) :
    p.rawSamples.length = 30 ∧ p.sortedSamples.Perm p.rawSamples ∧
    p.sortedSamples.Pairwise (fun a b ↦ a ≤ b) ∧
    p.xLog.argument = p.alpha ∧ p.yLog.argument = numericalRegressionMedian p := by
  have hs := List.all_eq_true.mp
    (List.all_eq_true.mp numerical_regression_all_raw_source_checks d hd) p hp
  have hsource : p.rawSamples.length = 30 ∧
      p.permutation.map (fun i ↦ p.rawSamples.getD i 0) = p.sortedSamples ∧
      p.sortedSamples.IsChain (fun a b ↦ a ≤ b) ∧
      10 ≤ p.alpha ∧ p.xLog.argument = p.alpha ∧
      p.yLog.argument = numericalRegressionMedian p := by
    simpa only [regressionSourceValid, decide_eq_true_eq] using hs
  have ht := List.all_eq_true.mp
    (List.all_eq_true.mp numerical_regression_all_sorting_permutations_valid d hd) p hp
  have heq : p.permutation.insertionSort (fun a b ↦ a ≤ b) = List.range 30 := by
    simpa only [regressionPermutationValid, decide_eq_true_eq] using ht
  have hperm : p.permutation.Perm (List.range 30) :=
    heq ▸ (List.perm_insertionSort (fun a b ↦ a ≤ b) p.permutation).symm
  have hrange : (List.range 30).map (fun i ↦ p.rawSamples.getD i 0) = p.rawSamples := by
    rw [← hsource.1]
    exact map_getD_range _ _
  refine ⟨hsource.1, ?_, List.isChain_iff_pairwise.mp hsource.2.2.1,
    hsource.2.2.2.2.1, hsource.2.2.2.2.2⟩
  rw [← hsource.2.1]
  exact hrange ▸ hperm.map (fun i ↦ p.rawSamples.getD i 0)

def numericalRegressionFallbackPoint : NumericalRegressionPoint :=
  ⟨1, [], [], [], numericalRegressionFallbackCertificate, numericalRegressionFallbackCertificate⟩

theorem numerical_regression_values_eq_raw_coordinates
    {d : NumericalRegressionDataset} (hd : d ∈ RegressionData.datasets) (i : Nat) :
    numericalRegressionValues d (2 * i) =
      Real.log (d.points.getD i numericalRegressionFallbackPoint).alpha ∧
    numericalRegressionValues d (2 * i + 1) =
      Real.log (numericalRegressionMedian (d.points.getD i numericalRegressionFallbackPoint)) := by
  have hxd : 2 * i / 2 = i := by omega
  have hyd : (2 * i + 1) / 2 = i := by omega
  have hxm : 2 * i % 2 = 0 := by omega
  have hym : (2 * i + 1) % 2 ≠ 0 := by omega
  cases hp : d.points[i]? with
  | none =>
    simp [numericalRegressionValues, numericalRegressionCertificate, hxd, hyd, hxm, hym, hp,
      List.getD_eq_getElem?_getD, numericalRegressionFallbackPoint,
      numericalRegressionFallbackCertificate, numericalRegressionMedian]
  | some p =>
    have hm := List.mem_of_getElem? hp
    have hs := numerical_regression_raw_sorting_properties hd hm
    simp [numericalRegressionValues, numericalRegressionCertificate, hxd, hyd, hxm, hym, hp,
      List.getD_eq_getElem?_getD, hs.2.2.2.1, hs.2.2.2.2]

noncomputable def numericalRawRegressionSlope (d : NumericalRegressionDataset) : ℝ :=
  numericalOLSSlope d.points.length
    (fun i ↦ Real.log (d.points.getD i numericalRegressionFallbackPoint).alpha)
    (fun i ↦ Real.log (numericalRegressionMedian (d.points.getD i numericalRegressionFallbackPoint)))

/-- The slope bound concerns actual log alpha and raw-sample medians. -/
theorem numerical_raw_regression_slopes_printed_precision
    {d : NumericalRegressionDataset} (hd : d ∈ RegressionData.datasets) :
    |numericalRawRegressionSlope d - (d.printed : ℝ)| ≤ 1 / 2000 := by
  have hx (i : Nat) := (numerical_regression_values_eq_raw_coordinates hd i).1
  have hy (i : Nat) := (numerical_regression_values_eq_raw_coordinates hd i).2
  have h := numerical_regression_real_slopes_printed_precision hd
  rw [numericalOLSExpression_eval] at h
  simpa only [numericalRawRegressionSlope, hx, hy] using h

theorem numerical_raw_regression_denominator_positive
    {d : NumericalRegressionDataset} (hd : d ∈ RegressionData.datasets) :
    0 < d.points.length *
      (∑ i ∈ Finset.range d.points.length,
        (Real.log (d.points.getD i numericalRegressionFallbackPoint).alpha) ^ 2) -
      (∑ i ∈ Finset.range d.points.length,
        Real.log (d.points.getD i numericalRegressionFallbackPoint).alpha) ^ 2 := by
  have h := List.all_eq_true.mp numerical_regression_all_interval_evaluations_checked d hd
  have he : (numericalOLSExpression d.points.length).enclosure (numericalRegressionIntervals d) =
      some d.slopeEnclosure := by
    simpa only [regressionIntervalEvaluationValid, decide_eq_true_eq] using h
  rw [numericalOLSExpression_div] at he
  have hp := numerical_division_enclosure_denominator_positive _ _ _ _
    (numerical_regression_variable_enclosures hd) he
  rw [numericalOLSDenominatorExpression_eval] at hp
  have hx (i : Nat) := (numerical_regression_values_eq_raw_coordinates hd i).1
  simpa only [hx] using hp

/-- Each certified slope, with its intercept, is a genuine global least-squares
minimizer for log alpha versus log of the 30-draw raw-data medians. -/
theorem numerical_raw_regression_coefficients_globally_optimal
    {d : NumericalRegressionDataset} (hd : d ∈ RegressionData.datasets) (A B : ℝ) :
    let N := d.points.length
    let x := fun i ↦ Real.log (d.points.getD i numericalRegressionFallbackPoint).alpha
    let y := fun i ↦ Real.log (numericalRegressionMedian (d.points.getD i numericalRegressionFallbackPoint))
    (∑ i ∈ Finset.range N,
      (y i - (numericalRawRegressionSlope d * x i + numericalOLSIntercept N x y)) ^ 2) ≤
      ∑ i ∈ Finset.range N, (y i - (A * x i + B)) ^ 2 := by
  have hn := List.all_eq_true.mp numerical_regression_dataset_counts.2 d hd
  have hlen : d.points.length = 14 := by
    simpa only [decide_eq_true_eq] using hn
  have hpos : 0 < d.points.length := by omega
  exact numerical_ols_globally_minimizes_squared_error _ _ _ hpos
    (numerical_raw_regression_denominator_positive hd) A B

end ReweightedNPMLE.NumericalStudy
