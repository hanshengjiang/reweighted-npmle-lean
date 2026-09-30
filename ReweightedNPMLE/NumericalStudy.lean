import ReweightedNPMLE.GeneratedNumericalData
import Mathlib.Tactic

/-!
# Certified numerical-study bookkeeping

`GeneratedNumericalData.lean` is deterministically generated from the three committed raw CSVs,
two diagnostic JSON files and the numerical LaTeX table by `scripts/generate_numerical_data.py`.
It records source SHA-256
digests, exact decimal rationals, and the 920 triples of resolved supports
`(ordinary, balanced, tiny)`.  The discrete claims below are proved by kernel reduction, without
`native_decide` or an oracle axiom.
-/

namespace ReweightedNPMLE.NumericalStudy

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- There are 920 paired replications in the generated raw-data certificate. -/
theorem paired_replication_count : supportTriples.length = 920 := by decide

/-- The inverse-polynomial (`RR-tiny`) fit has the same resolved support in all 920 pairs. -/
theorem tiny_same_support_all : supportTriples.all (fun r ↦ r.1 = r.2.2) = true := by
  decide

/-- Exactly 831 of 920 balanced fits have the same resolved support as the ordinary fit. -/
theorem balanced_same_support_count :
    (supportTriples.filter fun r ↦ r.1 = r.2.1).length = 831 := by
  decide

/-- The printed decimal is a rounding of the exact balanced fraction `831 / 920`. -/
theorem balanced_same_support_fraction :
    |(831 : ℚ) / 920 - 9032608695652173 / 10000000000000000| <
      1 / 10000000000000000 := by
  norm_num

/-- The generated certificate also covers all 3,680 Monte Carlo fits and 480
regularization-path fits. -/
theorem diagnostic_fit_count : diagnosticFlags.length = 4160 := by decide

/-- Every recorded fit converged, every KKT gap is below `2e-6`, and every
raw ordinary-likelihood gap is at least `-1e-4`. -/
theorem all_fit_diagnostics_pass :
    diagnosticFlags.all (fun r ↦ r.1 && r.2.1 && r.2.2) = true := by
  decide

/-- The one-dimensional maximum KKT residual is below `5e-7`, covering
3,200 Monte Carlo fits and 480 regularization-path fits. -/
theorem one_dimensional_kkt_fit_count : oneDimensionalKktFlags.length = 3680 := by decide

theorem one_dimensional_kkt_below_five_e_neg_seven :
    oneDimensionalKktFlags.all id = true := by decide

/-- The dispersed-initialization certificate contains ten starts in each of
the representative one- and two-dimensional problems. -/
theorem multistart_fit_count : multistartDiagnostics.length = 20 := by decide

theorem multistart_same_resolved_support_all :
    multistartDiagnostics.all (fun r ↦ r.1) = true := by decide

private def belowRat (b x : ℚ) : Bool := decide (x < b)

/-- Every one-dimensional multistart fit is within `8e-16` squared
Hellinger distance of its reference fit. -/
theorem multistart_one_dimensional_hellinger_certified :
    (multistartDiagnostics.take 10).all
      (fun r ↦ belowRat (8 / 10000000000000000) r.2.1) = true := by
  norm_num [multistartDiagnostics, belowRat]

/-- Every two-dimensional multistart fit is within `4e-13` squared
Hellinger distance of its reference fit. -/
theorem multistart_two_dimensional_hellinger_certified :
    (multistartDiagnostics.drop 10).all
      (fun r ↦ belowRat (4 / 10000000000000) r.2.1) = true := by
  norm_num [multistartDiagnostics, belowRat]

theorem multistart_kkt_below_two_e_neg_seven :
    multistartDiagnostics.all
      (fun r ↦ belowRat (2 / 10000000) r.2.2) = true := by
  norm_num [multistartDiagnostics, belowRat]

private def inClosedRatInterval (a b x : ℚ) : Bool :=
  decide (a ≤ x ∧ x ≤ b)

theorem numerical_summary_cell_count :
    balancedRiskRatios.length = 11 ∧
    tinyRiskRatios.length = 11 ∧
    bbRiskRatios.length = 11 := by decide

/-- In every design/sample-size cell, balanced risk is between `1` and
`1.021` times ordinary-NPMLE risk. -/
theorem balanced_risk_ratio_range_certified :
    balancedRiskRatios.all (inClosedRatInterval 1 (1021 / 1000)) = true := by
  norm_num [balancedRiskRatios, inClosedRatInterval]

/-- Tiny-reweighting risk stays within one part in ten thousand of ordinary
NPMLE risk in every cell. -/
theorem tiny_risk_ratio_range_certified :
    tinyRiskRatios.all
      (inClosedRatInterval (9999 / 10000) (10001 / 10000)) = true := by
  norm_num [tinyRiskRatios, inClosedRatInterval]

/-- Bayesian-bootstrap-scale risk is between `1.5` and `2.2` times ordinary
risk in every cell. -/
theorem bb_risk_ratio_range_certified :
    bbRiskRatios.all (inClosedRatInterval (3 / 2) (11 / 5)) = true := by
  norm_num [bbRiskRatios, inClosedRatInterval]

/-- The cellwise balanced-minus-ordinary mean support difference lies in the
reported interval `[-0.125, 0.025]`. -/
theorem balanced_mean_support_difference_range_certified :
    balancedMeanSupportDifferences.all
      (inClosedRatInterval (-1 / 8) (1 / 40)) = true := by
  norm_num [balancedMeanSupportDifferences, inClosedRatInterval]

theorem balanced_mean_hellinger_to_ordinary_range_certified :
    balancedMeanHellingerToOrdinary.all
      (inClosedRatInterval 0 (1 / 5000)) = true := by
  norm_num [balancedMeanHellingerToOrdinary, inClosedRatInterval]

theorem tiny_mean_hellinger_to_ordinary_range_certified :
    tinyMeanHellingerToOrdinary.all
      (inClosedRatInterval 0 (1 / 1000000000)) = true := by
  norm_num [tinyMeanHellingerToOrdinary, inClosedRatInterval]

theorem balanced_mean_ordinary_loglik_gap_range_certified :
    balancedMeanOrdinaryLoglikGap.all
      (inClosedRatInterval (3 / 100) (1 / 10)) = true := by
  norm_num [balancedMeanOrdinaryLoglikGap, inClosedRatInterval]

/-- The exact decimal representation of the reported weight-deviation slope
lies in `[-0.504,-0.502]`. -/
theorem path_weight_deviation_slope_certified :
    (pathMedianLogLogSlopes.take 1).all
      (inClosedRatInterval (-504 / 1000) (-502 / 1000)) = true := by
  norm_num [pathMedianLogLogSlopes, inClosedRatInterval]

/-- The three second-order path slopes (Hellinger, likelihood loss, fitted-log
discrepancy) all lie in `[-1.02,-1.01]`. -/
theorem path_second_order_slopes_certified :
    (pathMedianLogLogSlopes.drop 1).all
      (inClosedRatInterval (-102 / 100) (-101 / 100)) = true := by
  norm_num [pathMedianLogLogSlopes, inClosedRatInterval]

end ReweightedNPMLE.NumericalStudy
