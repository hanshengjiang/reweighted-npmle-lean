# Numerical corrections note

Author-approved correction record, 16 September 2026. This is a separate note,
as requested. The changes apply only to the numerical reporting in `paper.tex`
and its README summary in the original paper directory. This copy accompanies
the standalone package's `docs/paper.tex` reference snapshot.
No theoretical statement, recorded CSV/JSON value,
simulation code, figure, or numerical table is changed. The compiled manuscript
is rebuilt from the corrected source.

## 1. Balanced-path support assertion

Original wording:

> The resolved support remains three atoms at both concentrations and for every
> draw at the balanced value.

Corrected wording:

> The median resolved support is three atoms at both concentrations. At the
> balanced value, 28 of the 30 draws have three atoms and two have four; every
> tiny-regime draw has three atoms.

The four-atom balanced draws have CSV indices 13 and 26. This is a substantive
correction of the original universal assertion, not a rounding issue.
Lean evidence: `numerical_path_balanced_support_counts`,
`numerical_path_balanced_all_three_refuted`, and
`numerical_path_tiny_all_draws_support_three` in
`ReweightedNPMLE/NumericalDiagnostics.lean` at the package root.

## 2. Displayed precision and range endpoints

The numerical section now explicitly states that means, standard errors,
percentages, quantiles, and regression coefficients are reported at the
displayed precision. The following sentences describe rounded minimum and
maximum cell summaries, not literal enclosing bounds on unrounded values.
All previously displayed numbers are preserved.

| Cell summary | Rounded minimum | Rounded maximum |
| --- | --- | --- |
| Balanced mean risk ratio to ordinary | 1.001 | 1.020 |
| Balanced mean squared Hellinger distance to ordinary | 8.31e-6 | 1.76e-4 |
| Balanced mean total ordinary-likelihood loss | 0.0345 | 0.0964 |
| Log-scaled balanced mean likelihood loss | 0.253 | 0.532 |
| Log-scaled balanced mean squared fitted-log discrepancy | 0.479 | 0.928 |
| Tiny mean risk ratio to ordinary | 0.999985 | 1.000018 |
| Tiny mean squared Hellinger distance to ordinary | 1.43e-13 | 9.60e-10 |
| BB-scale mean risk ratio to ordinary | 1.60 | 2.19 |
| BB-scale mean total ordinary-likelihood loss | 2.14 | 7.86 |

Six of the eight unscaled original intervals fail as literal enclosing bounds;
all eight have valid rounded extrema. For example, the balanced risk-ratio
maximum is approximately 1.0202915252, not at most 1.020. The tiny-distance
and support-difference literal intervals are valid. Separately, the real
log-scaled likelihood maximum is approximately 0.5322799838: it rounds to
0.532 but exceeds that number literally. The log-scaled fitted-log discrepancy
also has valid rounded extrema; its original literal interval is valid.

The exact support-difference bound [-0.125, 0.025], the abstract's risk
comparison within 2.1%, the 90.3% support agreement, and all displayed table,
path-quantile, and regression values are retained.

Lean evidence includes `numerical_summary_raw_range_extrema_printed_precision`,
`numerical_summary_raw_literal_range_results`,
`numerical_summary_raw_scaled_extrema_printed_precision`, and
`numerical_scaled_likelihood_literal_upper_bound_refuted`. The raw-sample
equalities in `NumericalSummaryReports.lean` connect the summaries to all
920 paired replications. Historical original-interval counterexamples remain
in the development and in `PAPER_COVERAGE.md` as an audit trail.

## 3. KKT maximum wording

Original wording:

> The largest residual was 1.86 x 10^-6; the one-dimensional maximum was
> 4.84 x 10^-7.

Corrected wording specifies that the largest **recorded** residual was **at
most** 1.86 x 10^-6, a conservatively upward-rounded bound; the one-dimensional
maximum **rounded to** 4.84 x 10^-7.

The recorded all-fit maximum is approximately 1.8526120864e-6. Its nearest
three-significant-figure rounding would be 1.85e-6, so 1.86e-6 is described
as an upward bound, not nearest rounding. The recorded one-dimensional maximum
is approximately 4.8361052163e-7 and does round to 4.84e-7.
Lean evidence: `numerical_maximum_KKT_upward_decimal_bound` and
`numerical_one_dimensional_KKT_printed_precision`.

## Scope and reproducibility

The theoretical source-to-Lean audit covers all 18 named mathematical
statement blocks without a theoretical manuscript correction. The root
`ReweightedNPMLE.lean` imports both theory and numerical-report
certificates; it is not theory-only. Proof checking establishes the encoded
statements, while the separate coverage audit checks correspondence to the
paper. Numerical certificates concern recorded results, not floating-point
solver, quadrature, or continuous-oracle accuracy.

From the standalone package root, reproduce the checks with:

```bash
lake build
lake env lean Verification.lean
python3 scripts/generate_numerical_data.py --check --audit-numerics
```

The generator's six literal-interval FAIL labels deliberately audit the
original interpretations recorded above; they are not failures of the
corrected rounded-extremum statements or of generated-file reproduction.
See `COMPLETION_AUDIT.md` for the final verification record.
