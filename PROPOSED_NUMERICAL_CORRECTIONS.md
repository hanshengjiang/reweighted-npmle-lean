# Numerical text correction proposal - applied with author approval

The author approved these proposals on 16 September 2026. They have been
applied to the original manuscript and its README summary, preserving the recorded data,
displayed summary numbers, and theoretical statements. The original proposal
below is retained as an audit trail. The separate requested application record
is [NUMERICAL_CORRECTIONS_NOTE.md](docs/NUMERICAL_CORRECTIONS_NOTE.md).
The corrected source snapshot is `docs/paper.tex`.

## Balanced-path support

Replace the sentence beginning “The resolved support remains three atoms” with:

> The median resolved support is three atoms at both concentrations. At the
> balanced value, 28 of the 30 draws have three atoms and two have four;
> every tiny-regime draw has three atoms.

Evidence: `numerical_path_balanced_support_counts`,
`numerical_path_balanced_all_three_refuted`,
`numerical_path_tiny_all_draws_support_three`, and the raw path-quantile checks.
The four-atom balanced draws are CSV indices 13 and 26.

## Reporting precision and range endpoints

Add an explicit numerical-reporting convention:

> Numerical means, standard errors, percentages, quantiles and regression
> coefficients are reported at the displayed precision. Range endpoints
> described as rounded extrema are the rounded minimum and maximum cell
> summaries, not literal enclosing bounds on the unrounded values.

Rewrite the following range sentences to describe **rounded extrema**, while
keeping the existing numbers:

- Balanced mean risk ratio: `1.001`, `1.020`.
- Balanced mean squared Hellinger distance: `8.31e-6`, `1.76e-4`.
- Balanced mean likelihood loss: `0.0345`, `0.0964`.
- Log-scaled balanced mean likelihood loss: `0.253`, `0.532`.
- Log-scaled balanced mean squared log discrepancy: `0.479`, `0.928`.
- Tiny mean risk ratio: `0.999985`, `1.000018`.
- Tiny mean squared Hellinger distance: `1.43e-13`, `9.60e-10`.
- BB-scale mean risk ratio: `1.60`, `2.19`.
- BB-scale mean likelihood loss: `2.14`, `7.86`.

For example, replace “the ratio ... lies between ...” with “the ratio ...
has rounded minimum ... and rounded maximum ...”. The exact support-difference
bound `[-0.125,0.025]` is valid and need not change.

Evidence: all eight range-extremum precision certificates, the separate
six-failed/two-valid literal-range theorem, the real log-scaled extremum
certificates and the literal `0.532` upper-bound refutation. The whole-design
raw-sample equalities now link these certificates to all 920 replications.
`PAPER_COVERAGE.md` gives the unrounded extrema and individual verdicts.

## KKT maximum

Replace the all-fit maximum sentence with:

> Across the 4160 fitted optimization problems, the largest recorded residual
> was at most `1.86 × 10⁻⁶`, a conservatively upward-rounded bound; the
> one-dimensional maximum rounded to `4.84 × 10⁻⁷`.

Evidence: `numerical_maximum_KKT_upward_decimal_bound` and
`numerical_one_dimensional_KKT_printed_precision`. The first theorem proves
the recorded maximum lies in `(1.85e-6,1.86e-6]`; the second certifies nearest
rounding of the one-dimensional maximum. Do not describe the first as a
nearest-rounding certificate.

These are certificates about recorded numerical diagnostics and reports,
not proofs of floating-point optimization, oracle or quadrature accuracy.
