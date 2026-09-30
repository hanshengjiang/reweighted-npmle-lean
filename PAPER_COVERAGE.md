# Paper-statement coverage map (corrected numerical reporting)

Historical source snapshot: `docs/paper.tex`. This is the development coverage
map. Read it with the [29 September release review](audit/release-checks/coverage-review.md),
which records interface qualifications and differences in later manuscript versions. The author-approved numerical corrections reconcile
the reporting with the verified recorded data. No theoretical statement or
raw data was changed. The separate application record is
`docs/NUMERICAL_CORRECTIONS_NOTE.md`; the original-source counterexamples below
are retained as an audit trail. Compilation of a weaker statement is not
counted as exact coverage.

## Main statistical statements

| Paper label | Authoritative Lean evidence | Checked correspondence |
| --- | --- | --- |
| `thm:main` (i)--(iv) | `gaussian_exact_regularization_main` | Common positive constant; uniform threshold and true law; one Borel joint event; full probability-law optimizer fiber is a singleton; finite topological support; literal coordinate deviations, ordinary likelihood gap, squared log-density ratios and global Hellinger rate. |
| `thm:main`, dimension refinements | `gaussian_main_support_dimension_refinements`, `gaussianPaperSupportOrder` | Actual unique mixing-law support bounded by `C log n` for dimension one and `C r_n` for dimensions at least two, with uniform joint probability. |
| `cor:tiny` | `gaussian_exact_regularization_joint_tiny_explicit`; common-constant wrapper `gaussian_exact_regularization_tiny` | Separate probability/risk constants independent of `L` are preserved by the explicit theorem; the wrapper combines them with an `L`-dependent support constant. Actual shape `n^(2L+2)`; uniform joint event; uniqueness/finite support; literal perturbation `n^(-L)`; common-constant Hellinger risk. |
| `cor:weak` | `gaussian_reweighted_optimizer_weak_consistency` | Every weighted-optimizer rule at positive weights; every weak neighborhood has vanishing outer-probability failure under the actual triangular joint experiment. |
| `cor:approx` | `gaussian_approximate_optimizer_joint_robustness` | Fixed `c0=1/6144`; simultaneous attainable approximate laws, no atomicity assumption; actual likelihood/log-fit bounds and Hellinger risk on one Borel joint event. |
| `thm:near-mle` | `gaussian_uniform_nearMLE_paper_theorem` | One positive constant controls uniform failure `C n^-b` and the literal displayed Hellinger rate for every near-truth candidate on one Borel data event. |

The experiment `gaussianDataWeightMeasure` is the iid density sample measure
times the iid Gamma weight product. `compactGaussianMixtureLaw_eq_density`
identifies it with the generative Gaussian-mixture model. Gamma positivity and
probability are supplied at the eventual concentration scales. The
weak-consistency experiment uses shape one only at irrelevant small sample
sizes where the balanced concentration is nonpositive.

## Abstract geometry and appendices

| Paper label | Authoritative evidence | Checked correspondence |
| --- | --- | --- |
| `thm:effective` | `effective_dimension_full_support` | Actual hull, relative set, projection width and Gamma product; full-law support statistic, finiteness, measurability, attainment; exact and simultaneous approximate fits. Universal constants `C=10000000`, `c=1/3072`; `Q=q+log(2n)`. |
| `lem:regularity` | `canonical_fitted_maps_locally_lipschitz`, `canonical_fitted_value_convexOn_univ`, `canonical_fitted_value_contDiffOn_one`, canonical envelope derivative, `paper_full_optimizer_fiber_geometry` | Compact positive hull; globally convex/C1 optimized value on the whole positive orthant; fitted-log gradient; both fitted maps locally Lipschitz; all-law fitted-vector agreement. |
| `lem:extreme` | `paper_full_optimizer_fiber_geometry`, `full_probability_optimizer_extreme_iff`, `full_extreme_optimizer_support_finite_card_le`, `measurable_maximumExtremeSupport` | Compact/nonempty/intrinsically convex full fiber; full extremality iff finite positive injective atom representation with independent evaluations; at most `n` atoms; Borel statistic. No candidate-law finiteness hypothesis. |
| `lem:matrix-sensitivity`, `lem:hessian-summary` | `full_support_sensitivity_ae` | Actual second Fréchet derivative on one dictionary-dependent conull set; simultaneous projections for every full-law extreme optimizer of rank `k-1`, and attained maximal rank `s_ext-1`. Hermitian/idempotent matrices and Loewner domination are conclusions. |
| `lem:radial` | `isCompact_paperRadialEvent`, `paper_radial_localization`, `canonical_paper_radial_exact_fit` | Literal compact event with `rho=1/16`, positivity implied by the coordinate bound; strict relative norm and log displacement `<1/8`; exact constants `36/12`, `37/13`, `72/24`; nonnegative exact `Z` and its upper bound. |
| `lem:determinant-moment` | `canonical_maximumExtremeSupport_paper_gamma_moment` | Actual full-law statistic on the literal radial event; `t=z(w)-z(1)` on positive weights, `Z=sum (w_i-1)t_i`; restricted nonnegative expectation expresses the indicator; moment `<=1` proved, not assumed. |
| `prop:gaussian-width` | `gaussian_probability_relative_width_bound`, `gaussianTaylorResidual_eq_zero_of_mul_eq_zero` | Arbitrary reference probability law, actual full-law density ratios, exact rank, `one` membership and literal Taylor residual; `ST=0` gives residual zero. |
| `cor:conditional` | `gaussian_conditional_structural_and_likelihood_bounds` | Every deterministic dataset with arbitrary `C0 sqrt(log n)` radius; no genericity, sampling or correct specification; actual full-law statistic and all exact-law fit bounds on one measurable weight event. |
| `prop:generic` | `gaussian_generic_evaluation_independence`, full optimizer-fiber uniqueness consequence | One Borel conull data set; every distinct possibly data-dependent atom list under `k(d+1)<=n`; exact `2m(d+1)<=n` uniqueness threshold. |
| `lem:finite-net` | `compactGaussianMixture_simultaneous_paper_finite_net` | Deterministic nonempty finite net of actual probability-law densities on `K`; literal entropy order; radius `O(sqrt(log n))`; uniform radius failure `<=n^(-b-2)` without prefactor; `H<=n^-3` and uniform log error `<=n^-3`. |
| `lem:gamma-concentration` | `gamma_coordinate_concentration` | Actual Gamma law; exact scalar absolute coordinate tail `2 exp(-a t^2/4)` for `a>0`, `0<t<=1`, including the endpoint. |

## Dirichlet proposition

`prop:dirichlet` is mathematically closed.
`gammaWeight_normalize_total_joint_law` gives the exact product
Dirichlet/Gamma law and independence. The mean and variance interfaces are
`symmetricDirichlet_weighted_empirical_mean` and
`symmetricDirichlet_weighted_empirical_variance`.
`empiricalDirichlet_expected_tv_le` uses merged distinct-observation masses,
so repeated observations are covered; its summands are identified with actual
empirical probability-law singleton differences.
`compactGaussianMixture_unchanged_population_criterion` supplies the joint
iid-data/Gamma population equality for raw and normalized weights.
`compactGaussianMixture_population_gap_eq_klDiv` identifies the gap with
genuine mathlib KL divergence, proves nonnegativity and characterizes zero gap
by equality of density laws. True-log integrability is derived from exactly
the candidate integrability assumption in the paper.

## Historical numerical reporting audit: original literal ranges

`NumericalStudy` contains compiled exact/rational certificates for replication
counts, support comparisons, fit diagnostics, multistart agreement, slope
ranges and broad risk/likelihood ranges. Those broad intervals are not counted
as proofs of narrower printed intervals.

`python3 scripts/generate_numerical_data.py --check --audit-numerics`
verifies exact certificate reproduction from all six source files and compares
original printed ranges with exact rational statistics computed from the raw CSVs.
Decimals below approximate the extrema for readability; PASS/FAIL tests are
exact rational comparisons.

| Quantity | Printed range | Actual extrema (approximately) | Literal bounds |
| --- | --- | --- | --- |
| Balanced risk ratio | `[1.001,1.020]` | `[1.0011230675,1.0202915252]` | FAIL |
| Tiny risk ratio | `[0.999985,1.000018]` | `[0.9999846702,1.0000177566]` | FAIL |
| BB risk ratio | `[1.60,2.19]` | `[1.5989669858,2.1902608677]` | FAIL |
| Balanced H² to ordinary | `[8.31e-6,1.76e-4]` | `[8.3110537293e-6,1.7648081128e-4]` | FAIL |
| Tiny H² to ordinary | `[1.43e-13,9.60e-10]` | `[1.4332758273e-13,9.5957890168e-10]` | PASS |
| Balanced likelihood loss | `[0.0345,0.0964]` | `[0.0344945186,0.0964020198]` | FAIL |
| BB likelihood loss | `[2.14,7.86]` | `[2.1361195703,7.8632995503]` | FAIL |
| Balanced support difference | `[-0.125,0.025]` | `[-0.125,0.025]` | PASS |

These are consistent with ordinary finite-precision reporting, but rounded
summary values are different propositions from literal exact bounds.
The author approved explicit rounded-minimum/maximum wording, now applied
to the source. The separate numerical corrections note records this decision.
`numerical_range_all_rounded_extrema_certified` now certifies all eight rounded
extrema at their displayed precision. `numerical_range_literal_interpretation_results`
proves the six-FAIL/two-PASS pattern in Lean. These are different propositions.
The historical audit itself changed no paper or raw numerical source;
the subsequent approved correction changes reporting text only.

### Exact table and path certificates

`NumericalTable` checks all 48 table means against means recomputed from their
raw samples, and all 42 standard errors against recomputed exact squared
standard errors. All 3840 sample entries are included. The 90 displayed
values lie within half the last displayed decimal unit; the square-root
standard-error precision theorem concerns the actual standard error, not
just its square.

`NumericalReports` checks 12 displayed path medians/quantiles against the CSVs,
including balanced and tiny risks, likelihood losses and distances, the
Wasserstein median, and the BB 90th-percentile support. Sorting permutations
are proved to be permutations of all 30 draw indices; reordered raw samples,
pairwise ordering, and linear-interpolation quantile arithmetic are verified.
It also certifies `1.013` average balanced risk ratio and `90.3%` agreement.
`NumericalRegressionReports` additionally recomputes all four slopes from the
1680 raw responses at all 14 eligible alpha values, certifying each sorted
30-draw median, actual real logarithms, positive variance denominator and
half-last-decimal precision. The actual slope/intercept pair is proved to
globally minimize least-squares error; JSON slopes are not used as an oracle.

`NumericalKKT` gives the exact displayed residual formula and its nonpositivity
at every full-probability-measure optimizer. `NumericalLogBounds` supplies
proved finite-series logarithm enclosures, with a rational certificate soundness
interface. `NumericalScaledReports` now proves the actual real minimum and
maximum of the 11 scaled cell means lie within half a displayed decimal unit
of `0.253`, `0.532`, `0.479`, and `0.928`. It refutes the literal likelihood
upper bound `0.532` (the maximum is approximately `0.532280`), and proves the
literal log-fit bounds `[0.479,0.928]` for every cell. The real logarithm and
interval enclosures are also instantiated on all raw regression path medians.

### Original balanced-path contradiction and applied correction

The original paper said the support was three atoms for every balanced path draw.
`path_results.csv` records support four for draws 13 and 26 at the balanced
concentration; the other 28 draws have support three. This is not a rounding
issue. Standalone Lean checks of the generated raw sample lists verify the
`28`/`2` counts and all-three support for the tiny draws. `NumericalDiagnostics`
includes these claims and an explicit refutation of all-three balanced support;
its full compilation and integrated audit pass. It also verifies the tighter
KKT and multistart maxima using raw rationals, all 4160 raw fit diagnostics,
the exact 11 design/sample-size replication counts and 16 groups of 30 path
draws. The `1.86e-6` KKT maximum is certified as an upward decimal-unit bound,
not falsely labeled as nearest rounding.
The corrected paper now states the verified median and 28/2 balanced counts,
all-three tiny draws, and conservative recorded KKT bound. The raw data and
historical counterexample theorems remain unchanged.

The numerical certificates concern recorded data and reports, not correctness
of unverified floating-point solvers, quadrature or algorithmic convergence.
The paper makes no general numerical algorithm convergence claim.

### Whole-design source linkage and experimental laws

`NumericalSummaryReports` connects every whole-design mean and risk ratio to
all 920 paired replications: 8280 raw rational responses and 3680 integer
support counts in 11 cells. Replication indices, all input lengths and design
metadata are checked. Its exact arithmetic equalities link all eight range
reports, support agreement, balanced average risk ratio and log-scaled extrema
to the raw samples, not precomputed JSON summaries. Real sample means equal
the casts of exact rational means; the abstract's `2.1%` cellwise risk
comparison is proved using actual real ratios of raw sample means.

`NumericalDesigns` supplies the three literal experimental mixing laws:
three-point masses `1/4,1/2,1/4` at `-5/2,0,5/2`, Lebesgue-uniform mixing on
`[-5/2,5/2]`, and equal masses at the four `(±7/4,±7/4)` corners. Their stated
parameter boxes are compact and nonempty; all three laws satisfy the support
constraint and induce Gaussian densities integrating to one. Injectivity and
singleton masses identify the discrete laws; every uniform singleton has
mass zero. The tiny `n^3` shape is the exact `L=1/2` specialization, and the
numerical average-one normalization equals `nP`, sums to `n`, and preserves
all likelihood maximizers.

## Definition correspondence and verification

`probabilityMixtureValue` is the coordinatewise integral of the dictionary,
proved equal to its vector integral. `C` is its actual compact convex hull,
not an assumed finite dictionary or merely a closure. `IsMaxOn` expresses
membership and comparison with every feasible law/vector.
Intrinsic fiber convexity is probability convex combination; its
continuous-test-function embedding is injective and preserves these
combinations, so its extreme points are genuine full-fiber extreme laws.
`maximumExtremeSupport` is the attained maximum topological-support cardinality,
extended by zero outside positive weights. Euclidean vectors use `WithLp`
with exponent two; submodule `starProjection` is the orthogonal projection.
Hellinger uses the paper convention `integral (sqrt p-sqrt q)^2`.

All 621 central declarations were independently axiom-audited: 614 use only
standard axioms (one uses just two of the three), seven are axiom-free.
The latest whole default build passed 3822 jobs. All production
modules are included through the umbrella; only mathlib v4.30.0 is required.
No production proof placeholders, project axioms or audited `sorryAx` occur.
The preexisting excluded `Check.lean` experiments are retained.

## Completion checks

`COMPLETION_AUDIT.md` records the latest source/type requirement checks.
`PROPOSED_NUMERICAL_CORRECTIONS.md` retains the approved proposal;
`docs/NUMERICAL_CORRECTIONS_NOTE.md` separately records its application to
the false support assertion, rounded extrema and conservative KKT bound.

- The corrected source states 28 three-atom and two four-atom balanced draws,
  all three-atom tiny draws, rounded minimum/maximum cell summaries, and an
  upward bound for the recorded all-fit KKT maximum. These are the propositions
  proved by the corresponding numerical interfaces. The exact support-difference
  bound and all named theoretical statements remain unchanged.
  Whole-design raw-sample linkage and literal experimental definitions now
  compile and are integrated. The table, scaled extrema and 12
  displayed path quantiles are now certified at their displayed precision;
  do not substitute broad-range certificates for literal range bounds.
- Both default build targets pass; the independent central-declaration audit
  and generated-source reproduction check are recorded in `COMPLETION_AUDIT.md`.
- Preserve unrelated user edits and raw data.
- The task's `caffeinate -i` process has been stopped after final verification;
  see the terminal cleanup record in `COMPLETION_AUDIT.md`.
