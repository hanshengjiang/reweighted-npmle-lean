# Formalization status

Historical development record (16 September 2026). For the independently rerun
29 September release checks and current scope qualifications, see
[RELEASE_CHECKS.md](RELEASE_CHECKS.md) and the
[release statement review](audit/release-checks/coverage-review.md).

All named mathematical paper statements have compiled Lean interfaces.
The author approved the numerical reporting corrections on 16 September 2026;
they are applied to the manuscript and its README, with a separate record in
`docs/NUMERICAL_CORRECTIONS_NOTE.md`. The reference snapshot in `docs/paper.tex`
uses rounded extrema,
an upward bound for the recorded KKT maximum, and the actual balanced-path
counts (28 three-atom draws and two four-atom draws). No theoretical statement
or raw numerical data was changed. See `COMPLETION_AUDIT.md` for the final checks.

## Verified fitted-value/support milestone

`lake build` builds both `ReweightedNPMLE` and `Verification`. The dependency
manifest requires only mathlib v4.30.0. The audited theorems below use only
`propext`, `Classical.choice`, and `Quot.sound`; there are no proof placeholders
or project-defined axioms in the production development.

Latest whole-library verification, including the literal finite net, arbitrary
deterministic-radius conditional theorem, population/KL theorem, full-law
Hessian projections, C1 regularity, compact radial event, determinant moment,
dimension refinements, repeated-observation empirical TV and the exact numerical
table/path, raw diagnostics, real log-scaled extrema, raw-data regressions,
whole-design raw-sample summaries and literal experimental model laws:
`lake build` passed all 3822 jobs. All 621 declarations in
`Verification` were independently checked: 613 depend only on the three
standard axioms above, one uses only `propext` and `Quot.sound`, and seven
use no axioms.

- `FittedRegularity`: compact positive feasibility gives common coordinate
  bounds, canonical fitted-value and fitted-log continuity on the positive
  orthant, and almost-everywhere fitted-log differentiability on that whole
  orthant. `fittedLogDisplacement` is a globally measurable zero extension
  of the displacement used on positive weights.
- `FittedEnvelope` and `FittedHessian`: the canonical envelope gradient
  identity holds at every positive weight; its local second-order expansion
  follows at fitted-log differentiability points.
- `SupportSensitivityAnalytic`: two-sided active-mass perturbations imply
  Hessian domination of the weighted tangent projection and the exact
  `(17/9)^(k-1)` Jacobian determinant gain for a full-support extreme finite
  representation. Atoms may vary with weights; they are not required to
  remain in a fixed finite dictionary near the derivative point.
- `ExtremeSupport`: fixed-cardinality independent representation events and
  `maximumIndependentSupport` are measurable. The maximum is at most `n`,
  is attained when positive, and is positive when the canonical fit belongs
  to the dictionary's convex hull. The representation events agree with
  full-support extreme finite mixture-fiber representations.
- `ChangeOfVariables`: the injective Gamma change-of-variables transfer
  accepts almost-everywhere derivatives and Jacobian domination.
- `FittedDeterminantMoment`: the canonical maximum-independent-support
  Gamma moment is at most one on any measurable positive localization set
  with coordinatewise displacement bounded by `1/8`. Derivatives,
  monotonicity, injectivity, support measurability, and determinant gain are
  proved, not supplied as hypotheses.
- `EffectiveDimension.canonical_maximumIndependentSupport_gamma_tail`:
  if the localization set bounds the exponential cost by `H`, the support
  tail above `H + q` is bounded by `exp(-q)`. No integrability or moment
  estimate is supplied as a hypothesis.
- `FittedLocalization` translates radial localization to ordinary likelihood
  loss and fitted-log error for all near-optimal feasible fits.
- `GammaEffectiveEvent` gives a closed common concentration event with
  failure probability at most `2 exp(-q)` and derives radial scale bounds,
  including the residual-width cost `alpha E <= 2`.
- `EffectiveSparsification.effective_dimension_finite_support` assembles
  concentration, radial localization, and the determinant support tail on
  one measurable event of failure probability at most `3 exp(-q)`. Explicit
  universal constants are `C = 10000000` and `c = 1/3072`. The theorem includes
  coordinatewise weight deviation, independent finite-representation support,
  ordinary likelihood loss, fitted-log squared error, and simultaneous
  conclusions for all near-optimal fits and tolerances. It is not yet the
  full-measure `s_ext` theorem by itself; the verified transfer is listed below.
- `ProbabilityOptimizerFiber` now defines genuine arbitrary-probability-
  measure moment fibers and proves weak continuity, compactness, and
  nonemptiness exactly for fitted vectors in the compact dictionary hull.
  An explicit finite atomic probability measure realizes any finite convex
  representation; the fiber is closed under every probability convex
  combination. Optimization over all probability measures agrees with
  the fitted-vector fiber. Every optimizing measure satisfies the likelihood
  contact identity almost everywhere and everywhere on its topological
  support, including infinite-support measures.
- `ProbabilityFiberGeometry` embeds the full probability-measure fiber
  injectively via integrals of all continuous test functions into a real
  locally convex product space. Its image is compact and convex. Full-fiber
  extremality is proved equivalent to the intrinsic absence of nontrivial
  probability-measure decompositions. Extreme points exist, Krein--Milman
  holds, and uniqueness of full-fiber extreme points implies that the full
  probability-measure optimizer fiber is a singleton.
- `FiniteProbabilityExtreme` proves that any probability measure concentrated
  on a finite injective atom list is exactly its finite atomic mass
  representation. Independent evaluation vectors give uniqueness on that
  support and full-fiber extremality against arbitrary measure decompositions.
  For positive-mass finite optimizing laws, full-fiber extremality is
  equivalent to evaluation-vector independence. The law's topological support
  is exactly its atom list.
- `MeasureFiberPerturbation` constructs genuine probability laws with real
  densities `1+h` and `1-h` from any bounded nonzero zero-moment perturbation,
  proves that their fitted moments agree and their average is the original
  measure, and thereby excludes full-fiber extremality.
- `ExtremeSupportPartition` constructs such a perturbation from too many
  disjoint positive-mass measurable regions. The likelihood contact identity
  derives zero total mass from zero fitted moments.
- `FullExtremeSupport.full_extreme_optimizer_support_finite_card_le` now
  excludes infinite-support extreme optimizers and proves that every full-
  measure extreme optimizer has finite topological support of size at most
  `n`. `full_probability_optimizer_extreme_iff` proves the complete paper
  extreme-optimizer characterization: an extreme law is exactly a finite
  positive atomic probability law with independent evaluation vectors.
  Finite support and the `n`-atom bound are conclusions, not hypotheses.
- `MeasureExtremeSupport` defines `maximumExtremeSupport` directly from all
  full probability-measure extreme optimizers. Each support-cardinality event
  equals the corresponding independent representation event, and its supremum
  equals `maximumIndependentSupport`. The full-measure statistic is measurable;
  at positive weights its maximum is attained, lies between `1` and `n`, and
  bounds every extreme law's support size.
- `FullEffectiveDimension.effective_dimension_full_support` proves the abstract
  paper effective-dimension theorem for a continuous positive dictionary on a
  nonempty compact metric space, using the actual full-measure support statistic.
  On one measurable event with failure at most `3 exp(-q)`, every extreme law
  has finite support at most `10000000 (r+q)`, and all exact and simultaneous
  approximate fitted-vector error bounds hold. The statistic's measurability,
  finiteness, and attainment are conclusions, not extra hypotheses.
- `SupportUniqueness` proves the complete deterministic uniqueness transfer:
  if every extreme optimizer has at most `m` atoms and the dictionary is
  independent on every distinct atom list of size at most `2m`, the full
  optimizer fiber is a singleton with at most `m` atoms. The proof enumerates
  the union of two extreme supports and applies the full-measure
  Krein--Milman theorem; no finite-support assumption is placed on other laws.
- `GaussianStructural` identifies the actual relative fitted hull with
  convex combinations of relative Gaussian atoms, derives its Taylor width
  using only membership of the reference fit in the hull, and proves that
  canceling the common centered density preserves the full optimizer fiber
  and its extremality. `gaussian_effective_dimension_full_support` instantiates
  the full abstract theorem with rank `1 + choose (L+d) d` and the exact Taylor
  residual, giving conditional finite-sample structural and likelihood bounds
  without sampling or correct-specification assumptions. Its finite-sample
  interface retains explicit rank/remainder scale inequalities; their eventual
  paper specialization is now verified below. The Gaussian uniqueness consequence is also proved
  with the paper's exact `2m(d+1) <= n` threshold. Its simultaneous genericity
  hypothesis is now supplied by the verified null-incidence theorem below.
- `AnalyticIncidence` proves finite-order derivative detection at every point
  of a nontrivial real-analytic function, detection by finite words of basis
  vectors, and the minimal-order selection giving a vanishing scalar
  derivative with nonzero derivative in a basis coordinate. It also proves
  that every locally `C1` image from fewer real dimensions is null for every
  target Haar measure, using Hausdorff dimension and Haar absolute continuity.
- `GaussianIncidence` proves whole-function independence of distinct Gaussian
  translates via the existing Gaussian mixing-law identifiability theorem.
  Every nonzero signed combination is nontrivial. Gaussian kernels and
  parameterized signed families are jointly real analytic. Normalized
  coefficient charts have open distinct-location domains and nuisance dimension
  `kd + k - 1 < n` under the paper's threshold. Every evaluation dependence
  belongs to a normalized chart, and every chart-family zero has the regular
  finite-word derivative needed for the incidence argument.
- `IncidenceSmoothness` proves joint analytic smoothness of observation-only
  iterated derivative families. `IncidenceJacobian` proves full row rank using
  independent observation-coordinate blocks and an explicit right inverse.
  `IncidenceProjection` applies the implicit function theorem locally and a
  countable open subcover globally to prove that the projection of every regular
  zero locus with smaller nuisance dimension is Haar-null.
- `GaussianGenericity.gaussian_generic_evaluation_independence` proves the
  paper's simultaneous Gaussian evaluation-independence proposition on one
  Borel conull data set, for every distinct, possibly data-dependent location
  list with `k(d+1) <= n`. The full incidence projection is null; a measurable
  null hull gives the Borel exceptional set. The same data set gives full-
  probability-measure optimizer uniqueness whenever all extreme supports have
  at most `m` atoms and `2m(d+1) <= n`. Genericity holds almost surely under
  every data law absolutely continuous with respect to Lebesgue measure.
- `GaussianPaperScales` verifies the paper's actual logarithmic Taylor-order
  specialization. The Taylor rank is bounded by a constant times `r_n + log n`,
  the structural remainder decays faster than the required inverse power, and
  both scale conditions hold eventually for the balanced shape
  `(r_n + log n) log n` and for every tiny shape `n^(2L+2)`. The eventual
  uniqueness threshold is proved from `r_n + log n = o(n)`. Coordinate bounds
  are specialized to a constant over `sqrt(r_n + log n)` in the balanced regime
  and to the literal `n^(-L)` in the tiny regime. For `d >= 2`, `log n` is
  eventually absorbed by `r_n`; for `d = 1` the augmented dimension is at most
  `2 log n`.
- `GaussianExactRegularization.gaussian_exact_regularization_conditional_balanced`
  assembles the structural parts at the actual balanced concentration, on one
  Borel conull data set and conditional on the paper's sample-radius event.
  Weight-event failure is at most `3 n^(-b-2)`. The optimizer set over all
  probability measures is a singleton with finite support bounded by a fixed
  constant times `r_n + log n`. Weight, total ordinary likelihood gap, and
  literal squared log-density-ratio bounds hold against every ordinary NPMLE.
  The conditional tiny theorem gives uniqueness, the same support order,
  perturbation at most `n^(-L)`, and ordinary total near-MLE error at most one
  simultaneously against every comparison probability law.
- `CompactOptimizerEvents` proves that continuous compact optimization has a
  closed optimizer graph, and that optimizer nonuniqueness and strict optimizer-
  gap events are Borel via compact projections and countable thresholds.
  `ParameterizedProbabilityIntegral` proves joint continuity when both a weak
  probability law and a uniformly varying continuous integrand change. Gaussian
  fitted moments and weighted probability-law likelihoods are jointly continuous
  in data, weights, and laws, so their full-measure optimizer graph is closed.
  Small-support law sets are compact and closed. The corresponding Gaussian
  nonuniqueness, support, likelihood, and squared log-ratio failures are Borel
  jointly in observations and weights.
- `ConditionalProductBound` integrates uniform section bounds of one measurable
  joint event. `GaussianSampling` identifies the actual iid Gaussian-mixture law,
  proves its absolute continuity, and supplies a uniform sample-radius tail.
- `GaussianJointTheorems.gaussian_exact_regularization_joint_balanced_explicit`
  assembles all four main conclusions on one Borel joint data-and-weight event.
  Failure is at most `(4d+5) n^(-b-2)`, uniformly over the true mixing law.
  A Borel hull of the existing uniform near-MLE risk exception allows every
  comparison law to be controlled without assuming a measurable optimizer rule.
- `GaussianMainTheorem.gaussian_exact_regularization_main` gives the actual
  paper main theorem with one positive constant in all conclusions and failure
  at most `C n^(-b)`. The risk scale is proved exactly equal to the displayed
  `(log n)^(d+1) / [n (log log n)^d]`. `GaussianTinyJoint` and
  `gaussian_exact_regularization_tiny` give the tiny-perturbation corollary on one
  joint event, including literal perturbation `n^(-L)` and Hellinger risk.
- `GaussianJointConsistency.gaussian_reweighted_optimizer_weak_consistency`
  proves the paper weak-consistency corollary for any weighted-optimizer rule
  at positive weights. Every triangular experiment is a genuine probability
  law; an explicit shape-one convention only affects irrelevant small sample
  sizes. The theorem does not assume measurability of an optimizer selection.
- `GaussianApproxJointEvents` proves closedness and joint Borel measurability
  of failures involving a weighted optimizer, an ordinary optimizer, and an
  arbitrary approximate probability law. `GaussianApproxRegularization`
  transfers the abstract simultaneous bounds to actual Gaussian likelihoods
  and literal log-density ratios at tolerance `(1/6144) / log n`.
  `GaussianApproxTheorem.gaussian_approximate_optimizer_joint_robustness`
  proves the statistical robustness corollary on one joint Borel event,
  with common positive constant, uniform polynomial failure, and Hellinger
  risk for every attainable approximate law. No sparsity assumption or
  conclusion is imposed on approximate laws.
- `GaussianProbabilityWidth.gaussian_probability_relative_width_bound` gives
  the literal arbitrary-reference Gaussian probability-law width proposition.
  The projection subspace has the exact paper rank and contains `one`; density
  ratios are actual Gaussian mixtures of arbitrary probability laws. The exact
  Taylor residual is zero when `ST=0`.

## Latest closed interfaces

- `GaussianConditionalTheorem`: every deterministic dataset with arbitrary
  `C₀ sqrt(log n)` radius, without genericity or correct specification.
- `PopulationCriterion` and `PopulationKL`: actual joint data/Gamma criterion
  equality for raw and normalized weights; genuine mathlib KL gap and
  unchanged density-law target.
- `FullSupportSensitivity`: actual second Fréchet derivative and simultaneous
  orthogonal projections for every full-law extreme optimizer on one conull
  set, including the attained maximal-support rank.
- `GaussianPaperFiniteNet`: actual deterministic internal finite law net,
  literal entropy order, `H <= n^-3`, uniform log error `<= n^-3`, radius
  `O(sqrt(log n))` and uniform tail `<= n^(-b-2)` without a prefactor.
- `PaperRegularity`: both canonical fitted maps locally Lipschitz, optimized
  value globally convex and continuously differentiable, and compact/nonempty/intrinsically convex
  full-law optimizer fibers with all-law fitted-vector agreement.
- `PaperLocalization`: the literal compact localization event, strict log
  displacement `<1/8`, sharp radial constants, nonnegative exact `Z`, and the
  determinant moment for the actual maximum full-law support statistic.
- `GaussianSupportRefinements` and `GaussianNearMLETheorem`: direct dimension
  support-order refinements and common-positive-constant uniform near-MLE
  theorem with the literal displayed rate.
- `EmpiricalDirichletTV`: merged distinct-observation masses cover repeated
  observations; the sharp expected TV bound and its identification with actual
  finite empirical probability-law singleton differences compile.

## Numerical and experimental correspondence

### Newly verified numerical interfaces

- `NumericalTable` certifies all 48 table means and 42 parenthesized standard
  errors at half the last displayed decimal unit. Means and squared standard
  errors are recomputed from all 3840 recorded sample values in the 48 table
  cells, using kernel-checked exact rational arithmetic. A square-root interval
  theorem converts squared-error certificates to actual standard errors.
- `NumericalReports` certifies all eight rounded range extrema, the balanced
  average risk ratio `1.013`, support agreement `90.3%`, and precision of the
  four recorded regression coefficients. A separate theorem proves the exact
  pattern of six failed literal ranges and two valid literal ranges.
- All 12 displayed path medians/quantiles (including balanced/tiny risks,
  likelihood losses, distances, Wasserstein median and BB 90th-percentile
  support) are verified against the raw CSV samples. Every sorting permutation
  contains all 30 draw indices; reordered samples and their pairwise ordering
  are checked, followed by exact linear-interpolation quantile arithmetic.
- `NumericalKKT` identifies the residual with the literal normalized weighted
  sum in the paper and proves nonpositivity at every genuine full-law optimizer.
- `NumericalLogBounds` proves atanh-series and power-of-two range-reduced
  logarithm enclosures, including rational-to-real cast identities and a sound
  finite certificate interface for positive arguments and their reciprocals.
- `NumericalScaledReports` certifies every sample-size logarithm and the actual
  real minimum and maximum of the likelihood/log-fit means multiplied by
  `log n`, at half the last displayed decimal unit. The likelihood maximum
  exceeds `0.532` literally (approximately `0.532280`), while rounding to it.
  The log-fit values satisfy the literal `[0.479,0.928]` bounds.
- `NumericalDiagnostics` contains the tighter all-fit, one-dimensional and
  multistart maximum checks against recorded rational diagnostics, detailed
  design/draw counts, and path baseline precision. The full module and integrated
  audit pass. Its checks use all 4160 raw rational residual/gap records, not
  precomputed diagnostic flags. It verifies the balanced support counts `28`
  three-atom and `2` four-atom draws, explicitly refutes all-three balanced
  support, and proves that every tiny draw has three atoms.

- `NumericalRegressionReports` recomputes all four log-log regression slopes
  from the 1680 raw path responses at all 14 eligible alpha values. Sorting
  permutations and ordering certify each 30-draw median; proved real logarithm
  enclosures and sound exact rational interval arithmetic certify the actual
  slopes at half the last printed decimal unit. The variance denominator is
  proved positive, and the slope/intercept pair globally minimizes the actual
  least-squares error. These proofs do not use the JSON regression coefficients
  as an oracle.
- `NumericalSummaryReports` recomputes the whole-design summaries from 8280
  rational risk/distance/likelihood/log-fit inputs and 3680 integer support
  counts. All 11 cells, 920 paired replications, replication indices and input
  lengths are checked. Exact mean/ratio equalities connect all eight range
  reports, the balanced average, support agreement and real log-scaled extrema
  to these raw inputs. Rational means are identified with actual real sample
  means; the abstract's cellwise risk comparison within `2.1%` is proved.
- `NumericalDesigns` defines genuine three-point, Lebesgue-uniform and
  four-corner probability laws with the literal paper locations and masses.
  The parameter boxes are compact and nonempty; all laws are concentrated
  in the stated boxes and their Gaussian densities integrate to one. Atomic
  locations are injective and singleton masses are proved. The uniform law
  assigns zero mass to every singleton. Tiny concentration `n^3` is exactly
  the `L=1/2` specialization; average-one weight normalization is exactly
  `nP`, has total `n`, and leaves likelihood maximizers unchanged.

## Reconciled numerical source

The false all-balanced-draws assertion and original range semantics have been
corrected with author approval. The whole-design raw-sample linkage and
experimental definitions are compiled and integrated.
`COMPLETION_AUDIT.md` records the source/type completion checks;
`PROPOSED_NUMERICAL_CORRECTIONS.md` preserves the approved proposal, and
`docs/NUMERICAL_CORRECTIONS_NOTE.md` separately records the applied changes.

`python3 scripts/generate_numerical_data.py --check` confirms exact
reproduction of all three current generated Lean artifacts from all six source files.
Adding `--audit-numerics` uses exact rational CSV arithmetic to test the paper's
original printed ranges. Six of eight ranges fail if interpreted as literal exact bounds;
see `PAPER_COVERAGE.md`; this failure pattern and all eight rounded extrema are
now also kernel-checked in Lean. Existing broad-range certificates are not counted as
proofs of narrower printed intervals. The corrected source explicitly reports
rounded minimum and maximum cell summaries instead. The historical FAIL labels
are retained as an audit of the original enclosing-bound interpretations,
not failures of the corrected statements. No raw numerical source was changed.

`Check.lean` is an excluded, preexisting scratch file, not imported by either
production target; its existing experiments are retained. Production scanning
finds no proof placeholders or project axiom declarations.

The original formalization's Mac keep-awake process was stopped at completion.
It is not a dependency of this standalone package. `PUBLICATION.md` documents
the clean export and manual publication workflow; bundled reference material
and optional certificate inputs require no parent checkout.
