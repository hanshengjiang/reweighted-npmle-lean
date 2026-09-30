# Release statement-coverage review — 29 September 2026

This is an additional source-level mathematical interface review. It compares the **18 named theorem, proposition, lemma and corollary blocks in the frozen original `paper.tex`** with actual Lean declarations, and compares those blocks with versions 2 and 3. It supplements, rather than replaces, the [complete main-result statement audit](../main-result-2026-09-29/README.md). All declaration names below are in namespace `ReweightedNPMLE`.

**Outcome:** the inspected interfaces supply the substantive conclusions of all 18 original blocks under their surrounding setup. The package is suitable as a research companion with the qualifications below. This review does **not** support describing every wrapper type as a literally identical transcription of its paper block, or claiming every definitional equivalence to a conventional mathematical term has a separate theorem.

No Lean source or manuscript was edited by this review. No build, `lake env lean`, or `#print axioms` command was run by this reviewer; release build and axiom evidence is recorded separately. This review read theorem types, relevant definitions, and selected proof dependencies; it was not a line-by-line independent proof audit of every module.

## Qualifications that should accompany coverage claims

### 1. Tiny perturbations: use the explicit theorem for constant dependencies

The paper uses a failure/risk constant `C_b`, allowing the support constant `C_{b,L}` to depend on `L`. The convenient wrapper [GaussianMainTheorem.lean](../../ReweightedNPMLE/GaussianMainTheorem.lean), `gaussian_exact_regularization_tiny` (line 105), has

```lean
{S b L : ℝ} ... (hL : 0 < L) ... :
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ Gstar : ProbabilityMeasure K, ...
```

and uses this single `C` for probability, support and risk. Its witness is `1 + B + R + F`, where `B` depends on `L`. **That wrapper alone permits more constant dependence than the manuscript.** This is a weaker exported common-constant interface, not an unproved stronger conclusion.

The underlying proved declaration [GaussianTinyJoint.lean](../../ReweightedNPMLE/GaussianTinyJoint.lean), **`gaussian_exact_regularization_joint_tiny_explicit`** (line 130), supplies the manuscript's dependence separation:

```lean
(gaussianDataWeightMeasure Gstar n ((n : ℝ) ^ (2 * L + 2))).real Gᶜ ≤
  (4 * (d : ℝ) + 5) * (n : ℝ) ^ (-(b + 2))
...
((μ : Measure K).support.ncard : ℝ) ≤
  gaussianPaperSupportConstant d (8 * (2 * L + 6)) b *
    gaussianPaperAugmentedDimension d n
...
hellingerSq volume (compactGaussianMixtureDensity μ)
  (compactGaussianMixtureDensity Gstar) ≤
    gaussianPaperRateConstant d b * gaussianPaperLogScale n ^ d * Real.log n / n
```

The definitions checked are:

```lean
-- GaussianExactRegularization.lean:98
noncomputable def gaussianPaperSupportConstant (d : ℕ) (C b : ℝ) : ℝ :=
  10000000 * (1 + (4 * C + 1) ^ d + (b + 4))

-- GaussianNearMLERate.lean:1142–1147
noncomputable def gaussianPaperEntropyConstant (d : ℕ) : ℝ :=
  17 * ((d : ℝ) + 1) * ((1025 : ℝ) ^ d + 1)
noncomputable def gaussianPaperRateConstant (d : ℕ) (b : ℝ) : ℝ :=
  22 + 4 * (gaussianPaperEntropyConstant d + b + 4)
```

Thus failure and risk coefficients are independent of `L`; the support coefficient and eventual sample threshold may depend on `L`. The explicit theorem even gives the smaller failure order `n^{-(b+2)}`. It should be cited as the primary interface for the literal `cor:tiny` constant dependencies, with the wrapper cited as a convenience.

### 2. Conditional bounds: make fixed-radius dependence and eventual sample size explicit in future writing

[GaussianConditionalTheorem.lean](../../ReweightedNPMLE/GaussianConditionalTheorem.lean), `gaussian_conditional_structural_and_likelihood_bounds` (line 66), chooses `C` and the eventual sample threshold after the fixed radius coefficient `C₀`:

```lean
{d : ℕ} (hd : 0 < d) {S b C₀ : ℝ} ... :
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ x : Fin n → Point d,
    (∀ i, ‖x i‖ ≤ C₀ * Real.sqrt (Real.log (n : ℝ))) → ...
```

Its proof explicitly takes `b' := b + C₀ ^ 2 + 4`. Therefore the formal result permits `C₀` dependence in the displayed constant, while remaining uniform over every dataset satisfying that fixed radius bound. Reading the original paper's “Fix ... C₀” as allowing such dependence is natural. However, the new notation paragraph in v2/v3 says subscripts indicate additional dependence. Under a strict reading of that convention, the displayed `C_b` does not advertise its `C₀` dependence. A future manuscript should say `C_{b,C₀}`, or explicitly permit dependence on all fixed parameters of each local statement. This review has not proved an alternative theorem with `C` uniform over `C₀`.

The formal result holds for **all sufficiently large `n`**, with threshold uniform over eligible datasets. The printed `cor:conditional` does not repeat that qualifier; it is inherited from the scales and asymptotic discussion. Likewise `cor:approx` uses the setting of the eventual main theorem. These results must not be advertised as formal all-sample-size guarantees. The `thm:near-mle` block names `n₀` but does not explicitly attach “`n ≥ n₀`” to its probability sentence; Lean makes the intended eventual quantifier precise.

### 3. Dirichlet and total variation have explicit project definitions

[DirichletDistribution.lean](../../ReweightedNPMLE/DirichletDistribution.lean), lines 26 and 79, defines:

```lean
noncomputable def gammaWeightMeasure (n : ℕ) (α : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n ↦ gammaMeasure α α)
noncomputable def symmetricDirichletMeasure (n : ℕ) (α : ℝ) : Measure (Fin n → ℝ) :=
  (gammaWeightMeasure n α).map normalize
```

This is the usual normalized-independent-Gamma construction of the symmetric Dirichlet law. Equality with a **separately specified simplex-density definition** of Dirichlet is not proved here. The representation equality `normalized_gamma_has_symmetricDirichlet_law` is consequently `rfl`. Independence from the total, the total's Gamma law, and the displayed moment formulas are genuinely proved; they are not consequences supplied as hypotheses of the final interfaces.

[EmpiricalDirichletTV.lean](../../ReweightedNPMLE/EmpiricalDirichletTV.lean) defines the empirical deviation as

```lean
(1 / 2 : ℝ) * ∑ y ∈ empiricalObservationSet x,
  |∑ i, if x i = y then p i - 1 / n else 0|
```

and proves equality with half the sum of absolute singleton-mass differences between the actual empirical probability laws (`empiricalDirichletTV_eq_half_sum_actual_atom_mass_differences`). Repeated observations are merged correctly. This is the ordinary finite-atomic total variation distance. The package does not separately identify this expression with a library definition using a supremum over measurable sets; a claim that such a library-identity theorem was checked would overstate the evidence.

### 4. Existence and measurability are sometimes supplied by other declarations

The main theorem and tiny theorem explicitly export existence and singleton equality for a full optimizing probability law. Conditional and approximate interfaces quantify over exact optimizers without exporting a separate existence conjunct. Existence is available from the proved compact-fiber construction: [PaperRegularity.lean](../../ReweightedNPMLE/PaperRegularity.lean), `paper_full_optimizer_fiber_geometry`, and [ProbabilityOptimizerFiber.lean](../../ReweightedNPMLE/ProbabilityOptimizerFiber.lean), `probability_optimizer_exists`. Ordinary optimizer existence is also constructed in `gaussian_optimizer_nearMLE_of_likelihood_bound` in [GaussianJointStructural.lean](../../ReweightedNPMLE/GaussianJointStructural.lean), and was compiled as a separate semantic check in the main audit. The universal comparisons are not empty-set loopholes.

The statistical results provide measurable good subsets on which all indicated conclusions hold. They do not uniformly export measurability of the entire set described by every conjunction, or a globally measurable optimizer-selection map. `cor:weak` is formalized for any selection rule maximizing at positive weights, using outer-probability failure on arbitrary preimages; no measurability assumption on that rule is imposed. This is a strong meaningful convergence statement, but does not itself construct a measurable estimator.

## Clause coverage for all 18 original statement blocks

| Original label | Actual declarations and file | Independent interface check |
| --- | --- | --- |
| `prop:dirichlet` | `gammaWeight_normalize_total_joint_law`, `gammaWeight_normalize_indep_total` — [DirichletIndependence.lean](../../ReweightedNPMLE/DirichletIndependence.lean); `symmetricDirichlet_weighted_empirical_mean` — [DirichletDistribution.lean](../../ReweightedNPMLE/DirichletDistribution.lean); `symmetricDirichlet_weighted_empirical_variance` — [DirichletSecondMoment.lean](../../ReweightedNPMLE/DirichletSecondMoment.lean); `empiricalDirichlet_expected_tv_le` — [EmpiricalDirichletTV.lean](../../ReweightedNPMLE/EmpiricalDirichletTV.lean); `compactGaussianMixture_unchanged_population_criterion` — [PopulationCriterion.lean](../../ReweightedNPMLE/PopulationCriterion.lean); `compactGaussianMixture_population_gap_eq_klDiv` — [PopulationKL.lean](../../ReweightedNPMLE/PopulationKL.lean) | Positive shape and `n>0`; exact joint product law; arbitrary finite real target; variance denominator `nα+1`; correct half-TV factor and repeated points; actual iid-data/Gamma product integrals for raw and normalized weights. Only candidate-log integrability is assumed. True-log integrability and finite genuine mathlib KL are derived in the proof, and zero gap iff density-law equality is exported. Definition qualifications above apply. |
| `thm:main` | `gaussian_exact_regularization_main` — [GaussianMainTheorem.lean](../../ReweightedNPMLE/GaussianMainTheorem.lean); `gaussian_main_support_dimension_refinements` — [GaussianSupportRefinements.lean](../../ReweightedNPMLE/GaussianSupportRefinements.lean) | Main wrapper type re-read; full detailed comparison remains in the main audit. One constant and eventual threshold precede every true mixing law; one joint measurable event supplies singleton existence, finite actual support, coordinate deviations, all ordinary-NPMLE comparisons, and global risk. Dimension refinements are separate. |
| `cor:tiny` | **`gaussian_exact_regularization_joint_tiny_explicit`** — [GaussianTinyJoint.lean](../../ReweightedNPMLE/GaussianTinyJoint.lean); common-constant wrapper `gaussian_exact_regularization_tiny` — [GaussianMainTheorem.lean](../../ReweightedNPMLE/GaussianMainTheorem.lean) | Literal shape `n^(2L+2)`, literal `n^(-L)` coordinate deviations, uniqueness and finite support. The explicit theorem, not the wrapper alone, verifies the split constant dependence; see above. Threshold precedes `Gstar`. |
| `cor:weak` | `gaussian_reweighted_optimizer_weak_consistency` — [GaussianJointConsistency.lean](../../ReweightedNPMLE/GaussianJointConsistency.lean) | Every neighborhood in weak `ProbabilityMeasure K` topology has failure tending to zero for every optimizer rule on positive weights. Experiment is actual data × Gamma product; shape is replaced by 1 only at finitely many irrelevant small sizes where the logarithmic shape is nonpositive. Uses outer probability; selection measurability/existence not exported by this theorem itself. |
| `thm:effective` | `effective_dimension_full_support` — [FullEffectiveDimension.lean](../../ReweightedNPMLE/FullEffectiveDimension.lean) | Same nonempty compact metric parameter space, continuous strictly positive dictionary, its actual convex hull, ordinary optimum and relative width. A rank **at most** `r` subspace is enough (slightly stronger than exact-rank assumption). Universal `C=10000000`, `c=1/3072`; exact `Q=q+log(2n)` and width scale. One measurable weight event; support maximum attained; actual full extreme-law support finite; both exact losses and every `τ<c` attainable approximate vector handled simultaneously. No differentiability or determinant-moment premise is left assumed. |
| `lem:hessian-summary` | `full_support_sensitivity_ae` — [FullSupportSensitivity.lean](../../ReweightedNPMLE/FullSupportSensitivity.lean) | One dictionary-dependent conull set before all laws. Actual second Fréchet derivative, Hermitian idempotent `P`, rank `s_ext−1`, and positive-semidefinite difference are conclusions. The hull-equality assumptions identify the maximum statistic, rather than postulating a finite optimizer support. |
| `prop:gaussian-width` | `gaussian_probability_relative_width_bound`, `gaussianTaylorResidual_eq_zero_of_mul_eq_zero` — [GaussianProbabilityWidth.lean](../../ReweightedNPMLE/GaussianProbabilityWidth.lean) | Arbitrary reference probability law before projection; projection before every candidate law. Rank `≤1+choose(m+d,d)`, range contains one, literal full-mixture ratios and Taylor residual. `ST=0` gives zero. Compactness/nonemptiness are inherited from the paper's standing setup; the formal theorem even allows `d=0` and `n=0`. |
| `cor:conditional` | `gaussian_conditional_structural_and_likelihood_bounds` — [GaussianConditionalTheorem.lean](../../ReweightedNPMLE/GaussianConditionalTheorem.lean) | Every deterministic dataset meeting the radius bound; no genericity, sampling law or correct specification. Same event gives extreme-support and coordinate bounds and comparisons for every weighted and every ordinary optimizer. `C₀` dependence and eventual-n interpretation need the clarification above. |
| `prop:generic` | `gaussian_generic_evaluation_independence`, `gaussian_generic_optimizer_fiber_uniqueness` — [GaussianGenericity.lean](../../ReweightedNPMLE/GaussianGenericity.lean) | Borel conull dataset chosen before every `k` and injective location list. Exact `k(d+1)≤n`; locations may depend on data. Full-law uniqueness theorem uses exact `(2*m)*(d+1)≤n`, every extreme optimizer, exports singleton existence, extremality, support finiteness and `≤m`. Parameterization injectivity is satisfied by the inclusion of `K`; it prevents artificial duplicate latent parameters. |
| `thm:near-mle` | `gaussian_uniform_nearMLE_paper_theorem` — [GaussianNearMLETheorem.lean](../../ReweightedNPMLE/GaussianNearMLETheorem.lean) | One positive constant and eventual sample threshold before all true laws; one Borel data event before all candidate laws. Near-truth likelihood gap exactly 1, no atomicity or optimizing premise, literal Hellinger rate. `n₀` is represented by eventuality. |
| `cor:approx` | `gaussian_approximate_optimizer_joint_robustness` — [GaussianApproxTheorem.lean](../../ReweightedNPMLE/GaussianApproxTheorem.lean) | Fixed `c₀=1/6144` via `gaussianPaperApproxTolerance`; total weighted log-likelihood gap; every attainable probability law on one measurable joint event and every ordinary optimizer comparator. Any smaller nonnegative gap is included by the displayed maximum-tolerance implication. Literal likelihood/log-fit rate and global Hellinger bound, no approximate support claim or finite-atomic premise. Optimizer existence is supplied separately as above. |
| `lem:regularity` | `positive_kernel_hull_properties` — [FullEffectiveDimension.lean](../../ReweightedNPMLE/FullEffectiveDimension.lean); `canonical_fitted_value_convexOn_univ`, `canonical_fitted_maps_locally_lipschitz`, `canonical_fitted_value_contDiffOn_one`, `paper_full_optimizer_fiber_geometry` — [PaperRegularity.lean](../../ReweightedNPMLE/PaperRegularity.lean); `canonicalFittedOptimalValue_hasFDerivAt_of_positive_weights` — [FittedEnvelope.lean](../../ReweightedNPMLE/FittedEnvelope.lean) | Compactness and positivity derived from dictionary; global convexity of the optimized value (stronger than positivity-domain convexity); C¹ on positive orthant; local Lipschitz neighborhoods for both actual fitted maps. Envelope derivative is the fitted-log functional. Every maximizing law iff it is in the fitted fiber. |
| `lem:extreme` | `paper_full_optimizer_fiber_geometry` — [PaperRegularity.lean](../../ReweightedNPMLE/PaperRegularity.lean); `full_probability_optimizer_extreme_iff`, `full_extreme_optimizer_support_finite_card_le` — [FullExtremeSupport.lean](../../ReweightedNPMLE/FullExtremeSupport.lean); `measurable_maximumExtremeSupport`, `canonical_maximumExtremeSupport_attained` — [MeasureExtremeSupport.lean](../../ReweightedNPMLE/MeasureExtremeSupport.lean) | Nonempty compact fiber, convex probability combinations; extremality iff finite positive weights on distinct atoms with linearly independent evaluations. Finiteness and `≤n` are conclusions for arbitrary full laws, not candidate restrictions. Statistic is Borel and maximum attained, with extension zero outside positive weights. |
| `lem:matrix-sensitivity` | `full_extreme_optimizer_hessian_projection`, `full_support_sensitivity_ae` — [FullSupportSensitivity.lean](../../ReweightedNPMLE/FullSupportSensitivity.lean) | Pointwise inequality requires an actual derivative of fitted log `z`; a.e. existence of that derivative is proved from local Lipschitz regularity, and envelope theorem makes its matrix the Hessian. Same conull set works for every extreme law; rank `support.ncard−1`. See v2/v3 wording discussion below. |
| `lem:radial` | `isCompact_paperRadialEvent`, `paper_radial_localization`, `canonical_paper_radial_exact_fit` — [PaperLocalization.lean](../../ReweightedNPMLE/PaperLocalization.lean) | Literal event at `ρ=1/16`, compactness, strict relative norm `<ρ`, log coordinates `<1/8`; constants `36/12/12`, `37/13/13`, `72/24/24`. The formal approximate premise compares to the ordinary reference's weighted value, which is **weaker** than τ-optimality and therefore strengthens the implication. Exact `Z≥0` and its upper bound are exported separately. |
| `lem:determinant-moment` | `canonical_maximumExtremeSupport_paper_gamma_moment` — [PaperLocalization.lean](../../ReweightedNPMLE/PaperLocalization.lean) | Actual full-law support statistic, literal radial event, base `17/9`, negative exponent and squared log displacement. Restricted nonnegative integral is the indicator expectation. Natural-number subtraction `s_ext−1` is legitimate on positive weights because the maximum is at least 1. Moment bound is proved through canonical regularity, support sensitivity and change of variables; no moment bound hypothesis. |
| `lem:finite-net` | `compactGaussianMixture_simultaneous_paper_finite_net` — [GaussianPaperFiniteNet.lean](../../ReweightedNPMLE/GaussianPaperFiniteNet.lean) | Positive constant and eventual threshold before deterministic nonempty finite set of actual probability-law densities and radius. Both chosen before true/candidate laws. Literal entropy, `T≤C sqrt(log n)`, uniform failure `≤n^{−b−2}` without prefactor, `sqrt(H²)≤n^{−3}`, uniform log error `≤n^{−3}`. No restricted atomic candidate domain. |
| `lem:gamma-concentration` | `gamma_coordinate_concentration` — [GammaDistribution.lean](../../ReweightedNPMLE/GammaDistribution.lean) | Actual shape-rate Gamma law, `a>0`, `0<t≤1`, scalar absolute deviation with strict tail `>t`, constant 2 and exponent `−at²/4`. Endpoint `t=1` is separately proved and included. |

Throughout these interfaces, `[MeasurableSpace Θ] [BorelSpace Θ]` means the Borel sigma-algebra on the indicated compact metric parameter space; it is not an extra probabilistic regularity assumption. `[Nonempty (Fin n)]` is `n>0`, consistent with a nonempty sample. Gaussian subtype `K` gets these structures from Euclidean space. Nonnegative `S` follows from a nonempty set bounded by radius `S`; formal closed-ball inequalities are compatible with the original bounded-compact setup, and v2/v3 explicitly define `B(0,S)` as closed.

## Versions 2 and 3: checked differences, not label-based inference

A Python extraction of complete `theorem`, `lemma`, `proposition` and `corollary` environments followed by whitespace normalization gave:

```text
paper.tex:    18 named blocks
paper_v2.tex: 17 named blocks
paper_v3.tex: 17 named blocks
v2 and v3 named statement blocks equal after whitespace normalization: True
Original labels absent in v2/v3: ['lem:matrix-sensitivity']
```

The removed matrix-sensitivity block is **merged into `lem:hessian-summary`**, whose statement is expanded. It is therefore inaccurate to describe all three versions as having exactly the same theorem labels, or every theoretical statement as verbatim identical.

Other changes were inspected: `P_i,T_W` become `π_i,W_+`; `s_ext` becomes the `\sext` macro; `A₀,B₀` become `ω_P,ω`; several standing model assumptions are replaced with `ass:standing`. The corresponding definitions and standing assumption were read: they retain the same compact nonempty bounded Gaussian setting, norms, and radius `ρ=1/16`. The four main-theorem conclusions and tiny-corollary block have no substantive alteration.

The expanded v2/v3 support-sensitivity statement says the inequality holds **at each point where the Hessian exists**, for every extreme optimizer. The a.e. wrapper alone is not that pointwise statement. The relevant stronger declaration is `full_extreme_optimizer_hessian_projection` in [FullSupportSensitivity.lean](../../ReweightedNPMLE/FullSupportSensitivity.lean), whose only differentiability premise is:

```lean
{J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
(hz : HasFDerivAt (fittedLogSelection C hCcompact hCnonempty hCpos) J w)
```

The envelope theorem above identifies `z` with the gradient of `Ψ` throughout an open neighborhood of every positive weight. Consequently differentiability of `z` is the usual existence of that Hessian, and the pointwise theorem covers the expanded mathematical assertion under this interpretation. This review did **not** compile a new wrapper whose sole premise is differentiability of `fderiv Ψ`; the source already proves the pointwise gradient-derivative formulation and the actual second-derivative identification in the a.e. theorem. If “Hessian exists” meant merely the existence of all second coordinate partial derivatives without Fréchet differentiability of the gradient, that would be a different claim not checked here.

Only named statement blocks and their needed setup were compared between drafts. This is not a claim that all proofs, numerical prose, citations, or exposition of v2/v3 were independently audited. Future v4/v5 edits should be checked against this frozen statement snapshot, especially changes to quantifiers, probability experiments, optimizer domains, constant dependencies, and “Hessian exists” wording.

## Intermediate mathematics and verification limits

The final interfaces do not take the geometric moment inequality, generic evaluation independence, entropy/net theorem, Hellinger transfer theorem, identifiability, or finite-support characterization as unproved hypotheses. They call proved declarations. In particular, this review followed `effective_dimension_full_support` into `effective_dimension_finite_support`, and the moment interface into `canonical_maximumIndependentSupport_gamma_moment` / `canonical_gamma_determinant_moment` in [FittedDeterminantMoment.lean](../../ReweightedNPMLE/FittedDeterminantMoment.lean); the analytic and change-of-variables inputs are derived there. The near-MLE and tiny joint declarations supply their full probability/risk conclusions without additional mathematical premises beyond their printed model conditions.

Some lower-level reusable lemmas legitimately accept hypotheses such as a derivative, a finite extreme representation, covariance identities, an approximation width, or likelihood maximization. It would be misleading to audit one such conditional lemma as the final paper result. The source review checked that the cited final interfaces discharge the extra intermediate conditions. Definition choices for Dirichlet, empirical total variation, support and optimizer fibers remain part of the semantic trust boundary described above.

This review ran only read-only source commands (`rg`, `sed`, `cat`) and Python extraction/comparison, and wrote this release report. It did not run Lean compilation or axiom commands, certify the numerical solvers, prove estimator-selection measurability, or produce independent hand proofs of the entire mathematics. Fresh build and axiom reports elsewhere in this release must be cited for those actual checks, without treating successful compilation as a semantic statement-matching proof.

## Frozen sources reviewed

The SHA-256 values were calculated directly from the current original manuscript sources; the release copies should match them:

```text
4166c2e5db94f7fd267b79a97e3ef6ed7803709a3ea3a9ce2fc603002b76f385  paper.tex
e12d130e9da64c030ce6f394dbd8cae269c6f76e27de4470bc14908c21020762  paper_v2.tex
8ffa46f93551b73169fae3e1c518a62d612ce4ab7ec7b5abcbcc17226cc9ec64  paper_v3.tex
```

Frozen manuscript copies: [original](../../docs/manuscript/paper.tex), [v2](../../docs/manuscript/paper_v2.tex), [v3](../../docs/manuscript/paper_v3.tex). The review treats the original as the primary mathematical specification and v2/v3 as subsequent writing snapshots.
