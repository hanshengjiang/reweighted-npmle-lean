# Statement audit: main exact-regularization theorem

Audit date: 29 September 2026. Repository commit: `e8bf8f2832b3d3dfb94ebdf3e9d718ad3434eeb4`.

**Later verification addendum:** the [Comparator audit](../comparator/README.md)
adds a separate Mathlib-only challenge, successful Comparator comparison,
Nanoda independent-kernel checking, and Lean replay. The original commands and
scope below remain historical. The additional Mac run was unsandboxed.

**Finding:** the Lean main theorem matches the four displayed clauses of the manuscript's `thm:main`, with the correct uniformity and quantifier order. I found no stronger substantive hypothesis, restricted finite mixing-law domain, weakened displayed conclusion, inappropriate constant dependence, or intermediate mathematical result left assumed in this theorem. The formalization sources were not changed.

The exported-interface qualifications are precise: ordinary-NPMLE existence is proved in dependencies rather than exported as a separate conjunct of the main type; the dimension-specific support orders have a separate corollary; and the main type supplies a measurable good subset with pointwise unique optimizer existence. It does not separately assert measurability of the entire set defined by the four properties, or a global measurable estimator selection. These preserve the usual quantitative “with high probability” reading of the manuscript; a demand for exact-property-event measurability would be an additional claim not exported by this type.

## Reproducing the successful helper checks in this package

The mathematical audit below is the original 29 September report. Release preparation changed its navigation links and helper paths, not its mathematical conclusions or raw logs. Local source links resolve within this package; mathlib links identify the exact pinned dependency revision. The original manuscript is frozen at [docs/manuscript/paper.tex](../../docs/manuscript/paper.tex), with versions 2 and 3 alongside it. Later editorial manuscript revisions do not retroactively change this comparison target.

From the package root, first complete the build instructions in [the package README](../../README.md). Then run:

```sh
mkdir -p .audit-rerun
lake env lean audit/main-result-2026-09-29/StatementAudit.lean > .audit-rerun/statement-print.log 2>&1
lake env lean audit/main-result-2026-09-29/FullType.lean > .audit-rerun/full-type.log 2>&1
lake env lean audit/main-result-2026-09-29/SemanticChecks.lean > .audit-rerun/semantic-checks.log 2>&1
lake env lean Verification.lean > .audit-rerun/verification.log 2>&1
python3 audit/main-result-2026-09-29/check_axiom_output.py --log .audit-rerun/verification.log
python3 audit/main-result-2026-09-29/compare_manuscripts.py
python3 audit/main-result-2026-09-29/verify_sources.py
```

These are rerun instructions, not additional historical command claims. Each Lean command must exit successfully; redirection alone does not establish success. Omitting `--log` from the axiom parser checks the preserved historical log rather than rerunning Lean. The `.initial.lean` files and `historical/` scripts document failed or machine-specific audit attempts; they are not production imports and are not part of the commands above.

The historical fingerprint manifest covers 120 files from the author's original formalization directory. The portable `verify_sources.py` verifies only the **112 production Lean sources plus the toolchain and dependency manifest** against their historical hashes. It explicitly excludes the omitted scratch file `Check.lean` and the five manuscript/data/package-metadata entries outside this narrowed source check. It does not claim a fresh 120-file check or validate edited release documentation. The original 120-file result and script remain preserved for provenance.

## 1. Exact target and manuscript provenance

**Fully qualified name:** `ReweightedNPMLE.gaussian_exact_regularization_main`.

**Declaration:** [GaussianMainTheorem.lean](../../ReweightedNPMLE/GaussianMainTheorem.lean#L56), lines 56–74 (proof follows through line 102). The containing namespace is `ReweightedNPMLE`.

The comparison target is “Exact regularization by random reweighting,” label `thm:main`, at [paper.tex](../../docs/manuscript/paper.tex#L373), lines 373–409, with model/weight/scale definitions in the preceding section. I also compared [paper_v2.tex](../../docs/manuscript/paper_v2.tex#L362), [paper_v3.tex](../../docs/manuscript/paper_v3.tex#L373) and the formalization's [paper.tex](../../docs/paper.tex#L355). The main theorem in `paper.tex` and the bundled snapshot is textually identical. Versions 2 and 3 replace the opening assumption sentence with a reference to their explicit standing assumption; their conclusions and constant quantifiers are identical. The standing assumptions still say positive integer dimension, nonempty compact K in a bounded Euclidean ball. Version 3 explicitly defines B(0,S) as the closed ball.

This audits the current reweighted-NPMLE main theorem, not the distinct historical development under `archived/`. Exact extraction diffs and manuscript SHA-256 hashes are in [manuscript-comparison.log](manuscript-comparison.log).

## 2. Complete formal type and all assumptions

Here is the complete source type, without its proof body. No binder or hypothesis has been omitted:

```lean
theorem gaussian_exact_regularization_main
    {d : ℕ} (hd : 0 < d) (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S b : ℝ} (hS : 0 ≤ S) (hb : 0 < b) (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ Gstar : ProbabilityMeasure K,
      ∃ G : Set (GaussianDataWeight d n), MeasurableSet G ∧
        (gaussianDataWeightMeasure Gstar n (gaussianPaperBalancedShape d n)).real Gᶜ ≤
          C * (n : ℝ) ^ (-b) ∧
        ∀ p ∈ G, (∀ i, |p.2 i - 1| ≤ C / Real.sqrt (gaussianPaperAugmentedDimension d n)) ∧
          p.2 ∈ positiveVectors n ∧ ∃ μ : ProbabilityMeasure K,
            gaussianProbabilityOptimizerSet (fun a : K ↦ (a : Point d)) p = {μ} ∧
            (μ : Measure K).support.Finite ∧ ((μ : Measure K).support.ncard : ℝ) ≤
              C * gaussianPaperAugmentedDimension d n ∧
            (∀ μ₀ ∈ gaussianProbabilityOptimizerSet (fun a : K ↦ (a : Point d)) (p.1, 1),
              0 ≤ gaussianOrdinaryLikelihoodGap (fun a : K ↦ (a : Point d)) (p, (μ, μ₀)) ∧
              gaussianOrdinaryLikelihoodGap (fun a : K ↦ (a : Point d)) (p, (μ, μ₀)) ≤ C / Real.log n ∧
              gaussianSquaredLogRatioGap (fun a : K ↦ (a : Point d)) (p, (μ, μ₀)) ≤ C / Real.log n) ∧
            hellingerSq volume (compactGaussianMixtureDensity μ) (compactGaussianMixtureDensity Gstar) ≤
              C * gaussianPaperRiskScale d n
```

The imports and namespace context are:

```lean
import ReweightedNPMLE.GaussianTinyJoint
import Mathlib.Tactic
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal
namespace ReweightedNPMLE
```

There are **no surrounding `variable` declarations, section assumptions, or typeclass binders** on this theorem. Its implicit parameters are exactly `{d : ℕ}` and `{S b : ℝ}`. The explicit assumptions are `hd`, `hKcompact`, `hKnonempty`, `hS`, `hb`, `hKbound`; `K` itself is an explicit parameter. The theorem has no free universe parameter: the ambient space and its subtype live in `Type 0`.

The Euclidean metric/norm, Borel measurable structure, subtype structures on K, and Lebesgue measure on `Point d` are concrete inferred instances, not additional caller-supplied assumptions. `ProbabilityMeasure K` bundles a measure with total mass one. The proof constructs `CompactSpace K` from `hKcompact` and `Nonempty K` from `hKnonempty`, and obtains `Nonempty (Fin n)` after restricting to sufficiently large n. Those are internal derived instances; they do not add hidden assumptions.

I checked the compiler's `#check @...` and `#print ...` output, rather than relying only on source syntax. Full readable output is in [statement-print.log](statement-print.log); [full-type.log](full-type.log) is the **unabridged `pp.all` compiler type**, exposing inserted implicit arguments, universes and concrete instance terms. `pp.proofs false` in the readable helper hides the theorem proof body, not its proposition.

## 3. Translation into ordinary mathematics

Let d≥1, let K be a nonempty compact subset of Euclidean ℝᵈ, and fix real S≥0 and b>0 such that ‖u‖≤S for every u∈K. Let 𝒫(K) be all Borel probability laws on K. Set

$$
f_\mu(x)=\int_K(2\pi)^{-d/2}\exp(-\|x-u\|^2/2)\,d\mu(u),\qquad
L_w(\mu;x)=\sum_{i=1}^n w_i\log f_\mu(x_i),
$$

$$
\mathcal M_x(w)=\{\mu\in\mathcal P(K):\ \forall\nu\in\mathcal P(K),\ L_w(\nu;x)\le L_w(\mu;x)\}.
$$

For sufficiently large n, define

$$
r_n=\left(\frac{\log n}{\log\log n}\right)^d,\quad
\bar r_n=r_n+\log n,\quad \alpha_n=\bar r_n\log n,\quad
R_n=\frac{(\log n)^{d+1}}{n(\log\log n)^d}.
$$

The probability law used in the conclusion is exactly

$$
P_{G^*,n}=\bigl(f_{G^*}(x)\,dx\bigr)^{\otimes n}
\otimes\operatorname{Gamma}(\alpha_n,\text{rate }\alpha_n)^{\otimes n}.
$$

Thus data are iid with mixture density $f_{G^*}$; weights are iid Gamma with shape and rate αₙ, independently of data. The latent-variable representation Xᵢ=Θᵢ+Zᵢ is encoded through its induced law rather than by carrying named latent variables in the final type. [GaussianSampling.lean](../../ReweightedNPMLE/GaussianSampling.lean#L23) proves the equality with the Gaussian location-mixture law.

There exist **C>0 and n₀**, independent of G*, such that for every n≥n₀ and every G*∈𝒫(K), there exists a measurable event $E=E_{n,G^*}$ with

$$P_{G^*,n}(E^c)\le Cn^{-b}.$$

For every (x,w)∈E, all of the following hold on that same event:

1. Every wᵢ>0 and $\max_i|w_i-1|\le C/\sqrt{\bar r_n}$.
2. There exists $\widehat G_w\in\mathcal P(K)$ with $\mathcal M_x(w)=\{\widehat G_w\}$, finite topological support, and $\#\operatorname{supp}\widehat G_w\le C\bar r_n$.
3. For **every** $\widehat G_0\in\mathcal M_x(\mathbf1)$,
   $$0\le\sum_i\log f_{\widehat G_0}(x_i)-\sum_i\log f_{\widehat G_w}(x_i)\le C/\log n,$$
   $$\sum_i\left[\log\frac{f_{\widehat G_w}(x_i)}{f_{\widehat G_0}(x_i)}\right]^2\le C/\log n.$$
4. With the paper's Hellinger convention,
   $$\int_{\mathbb R^d}\left(\sqrt{f_{\widehat G_w}(y)}-\sqrt{f_{G^*}(y)}\right)^2\,dy\le C R_n.$$

The quantifier order is

$$
\exists C>0\ \exists n_0\ \forall n\ge n_0\ \forall G^*\in\mathcal P(K)\quad
\exists E\ \forall(x,w)\in E\ \exists\widehat G_w\ \forall\widehat G_0\in\mathcal M_x(\mathbf1).
$$

`∀ᶠ n : ℕ in atTop` means exactly “there exists n₀ such that for every n≥n₀.” The good event may depend on n and G*; C and n₀ cannot. Neither the paper nor Lean states one joint event simultaneously over every sample size. There is one common event for the four conclusions at each sample size and truth.

## 4. Clause-by-clause comparison

In the table, abbreviated Lean filenames refer to files under `ReweightedNPMLE/` at the package root. Their definitions and exact source excerpts are given in section 7.

| Clause | Lean meaning/evidence | Assessment |
|---|---|---|
| Fixed integer d>=1 | `{d : ℕ} (hd : 0 < d)` at MainTheorem:57 | Match. |
| Euclidean R^d | `abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)` at Gaussian:21 | Match; not a sup-norm function space. |
| Arbitrary fixed nonempty compact K | `(K : Set (Point d)) (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)` at MainTheorem:57–58 | Match. No finite-grid, finite-support, convexity, interior, separation, or smooth-boundary restriction. |
| K subset closed Euclidean ball, finite S | `{S : ℝ}`, `hS : 0 ≤ S`, `hKbound : ∀ u ∈ K, ‖u‖ ≤ S` | Match. S finite is implicit in being a real number. Explicit S>=0 is redundant given nonempty K and norm bound; not a substantive added assumption. |
| Gstar any Borel probability supported on K | `∀ Gstar : ProbabilityMeasure K` | Match under identification of Borel probabilities on closed subtype K with ambient probabilities carried by K. Not restricted to finite mixtures. |
| Model and weight independence | `gaussianDataWeightMeasure = compactGaussianSampleMeasure.prod gammaProductMeasure`; sample law is product of density f_Gstar; weight law is product Gamma(alpha,alpha) | Match in distribution. No separate latent Theta/Z variables appear in the final type, but GaussianSampling:23–27 proves equality with latent Gaussian location-mixture law. |
| Balanced scale | GaussianPaperScales:19–26 expands to r=(log n/log log n)^d, bar r=r+log n, alpha=bar r log n | Exact match. |
| Constant and threshold uniform in truth | `∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, ∀ Gstar, ...` | Correct order: a single C and n0 precede Gstar. They cannot depend on n, Gstar, data or weights. AtTop on naturals means exists n0, for every n>=n0. |
| Polynomial high probability on joint event | `∃ G, MeasurableSet G ∧ P.real Gᶜ ≤ C*n^(-b) ∧ ∀ p∈G, ...` | Equivalent to probability >=1-C*n^-b. G may depend on n and Gstar, as allowed by a uniform-in-law event statement. Both paper and Lean are for each n, not one simultaneous-across-n event. |
| (i) Existence, uniqueness, exact finite support | `∃ μ : ProbabilityMeasure K, optimizerSet p = {μ} ∧ support.Finite ∧ (support.ncard : ℝ) ≤ C*bar r` | Match. Singleton equality plus existential explicitly supplies a maximizer, not merely “at most one”; finite support is stated separately, avoiding ncard's infinite-set value convention. Support is topological support on K, corresponding to ambient support because K is closed. |
| (ii) Maximum perturbation | `∀ i, abs(p.2 i - 1) ≤ C / sqrt bar r` | Equivalent finite-coordinate formulation. Lean also explicitly states all weights >0 on G; a harmless additional conclusion. |
| (iii) Every ordinary NPMLE | `∀ μ₀ ∈ optimizerSet (p.1,1), ...` | Correct universal quantifier inside the same good event; not one selected comparator or separately chosen events. |
| (iii) Total ordinary likelihood gap | `0 ≤ gaussianOrdinaryLikelihoodGap ... ∧ gap ≤ C/log n` | Exact match: gap is total sum log f_mu0 minus total sum log f_mu. No 1/n normalization. |
| (iii) Squared fitted-log difference | `gaussianSquaredLogRatioGap ... ≤ C/log n` | Exact match: sum_i [log(f_mu(X_i)/f_mu0(X_i))]^2. Neither square of sum nor averaged square. |
| (iv) Global Hellinger | `hellingerSq volume (compactGaussianMixtureDensity μ) (...Gstar) ≤ C*gaussianPaperRiskScale d n` | Exact match. Integrates over all Point d with Lebesgue volume. No restriction to observed points or a bounded box. Hellinger convention is ∫(sqrt p-sqrt q)^2. |
| (iv) Rate | MainTheorem:18–23 proves `gaussianPaperRiskScale = (log n)^(d+1) / (n*(log(log n))^d)` | Exact match, including log-log denominator. |
| Final d>=2 / d=1 big-O sentence | Main theorem retains C*bar r bound rather than separately stating the two big-O corollaries | No weakened quantitative conclusion: the displayed bar-r bound gives those asymptotic regimes. Separate big-O syntactic assertions are not in this theorem's type. |

**Stronger assumptions:** none substantive found. Explicit S≥0 is implied already by nonempty K and ‖u‖≤S. Compactness, nonemptiness, d≥1, identity Gaussian covariance, the same fixed K for truth and optimization, and eventual-in-n scope match the manuscript's model.

**Weaker conclusions/restricted domains:** none in the four displayed clauses. The support bound is on the actual mixing measure, and optimization includes arbitrary probability measures, including nonatomic ones. Hellinger is integrated on all ℝᵈ. The theorem does not assume a finite true mixture, separated atoms, a candidate grid, a smooth boundary, a generic fixed dataset, or a chosen smooth optimizer.

**Existence:** weighted existence is explicit: `∃ μ` together with `optimizerSet = {μ}`. Ordinary existence is not a separate conjunct of the main type; it is proved in [GaussianJointStructural.lean](../../ReweightedNPMLE/GaussianJointStructural.lean#L170), lines 179–185. I also compiled an external helper establishing ordinary optimizer nonemptiness from the same proved ingredients. Thus the universal comparison is not an empty-set loophole. This helper requires n>0, as is available eventually in the main theorem.

**Dimension refinements:** the final manuscript sentence is exported separately as `ReweightedNPMLE.gaussian_main_support_dimension_refinements` at [GaussianSupportRefinements.lean](../../ReweightedNPMLE/GaussianSupportRefinements.lean#L29). Its support order is log n when d=1 and rₙ when d≠1; the theorem assumes d>0. The proof uses the eventual inequality $\bar r_n\le2\,\mathrm{supportOrder}(d,n)$ together with the main theorem. This is not an extra hypothesis. The main type itself retains the stronger explicit $C\bar r_n$ formulation, rather than a syntactic big-O clause.

**Constant dependencies:** the type permits C and n₀ to depend only on fixed d,K,S,b. The actual proof chooses

$$C_{d,b}=1+10^7(1+161^d+b+4)+2\sqrt{b+4}
+22+4\bigl(17(d+1)(1025^d+1)+b+4\bigr)+4d+5.$$

This chosen C depends only on d,b, which is permissible and stronger uniformity. It does not depend on n, G*, observations, weights, or the optimizer. The eventual threshold is not numerically explicit; it may depend on the fixed geometry/radius and b, as allowed. Section 7 includes every definition of this witness.

**Exact event versus measurable good subset:** Lean proves `∃ G, MeasurableSet G ∧ P(Gᶜ) ≤ C n⁻ᵇ ∧ ∀ p ∈ G, ...`. It does not assert `G = {p | all four properties}` or explicitly prove that this entire property set is measurable. A measurable subset with the stated probability is sufficient for the usual “all conclusions hold with high probability” guarantee. If the LaTeX word “event” is read as demanding measurability of exactly the maximal four-property set, that extra conclusion is not stated in the main type. The report makes no claim that a separate exact-event measurability theorem was checked.

**What this type does not claim:** it does not provide a globally measurable estimator map, its values off the good event, or an algorithm that computes the optimizer. It supplies a measurable good event and pointwise unique optimizer existence on that event. It does not assert finite-n bounds for every small n. These are scope distinctions, not discrepancies with `thm:main`.

## 5. Mathematical inputs: proved or assumed?

No intermediate mathematical result was found left as an assumption of the final main theorem. This conclusion uses the compiled complete type, the transitive axiom output, and inspection of the nontrivial dependency call sites below. An intermediate lemma can legitimately assume genericity, small support, differentiability, or a Jacobian estimate; the question is whether the main proof supplies those hypotheses. Here the inspected callers do.

### Significant mathematical inputs and their discharge

| Input that could otherwise conceal a missing theorem | Actual proof/discharge |
|---|---|
| Simultaneous evaluation independence for every distinct, potentially data-dependent Gaussian location list | [GaussianGenericity.lean:101–119](../../ReweightedNPMLE/GaussianGenericity.lean#L101) proves the Borel conull data set; the proof uses the proved null projection theorem at [GaussianGenericity.lean:57–82](../../ReweightedNPMLE/GaussianGenericity.lean#L57), whose regular-locus argument is at [IncidenceProjection.lean:19–89](../../ReweightedNPMLE/IncidenceProjection.lean#L19). It is invoked at [GaussianExactRegularization.lean:146](../../ReweightedNPMLE/GaussianExactRegularization.lean#L146), and supplied to uniqueness at lines 193–194. It is not a hypothesis of the main theorem. |
| Small support for every extreme optimizer | [GaussianStructural.lean:111–187](../../ReweightedNPMLE/GaussianStructural.lean#L111) proves the conditional bound by applying `effective_dimension_full_support`, supplying the Gaussian Taylor subspace, rank bound, and proved width inequality at lines 169–183. [FullEffectiveDimension.lean:34–103](../../ReweightedNPMLE/FullEffectiveDimension.lean#L34) includes both finite support and the bound for all extreme laws. [GaussianExactRegularization.lean:187–194](../../ReweightedNPMLE/GaussianExactRegularization.lean#L187) constructs the `hsmall` input and supplies it to uniqueness. |
| Finiteness of full probability-measure extreme optimizers | [FullExtremeSupport.lean:70–102](../../ReweightedNPMLE/FullExtremeSupport.lean#L70) proves finite support and support size at most `n`; it argues by selecting too many distinct support points and producing disjoint positive-mass regions, invoking the non-extremality perturbation theorem. No finite-support premise is imposed on the optimizer. |
| Passage from unique extreme optimizer to unique full optimizer | [SupportUniqueness.lean:18–77](../../ReweightedNPMLE/SupportUniqueness.lean#L18) proves equality of extreme laws using the union of their proved finite supports and linear independence. [ProbabilityFiberGeometry.lean:131–170](../../ReweightedNPMLE/ProbabilityFiberGeometry.lean#L131) proves the Krein–Milman step using mathlib's compact-convex extreme-point theorem. |
| Existence of weighted and ordinary optimizers | [FittedRegularity.lean:24–34](../../ReweightedNPMLE/FittedRegularity.lean#L24) uses `Classical.choose` on the proved `exists_fittedValue_maximizer`; [ProbabilityOptimizerFiber.lean:102–122](../../ReweightedNPMLE/ProbabilityOptimizerFiber.lean#L102) constructs an atomic probability law for every vector in the convex hull. Weighted optimizer existence is constructed in [GaussianJointStructural.lean:136–142](../../ReweightedNPMLE/GaussianJointStructural.lean#L136); ordinary optimizer existence is constructed at lines 179–185. Thus the universal comparison clause of the main statement is not vacuous under its hypotheses, even though the main theorem's type does not separately export `∃ μ₀`. |
| Differentiability of a chosen fitted map | [FittedRegularity.lean:386](../../ReweightedNPMLE/FittedRegularity.lean#L386) proves a.e. differentiability of the canonical fitted log map, using its Lipschitz bounds. [FittedDeterminantMoment.lean:118–127](../../ReweightedNPMLE/FittedDeterminantMoment.lean#L118) calls that theorem and derives measurability. No arbitrary smooth optimizer selection is assumed. |
| Gamma determinant moment / Jacobian gain | [FittedDeterminantMoment.lean:98–156](../../ReweightedNPMLE/FittedDeterminantMoment.lean#L98) proves the maximum-support moment bound and supplies differentiability, monotonicity, and determinant domination to the general change-of-variables lemma. In particular, lines 152–154 invoke `canonical_maximumIndependentSupport_jacobian_determinant_lower`. [ChangeOfVariables.lean:519–554](../../ReweightedNPMLE/ChangeOfVariables.lean#L519) is a conditional general lemma, but its hypotheses are discharged at this call site. [EffectiveDimension.lean:115–163](../../ReweightedNPMLE/EffectiveDimension.lean#L115) applies the proved moment bound to obtain the Gamma support tail. |
| Uniform statistical risk bound | [GaussianNearMLERate.lean:1295–1401](../../ReweightedNPMLE/GaussianNearMLERate.lean#L1295) proves the actual paper-scale bad-event bound uniformly over `Gstar`; the approximation and scale conditions of [GaussianNearMLE.lean:446–481](../../ReweightedNPMLE/GaussianNearMLE.lean#L446) are supplied at [GaussianNearMLERate.lean:1314–1357](../../ReweightedNPMLE/GaussianNearMLERate.lean#L1314). [GaussianJointTheorems.lean:32–60](../../ReweightedNPMLE/GaussianJointTheorems.lean#L32) makes a measurable hull, then lines 93–95 and 137–140 combine the risk theorem with the structural theorem and the proved near-MLE implication. |
| Data law absolute continuity | [GaussianJointTheorems.lean:119](../../ReweightedNPMLE/GaussianJointTheorems.lean#L119) supplies `compactGaussianSampleMeasure_absolutelyContinuous Gstar n`; it does not assume arbitrary data are generic. [GaussianSampling.lean:39](../../ReweightedNPMLE/GaussianSampling.lean#L39) proves this from the actual mixture density law. |

The lower-level conditional interfaces do contain nontrivial hypotheses, for example `hgeneric` and `hsmall` at [GaussianStructural.lean:201–205](../../ReweightedNPMLE/GaussianStructural.lean#L201), or derivative/monotonicity/Jacobian hypotheses at [ChangeOfVariables.lean:524–534](../../ReweightedNPMLE/ChangeOfVariables.lean#L524). Listing these as *unproved assumptions of the main result* would be incorrect: the above caller sites discharge them. They remain assumptions only when those general-purpose lemmas are used in isolation.

The actual transitive foundation list for the main theorem is exactly `propext`, `Classical.choice`, and `Quot.sound`. These are Lean's standard propositional extensionality, classical choice, and quotient-soundness axioms. There is no `sorryAx` or project-defined mathematical axiom in that dependency list. In particular, using `Classical.choose` on a proved existence theorem is not assuming that existence theorem.

This was a statement/definition and proof-input audit, not an independent handwritten reproof of every imported theorem or a compiler-trust audit. The kernel checks establish the encoded propositions under the reported foundations; the source reading establishes the mathematical interpretation described here.

## 6. Historical commands actually run and their output

This section records the original audit on the author’s machine, before preparation of this standalone package. The absolute paths and raw log contents below are historical provenance, not portable commands. The raw `.log` files have been retained byte-for-byte. Original Python helpers are preserved in [historical/](historical/); their portable replacements alongside this README use package-relative locations. For fresh package checks and rerun instructions, see the release documentation and the section above.

All Lean commands below were run in:

```text
/Users/hanshengjiang/Documents/GitHubLocal-M5Pro/sparse-npmle/paper/exact_sparsity_reweighted_npmle_numerical_study/formalization
```

The existing `.lake/packages` is a symlink into this checkout's archived Lean dependency directory. The build used those locally present dependencies and existing build artifacts. It was **an incremental build**, not a clean rebuild of all 3,822 jobs.

Environment commands and actual output:

```text
$ lake --version
Lake version 5.0.0-src+d024af0 (Lean version 4.30.0)
$ lake env lean --version
Lean (version 4.30.0, arm64-apple-darwin24.6.0, commit d024af099ca4bf2c86f649261ebf59565dc8c622, Release)
$ git rev-parse HEAD
e8bf8f2832b3d3dfb94ebdf3e9d718ad3434eeb4
```

The manifest pins mathlib to `v4.30.0`, resolved revision `c5ea00351c28e24afc9f0f84379aa41082b1188f`.

### Build

Actual command (exit 0):

```sh
lake build > /private/tmp/npmle-statement-audit/lake-build.log 2>&1
```

The final output line was:

```text
Build completed successfully (3822 jobs).
```

The output contains replayed linter warnings and the Verification target's axiom reports; the complete, unedited 1,713-line output is [lake-build.log](lake-build.log). Both default targets, `ReweightedNPMLE` and `Verification`, were included.

I also directly re-elaborated the main source file, with its imported dependencies, rather than only importing its cached compiled declaration (exit 0):

```sh
lake env lean ReweightedNPMLE/GaussianMainTheorem.lean > /private/tmp/npmle-statement-audit/main-source-check.log 2>&1
```

Complete output:

```text
ReweightedNPMLE/GaussianMainTheorem.lean:21:60: warning: This simp argument is unused:
  div_pow

Hint: Omit it from the simp argument list.
  simp only [gaussianPaperRiskScale, gaussianPaperLogScale, d̵i̵v̵_̵pow,̵ ̵p̵o̵w̵_succ,
  ̵  ̵ ̵ ̵div_eq_mul_inv, mul_inv_rev]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
```

This is a linter warning, not a missing proof or build failure. It was left unchanged.

### Complete type and focused axiom checks

Actual successful commands (each exit 0):

```sh
lake env lean /private/tmp/npmle-statement-audit/StatementAudit.lean > /private/tmp/npmle-statement-audit/statement-print.log 2>&1
lake env lean /private/tmp/npmle-statement-audit/FullType.lean > /private/tmp/npmle-statement-audit/full-type.log 2>&1
```

The exact successful [StatementAudit.lean](StatementAudit.lean) contains:

```lean
import ReweightedNPMLE.GaussianMainTheorem
set_option format.width 120
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.proofs false
#check @ReweightedNPMLE.gaussian_exact_regularization_main
#print ReweightedNPMLE.gaussian_exact_regularization_main
#print axioms ReweightedNPMLE.gaussian_exact_regularization_main
#print axioms ReweightedNPMLE.gaussian_exact_regularization_joint_balanced_explicit
#print ReweightedNPMLE.gaussianPaperJointConstant
#print ReweightedNPMLE.gaussianPaperSupportConstant
#print ReweightedNPMLE.gaussianPaperRateConstant
#print ReweightedNPMLE.gaussianPaperEntropyConstant
```

Its main axiom output is:

```text
'ReweightedNPMLE.gaussian_exact_regularization_main' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReweightedNPMLE.gaussian_exact_regularization_joint_balanced_explicit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Full type/constant output is [statement-print.log](statement-print.log). The [FullType.lean](FullType.lean) uses `set_option pp.all true in #check @ReweightedNPMLE.gaussian_exact_regularization_main`; its 1,049-line output is [full-type.log](full-type.log). That long output is provided as a file without truncation.

### Independent Verification entry point

Actual command (exit 0):

```sh
lake env lean Verification.lean > /private/tmp/npmle-statement-audit/verification.log 2>&1
```

The complete 1,277-line output is [verification.log](verification.log). I parsed that actual output against the distinct `#print axioms` declarations in `Verification.lean`, rejecting missing, duplicate, or extra reports and any axiom outside the three-element allowlist. The original audit parser is preserved at [historical/check_axiom_output.py](historical/check_axiom_output.py); a portable version is [check_axiom_output.py](check_axiom_output.py). The actual historical command and output (exit 0):

```text
$ python3 /private/tmp/npmle-statement-audit/check_axiom_output.py
7 declarations: []
613 declarations: [Classical.choice, Quot.sound, propext]
1 declarations: [Quot.sound, propext]
Independent axiom audit passed: 621 unique declarations
```

The command's stdout was captured to `axiom-summary.log` with shell redirection. An earlier parser run also used the repository verifier's `audit_output` function against the same log and gave the same counts; I did not run the verifier's full `main()` workflow.

### Semantic side checks and intermediate axioms

Actual successful command (exit 0):

```sh
lake env lean /private/tmp/npmle-statement-audit/SemanticChecks.lean > /private/tmp/npmle-statement-audit/semantic-checks.log 2>&1
```

The external [SemanticChecks.lean](SemanticChecks.lean) proves two extra checks: (a) the defined joint measure is a probability measure whenever α>0, and (b) ordinary optimizer nonemptiness under compactness/nonemptiness and n>0. These compiled `example`s emit no success text; their success is the command's zero exit status. The same file prints the type of the dimension refinement and axioms of five relevant results. Their actual output is:

```text
'ReweightedNPMLE.gaussian_main_support_dimension_refinements' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReweightedNPMLE.compactGaussianMixture_uniform_nearMLE_paper_rate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ReweightedNPMLE.gaussian_evaluation_independence_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReweightedNPMLE.full_extreme_optimizer_support_finite_card_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ReweightedNPMLE.canonical_maximumIndependentSupport_gamma_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Full output, including the dimension-refinement type, is [semantic-checks.log](semantic-checks.log).

### Source scan, manuscript diff, and unchanged-source verification

Actual production-source scan:

```sh
rg -n '\b(axiom|sorry|admit|unsafe|sorryAx|native_decide|implemented_by)\b' ReweightedNPMLE.lean Verification.lean ReweightedNPMLE > /private/tmp/npmle-statement-audit/source-scan.log
```

Actual output (all four matches are comments, not declarations or proof terms):

```text
Verification.lean:5:standard mathlib axioms and must not use any proof placeholder or project-defined axiom.
ReweightedNPMLE/NumericalTable.lean:10:literal bounds, and without a floating-point oracle or `native_decide`.
ReweightedNPMLE/SupportSensitivity.lean:17:likelihood contact equations, and admit an explicit orthonormal matrix.
ReweightedNPMLE/NumericalStudy.lean:12:`native_decide` or an oracle axiom.
```

This textual check supplements the transitive axiom checks; it is not their substitute. The preexisting excluded scratch file `Check.lean` is not a production import.

I ran `python3 /private/tmp/npmle-statement-audit/compare_manuscripts.py` with stdout redirected to `manuscript-comparison.log`; the [original compare_manuscripts.py](historical/compare_manuscripts.py) and [manuscript-comparison.log](manuscript-comparison.log) preserve the exact extraction and output. I fingerprinted 120 formalization source/config/reference files before the checks; the after-check comparison is [source-integrity.log](source-integrity.log). `git diff --exit-code -- paper/exact_sparsity_reweighted_npmle_numerical_study/formalization` also passed with no output. Audit artifacts live outside the formalization directory; normal build artifacts may have been refreshed.

Actual fingerprint-check command (exit 0), from the formalization directory:

```sh
python3 /private/tmp/npmle-statement-audit/verify_sources.py > /private/tmp/npmle-statement-audit/source-integrity.log
```

Actual output:

```text
Fingerprinted source/config/reference files: 120
Missing: 0
Changed: 0
PASS: every fingerprinted formalization file is unchanged.
```

The final repository status at the time of this audit was `?? audit/`; no tracked source change was present.

### Failed audit-helper attempts, retained for transparency

Two first attempts to run external scratch helpers returned exit 1. They did not edit the project or reveal a formalization failure:

- The initial `StatementAudit.lean` used unsupported option `pp.width` and requested nonexistent exploratory names `gaussianPaperDegreeConstant` and `gaussianPaperDegree`. The actual errors and all output are [statement-print.initial.log](statement-print.initial.log), with the original [StatementAudit.initial.lean](StatementAudit.initial.lean). I changed only the external helper to `format.width` and removed the two nonexistent requests, then reran the same shell command successfully.
- The initial `SemanticChecks.lean` requested the nonexistent exploratory name `gaussianEvaluationGeneric_ae`. Both semantic `example`s had already elaborated without error. I corrected that one external request to the source-verified `gaussian_evaluation_independence_ae` and reran successfully. The original [SemanticChecks.initial.lean](SemanticChecks.initial.lean) and [semantic-checks.initial.log](semantic-checks.initial.log) preserve the failed attempt.

The failed shell commands used the same helper paths and output redirections as the later successful commands above; their earlier contents and logs are retained with `.initial` filenames. The final reported passes refer to the corrected helpers.

### Checks not run

I did **not** run a clean dependency rebuild, `lake exe cache get`, the complete `python3 scripts/verify.py` workflow, numerical-data regeneration or simulations, LaTeX/PDF compilation, CI/GitHub actions, a separate kernel implementation, or a theorem proving the existence of a global measurable estimator selection. I did not rerun the archived historical formalization. No such check is implied by this report.

## 7. Recursive definition expansions with corresponding Lean source

The following expands every project-specific definition needed to interpret the main type, including the project-local `IsMaxOn` (which includes feasible-set membership), the probability-law construction, and the actual common-constant witness. Mathlib definitions are included where they matter for probability, support, or totalization. Supporting theorem excerpts are evidence for semantic side conditions rather than additional hypotheses of the main result.

### Ambient space, candidate domain, and optimizer

`Point d` is Euclidean $\mathbb R^d$, with its usual Euclidean norm and Borel measurable structure. Data and weights are $(x,w)\in(\mathbb R^d)^n\times\mathbb R^n$. Indexing by `Fin n` is indexing $0,\ldots,n-1$.

Source: [Gaussian.lean:20](../../ReweightedNPMLE/Gaussian.lean#L20) (lines 20–21).

```lean
/-- The ambient Euclidean parameter and observation space. -/
abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)
```

Source: [GaussianJointEvents.lean:18](../../ReweightedNPMLE/GaussianJointEvents.lean#L18) (lines 18–18).

```lean
abbrev GaussianDataWeight (d n : ℕ) := (Fin n → Point d) × (Fin n → ℝ)
```

`ProbabilityMeasure K` bundles an actual probability measure on the subtype $K$, not a finite atomic parameterization. Because $K$ inherits its topology and Borel structure from Euclidean space, this means a Borel probability law on $K$. The statement restricts **both the true mixing law and the optimization domain to this same compact $K$**. There is no finite grid, bounded support-cardinality constraint, or discretized optimizer domain in the definition.

Source: [.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean:102](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean#L102) (lines 102–105).

```lean
/-- Probability measures are defined as the subtype of measures that have the property of being
probability measures (i.e., their total mass is one). -/
def ProbabilityMeasure (Ω : Type*) [MeasurableSpace Ω] : Type _ :=
  { μ : Measure Ω // IsProbabilityMeasure μ }
```

The kernel and candidate mixture are
$$\phi_d(x-u)=(2\pi)^{-d/2}e^{-\|x-u\|^2/2},\qquad f_\mu(x)=\int_K\phi_d(x-u)\,d\mu(u).$$
The covariance is fixed to the identity matrix; neither covariance nor bandwidth is optimized.

Source: [Gaussian.lean:27](../../ReweightedNPMLE/Gaussian.lean#L27) (lines 27–29).

```lean
/-- The standard Gaussian normalizing constant in dimension `d`. -/
noncomputable def gaussianConstant (d : ℕ) : ℝ :=
  (2 * Real.pi) ^ (-(d : ℝ) / 2)
```

Source: [Gaussian.lean:35](../../ReweightedNPMLE/Gaussian.lean#L35) (lines 35–37).

```lean
/-- The standard Gaussian location kernel. -/
noncomputable def gaussianKernel (d : ℕ) (x θ : Point d) : ℝ :=
  gaussianConstant d * Real.exp (-‖x - θ‖ ^ 2 / 2)
```

Source: [GaussianMixtureMeasure.lean:17](../../ReweightedNPMLE/GaussianMixtureMeasure.lean#L17) (lines 17–21).

```lean
/-- The Gaussian location-mixture density generated by a parameter map and a
mixing measure. -/
noncomputable def gaussianMixture {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (θ : Θ → Point d) (x : Point d) : ℝ :=
  ∫ a, gaussianKernel d x (θ a) ∂μ
```

Source: [GaussianNearMLE.lean:20](../../ReweightedNPMLE/GaussianNearMLE.lean#L20) (lines 20–24).

```lean
/-- The density of the Gaussian location mixture generated by a probability
measure on the subtype `K`. -/
noncomputable def compactGaussianMixtureDensity {d : ℕ}
    {K : Set (Point d)} (G : ProbabilityMeasure K) : Point d → ℝ :=
  gaussianMixture (G : Measure K) (fun θ : K ↦ (θ : Point d))
```

For a general feature map $A$, `probabilityMixtureValue A μ i` is $\int A(u,i)\,d\mu(u)$. Specializing to the Gaussian kernel gives exactly $f_\mu(x_i)$.

Source: [ProbabilityOptimizerFiber.lean:24](../../ReweightedNPMLE/ProbabilityOptimizerFiber.lean#L24) (lines 24–26).

```lean
noncomputable def probabilityMixtureValue {Θ : Type*} [MeasurableSpace Θ] {n : ℕ}
    (A : Θ → Fin n → ℝ) (μ : ProbabilityMeasure Θ) : Fin n → ℝ :=
  fun i ↦ ∫ θ, A θ i ∂μ
```

The objective is the **total**, unnormalized weighted log likelihood
$$L_w(\mu;x)=\sum_{i=0}^{n-1}w_i\log f_\mu(x_i).$$
The maximizer set is
$$\operatorname{Argmax}_w(x)=\{\mu\in\mathcal P(K):\forall\nu\in\mathcal P(K),\ L_w(\nu;x)\le L_w(\mu;x)\}.$$

Source: [Weights.lean:25](../../ReweightedNPMLE/Weights.lean#L25) (lines 25–31).

```lean
/-- The finite weighted log-likelihood of a positive fitted-value vector. -/
noncomputable def weightedLogLikelihood {n : ℕ} (w v : Fin n → ℝ) : ℝ :=
  ∑ i, w i * Real.log (v i)

/-- A point `v` maximizes `f` on the feasible set `C`. -/
def IsMaxOn {E : Type*} (C : Set E) (f : E → ℝ) (v : E) : Prop :=
  v ∈ C ∧ ∀ u ∈ C, f u ≤ f v
```

Source: [GaussianJointEvents.lean:20](../../ReweightedNPMLE/GaussianJointEvents.lean#L20) (lines 20–27).

```lean
noncomputable def gaussianProbabilityLogLikelihood {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (p : GaussianDataWeight d n × ProbabilityMeasure Θ) : ℝ :=
  weightedLogLikelihood p.1.2
    (probabilityMixtureValue (fun a i ↦ gaussianKernel d (p.1.1 i) (θ a)) p.2)

def gaussianProbabilityOptimizerSet {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d) (p : GaussianDataWeight d n) : Set (ProbabilityMeasure Θ) :=
  {μ | IsMaxOn univ (fun ν ↦ gaussianProbabilityLogLikelihood θ (p, ν)) μ}
```

`univ` in this definition is all of `ProbabilityMeasure K`, not all probability laws on the ambient $\mathbb R^d$. Equality of this set to `{μ}` states existence and uniqueness of a **mixing law**, not merely equality of fitted density vectors. The separate finite-support conclusion is substantive.

`positiveVectors n` means every coordinate is strictly positive: $w_i>0$ for every $i$. It does not impose a normalization or a sum constraint.

Source: [Weights.lean:33](../../ReweightedNPMLE/Weights.lean#L33) (lines 33–35).

```lean
/-- The strictly positive orthant containing all fitted-value vectors. -/
def positiveVectors (n : ℕ) : Set (Fin n → ℝ) :=
  {v | ∀ i, 0 < v i}
```

### Scales and probability experiment

For sufficiently large $n$, write
$$q_n=\frac{\log n}{\log\log n},\quad r_n=q_n^d,\quad D_n=r_n+\log n,\quad\alpha_n=D_n\log n,\quad R_n=\frac{r_n\log n}{n}=\frac{(\log n)^{d+1}}{n(\log\log n)^d}.$$

Source: [GaussianNearMLERate.lean:22](../../ReweightedNPMLE/GaussianNearMLERate.lean#L22) (lines 22–25).

```lean
/-- The logarithmic scale used for the paper's Taylor order.  Values at the
finitely many small sample sizes are immaterial to the eventual statements. -/
noncomputable def gaussianPaperLogScale (n : ℕ) : ℝ :=
  Real.log n / Real.log (Real.log n)
```

Source: [GaussianPaperScales.lean:19](../../ReweightedNPMLE/GaussianPaperScales.lean#L19) (lines 19–26).

```lean
noncomputable def gaussianPaperEffectiveDimension (d n : ℕ) : ℝ :=
  gaussianPaperLogScale n ^ d

noncomputable def gaussianPaperAugmentedDimension (d n : ℕ) : ℝ :=
  gaussianPaperEffectiveDimension d n + Real.log n

noncomputable def gaussianPaperBalancedShape (d n : ℕ) : ℝ :=
  gaussianPaperAugmentedDimension d n * Real.log n
```

Source: [GaussianMainTheorem.lean:15](../../ReweightedNPMLE/GaussianMainTheorem.lean#L15) (lines 15–23).

```lean
noncomputable def gaussianPaperRiskScale (d n : ℕ) : ℝ :=
  gaussianPaperLogScale n ^ d * Real.log n / n

theorem gaussianPaperRiskScale_eq (d n : ℕ) :
    gaussianPaperRiskScale d n = Real.log (n : ℝ) ^ (d + 1) /
      ((n : ℝ) * Real.log (Real.log (n : ℝ)) ^ d) := by
  simp only [gaussianPaperRiskScale, gaussianPaperLogScale, div_pow, pow_succ,
    div_eq_mul_inv, mul_inv_rev]
  ring
```

The iid sample law has density $\prod_{i=0}^{n-1} f_{G_*}(x_i)$ relative to product Lebesgue measure. The weights have independent Gamma distributions with **shape and rate both $\alpha_n$**. Data and weights are independent because the final measure is a product. Equivalently,
$$P_{G_*,n}=\Bigl(f_{G_*}(x)\,dx\Bigr)^{\otimes n}\otimes\operatorname{Gamma}(\alpha_n,\text{rate }\alpha_n)^{\otimes n}.$$

Source: [GaussianSampling.lean:18](../../ReweightedNPMLE/GaussianSampling.lean#L18) (lines 18–21).

```lean
noncomputable def compactGaussianSampleMeasure {d : ℕ} {K : Set (Point d)}
    (Gstar : ProbabilityMeasure K) (n : ℕ) : Measure (Fin n → Point d) :=
  Measure.pi (fun _ : Fin n ↦ volume.withDensity
    (fun y ↦ ENNReal.ofReal (compactGaussianMixtureDensity Gstar y)))
```

Source: [DirichletIndependence.lean:114](../../ReweightedNPMLE/DirichletIndependence.lean#L114) (lines 114–117).

```lean
/-- Product law of independent shape `a`, rate `r` Gamma coordinates. -/
noncomputable def gammaProductMeasure (n : ℕ) (a r : ℝ) :
    Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n ↦ gammaMeasure a r)
```

Source: [GaussianJointTheorems.lean:19](../../ReweightedNPMLE/GaussianJointTheorems.lean#L19) (lines 19–21).

```lean
noncomputable def gaussianDataWeightMeasure {d : ℕ} {K : Set (Point d)}
    (Gstar : ProbabilityMeasure K) (n : ℕ) (α : ℝ) : Measure (GaussianDataWeight d n) :=
  (compactGaussianSampleMeasure Gstar n).prod (gammaProductMeasure n α α)
```

For completeness, the imported Gamma density is
$$g_{a,r}(w)=\mathbf 1_{\{w\ge0\}}\frac{r^a}{\Gamma(a)}w^{a-1}e^{-rw}.$$

Source: [.lake/packages/mathlib/Mathlib/Probability/Distributions/Gamma.lean:43](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Probability/Distributions/Gamma.lean#L43) (lines 43–51).

```lean
/-- The pdf of the gamma distribution depending on its scale and rate -/
noncomputable
def gammaPDFReal (a r x : ℝ) : ℝ :=
  if 0 ≤ x then r ^ a / (Gamma a) * x ^ (a - 1) * exp (-(r * x)) else 0

/-- The pdf of the gamma distribution, as a function valued in `ℝ≥0∞` -/
noncomputable
def gammaPDF (a r x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (gammaPDFReal a r x)
```

Source: [.lake/packages/mathlib/Mathlib/Probability/Distributions/Gamma.lean:126](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Probability/Distributions/Gamma.lean#L126) (lines 126–133).

```lean
/-- Measure defined by the gamma distribution -/
noncomputable
def gammaMeasure (a r : ℝ) : Measure ℝ :=
  volume.withDensity (gammaPDF a r)

lemma isProbabilityMeasure_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IsProbabilityMeasure (gammaMeasure a r) where
  measure_univ := by simp [gammaMeasure, lintegral_gammaPDF_eq_one ha hr]
```

This is a probability law for $a,r>0$. In the theorem, $\alpha_n>0$ is proved eventually rather than assumed as an extra hypothesis. Thus the real-valued complement bound is an ordinary probability bound for the large sample sizes quantified in the statement. The source explicitly installs this probability instance in `GaussianJointTheorems.lean:107–111`.

Source: [GaussianPaperScales.lean:264](../../ReweightedNPMLE/GaussianPaperScales.lean#L264) (lines 264–277).

```lean
/-- Both scale hypotheses of the Gaussian structural theorem hold at the
paper's balanced shape; no rank or remainder estimate is left as an input. -/
theorem eventually_gaussianPaperBalanced_conditions (d : ℕ) {S b : ℝ}
    (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop,
      1 ≤ gaussianPaperStructuralTail b n ∧
      0 < gaussianPaperBalancedShape d n ∧
      10000000 * ((gaussianPaperStructuralRank d 40 n : ℝ) +
        effectiveQ n (gaussianPaperStructuralTail b n)) ≤ gaussianPaperBalancedShape d n ∧
      gaussianTaylorResidual n (gaussianPaperSampleRadius d S b n) S
          (gaussianPaperMomentOrder 40 n) *
        Real.sqrt (gaussianPaperBalancedShape d n * (n : ℝ) *
          effectiveQ n (gaussianPaperStructuralTail b n)) ≤ 1 := by
  filter_upwards [eventually_gaussianPaperStructuralTail_ge_one hb,
```

`Measure.real A` denotes `(measure A).toReal`. This conversion is harmless here: the measure is a probability law for the eventual sample sizes, so its set values are finite. With an arbitrary infinite measure the conversion would require care because `ENNReal.toReal ∞ = 0`; that loophole is not active here.

### Support, comparison losses, and Hellinger loss

The support is the ordinary topological support relative to $K$: $u\in\operatorname{supp}\mu$ iff every neighborhood of $u$ in $K$ has positive $\mu$-measure. Because $K$ is compact and hence closed in $\mathbb R^d$, identifying this support with the support of the pushed-forward law in $\mathbb R^d$ preserves the cardinality.

Source: [.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Support.lean:52](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/MeasureTheory/Measure/Support.lean#L52) (lines 52–55).

```lean
/-- A point `x` is in the support of `μ` if any open neighborhood of `x` has positive measure.
We provide the definition in terms of the filter-theoretic equivalent
`∃ᶠ u in (𝓝 x).smallSets, 0 < μ u`. -/
protected def support (μ : Measure X) : Set X := {x : X | ∃ᶠ u in (𝓝 x).smallSets, 0 < μ u}
```

Source: [.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Support.lean:69](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/MeasureTheory/Measure/Support.lean#L69) (lines 69–72).

```lean
/-- A point `x` is in the support of measure `μ` iff every neighborhood of `x` has positive
measure. -/
lemma mem_support_iff_forall (x : X) : x ∈ μ.support ↔ ∀ U ∈ 𝓝 x, 0 < μ U :=
  (𝓝 x).basis_sets.mem_measureSupport
```

`Set.ncard` is the natural-number cardinality for finite sets (and is totalized on infinite sets), so the explicit conjunction `(μ : Measure K).support.Finite ∧ ...ncard ≤ ...` matters. The theorem contains the finiteness assertion; it cannot pass its sparsity bound merely by the totalized infinite-set cardinality.

For $\mu_0\in\operatorname{Argmax}_1(x)$, the ordinary likelihood gap is
$$\Delta(\mu,\mu_0;x)=\sum_i\log f_{\mu_0}(x_i)-\sum_i\log f_\mu(x_i).$$
The weights $w$ are carried in the input tuple but the gap uses only $x$, $\mu$, and $\mu_0$. No $1/n$ appears.

Source: [GaussianJointEvents.lean:82](../../ReweightedNPMLE/GaussianJointEvents.lean#L82) (lines 82–86).

```lean
noncomputable def gaussianOrdinaryLikelihoodGap {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d)
    (p : GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ)) : ℝ :=
  gaussianProbabilityLogLikelihood θ ((p.1.1, 1), p.2.2) -
    gaussianProbabilityLogLikelihood θ ((p.1.1, 1), p.2.1)
```

The fitted log-ratio loss is also a **total sum**:
$$Q(\mu,\mu_0;x)=\sum_i\left[\log\frac{f_\mu(x_i)}{f_{\mu_0}(x_i)}\right]^2.$$

Source: [GaussianJointEvents.lean:113](../../ReweightedNPMLE/GaussianJointEvents.lean#L113) (lines 113–118).

```lean
noncomputable def gaussianSquaredLogRatioGap {Θ : Type*} [MeasurableSpace Θ]
    {d n : ℕ} (θ : Θ → Point d)
    (p : GaussianDataWeight d n × (ProbabilityMeasure Θ × ProbabilityMeasure Θ)) : ℝ :=
  ∑ i, (Real.log
    (probabilityMixtureValue (fun a j ↦ gaussianKernel d (p.1.1 j) (θ a)) p.2.1 i /
     probabilityMixtureValue (fun a j ↦ gaussianKernel d (p.1.1 j) (θ a)) p.2.2 i)) ^ 2
```

Squared Hellinger is
$$H^2(f,g)=\int_{\mathbb R^d}(\sqrt{f(x)}-\sqrt{g(x)})^2\,dx.$$

It is the convention with **no factor $1/2$**, and the integration domain is all of $\mathbb R^d$. It is not sample Hellinger distance, a discrete grid integral, a local metric, or a truncated integral.

Source: [Hellinger.lean:22](../../ReweightedNPMLE/Hellinger.lean#L22) (lines 22–25).

```lean
/-- Squared Hellinger distance with respect to a dominating measure. -/
noncomputable def hellingerSq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ) : ℝ :=
  ∫ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ∂μ
```

### Totalization and non-vacuity checks

Lean real logarithm, division, square root, and Bochner integral are total functions. Those facts do not collapse this theorem:

- Candidate Gaussian densities are proved strictly positive, integrable, and normalized for every bundled probability law on $K$ (without even needing compactness for these facts). Thus all fitted values in the objective and ratios are positive.
- The squared Hellinger integrand is integrable for nonnegative integrable densities. It is not using the Bochner integral's nonintegrability default.
- The logarithmic scales and Gamma shape are eventually positive. The statement is eventual in $n$ and makes no finite-sample assertion at $n=0,1$ or at nonpositive logarithmic denominators.
- `K.Nonempty` and compactness are hypotheses. Probability laws on $K$ exist; the true-law universal quantifier is not over an empty type.
- Singleton optimizer equality explicitly implies weighted optimizer existence.
- The main type does not explicitly state ordinary optimizer existence; its comparison clause is universal. However, the proof of `gaussian_optimizer_nearMLE_of_likelihood_bound` constructs an ordinary optimizer in lines 181–185 below. Therefore the comparison is not relying on an empty ordinary optimizer set. This is an omission of an explicit existence conjunct, not an assumed existence fact or mathematical vacuity.
- No measurable estimator $p\mapsto\mu(p)$ is asserted by the main theorem. It states a measurable good event and pointwise existence/uniqueness on it. This distinction matters only if a stronger measurable-estimator statement is requested.

Source: [GaussianNearMLE.lean:32](../../ReweightedNPMLE/GaussianNearMLE.lean#L32) (lines 32–48).

```lean
theorem compactGaussianMixtureDensity_pos {d : ℕ}
    {K : Set (Point d)} (G : ProbabilityMeasure K) (x : Point d) :
    0 < compactGaussianMixtureDensity G x := by
  exact gaussianMixture_pos (G : Measure K)
    (fun θ : K ↦ (θ : Point d)) measurable_subtype_coe x

theorem compactGaussianMixtureDensity_integrable {d : ℕ}
    {K : Set (Point d)} (G : ProbabilityMeasure K) :
    Integrable (compactGaussianMixtureDensity G) := by
  exact gaussianMixture_integrable (G : Measure K)
    (fun θ : K ↦ (θ : Point d)) measurable_subtype_coe

theorem integral_compactGaussianMixtureDensity {d : ℕ}
    {K : Set (Point d)} (G : ProbabilityMeasure K) :
    ∫ x, compactGaussianMixtureDensity G x = 1 := by
  exact integral_gaussianMixture (G : Measure K)
    (fun θ : K ↦ (θ : Point d)) measurable_subtype_coe
```

Source: [Hellinger.lean:168](../../ReweightedNPMLE/Hellinger.lean#L168) (lines 168–186).

```lean
/-- Integrable nonnegative densities have an integrable squared Hellinger
integrand.  This discharges a recurring analytic side condition for finite
Gaussian mixtures. -/
theorem hellingerIntegrand_integrable_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p q : Ω → ℝ)
    (hpmeas : AEStronglyMeasurable p μ) (hqmeas : AEStronglyMeasurable q μ)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ) :
    Integrable (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ := by
  have hmeas : AEStronglyMeasurable
      (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ := by
    exact ((Real.continuous_sqrt.comp_aestronglyMeasurable hpmeas).sub
      (Real.continuous_sqrt.comp_aestronglyMeasurable hqmeas)).pow 2
  apply ((hpint.add hqint).const_mul 2).mono' hmeas
  filter_upwards [hp, hq] with x hpx hqx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  change (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ≤ 2 * (p x + q x)
  nlinarith [sq_nonneg (Real.sqrt (p x) + Real.sqrt (q x)),
    Real.sq_sqrt hpx, Real.sq_sqrt hqx]
```

Source: [GaussianJointStructural.lean:170](../../ReweightedNPMLE/GaussianJointStructural.lean#L170) (lines 170–192).

```lean
theorem gaussian_optimizer_nearMLE_of_likelihood_bound {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [Nonempty Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {d n : ℕ} [Nonempty (Fin n)] (θ : Θ → Point d) (hθ : Continuous θ)
    (x : Fin n → Point d) (w : Fin n → ℝ) (μ : ProbabilityMeasure Θ) {t : ℝ} (ht : t ≤ 1)
    (hbound : ∀ μ₀ ∈ gaussianProbabilityOptimizerSet θ (x, 1),
      gaussianOrdinaryLikelihoodGap θ ((x, w), (μ, μ₀)) ≤ t) :
    ∀ ν : ProbabilityMeasure Θ,
      gaussianProbabilityLogLikelihood θ ((x, 1), ν) - 1 ≤
        gaussianProbabilityLogLikelihood θ ((x, 1), μ) := by
  let A := fun a ↦ gaussianScoreFeature x (θ a)
  have hA : Continuous A := (continuous_gaussianScoreFeature x).comp hθ
  have hfit := gaussianCanonicalFit_isMax x θ hθ 1
  obtain ⟨μ₀, hμ₀⟩ := probabilityMixtureFiber_nonempty_of_mem_convexHull A hA
    (gaussianCanonicalFit x θ hθ 1) hfit.1
  have hμ₀opt : μ₀ ∈ gaussianProbabilityOptimizerSet θ (x, 1) :=
    (gaussian_probability_optimizer_iff_score_fiber x θ hθ 1 _ (fun _ ↦ by norm_num) hfit μ₀).mpr hμ₀
  intro ν
  have hmax := hμ₀opt.2 ν (mem_univ ν)
  have hgap := (hbound μ₀ hμ₀opt).trans ht
  change gaussianProbabilityLogLikelihood θ ((x, 1), μ₀) -
    gaussianProbabilityLogLikelihood θ ((x, 1), μ) ≤ 1 at hgap
  dsimp only at hmax
  linarith
```

### Concrete common constant used by the proof

The final theorem permits $C$ to depend on the outer fixed data $(d,K,S,b)$, and its sample-size threshold can also depend on those quantities; both occur before `∀ Gstar`. In fact, the proof supplies the explicit witness below, depending **only on $d,b$**. There is no inappropriate dependence of this chosen constant on $n$, $G_*$, the sample, weights, or the optimizing law. The threshold is not explicit and is uniform over $G_*$.

Source: [GaussianExactRegularization.lean:98](../../ReweightedNPMLE/GaussianExactRegularization.lean#L98) (lines 98–99).

```lean
noncomputable def gaussianPaperSupportConstant (d : ℕ) (C b : ℝ) : ℝ :=
  10000000 * (1 + (4 * C + 1) ^ d + (b + 4))
```

Source: [GaussianNearMLERate.lean:1141](../../ReweightedNPMLE/GaussianNearMLERate.lean#L1141) (lines 1141–1147).

```lean
/-- Explicit entropy coefficient at the fixed Taylor constant `256`. -/
noncomputable def gaussianPaperEntropyConstant (d : ℕ) : ℝ :=
  17 * ((d : ℝ) + 1) * ((1025 : ℝ) ^ d + 1)

/-- Displayed constant in the final Hellinger-rate theorem. -/
noncomputable def gaussianPaperRateConstant (d : ℕ) (b : ℝ) : ℝ :=
  22 + 4 * (gaussianPaperEntropyConstant d + b + 4)
```

Source: [GaussianMainTheorem.lean:25](../../ReweightedNPMLE/GaussianMainTheorem.lean#L25) (lines 25–28).

```lean
noncomputable def gaussianPaperJointConstant (d : ℕ) (b : ℝ) : ℝ :=
  1 + gaussianPaperSupportConstant d 40 b + 2 * Real.sqrt (b + 4) +
    gaussianPaperRateConstant d b + (4 * (d : ℝ) + 5)

```

Writing
$$B_{d,b}=10^7(1+161^d+b+4),\quad E_d=17(d+1)(1025^d+1),\quad T_{d,b}=22+4(E_d+b+4),$$
the actual witness is
$$C_{d,b}=1+B_{d,b}+2\sqrt{b+4}+T_{d,b}+4d+5.$$

## 8. Exact manuscript statement compared

From [paper.tex](../../docs/manuscript/paper.tex#L373):

```latex
\begin{theorem}[Exact regularization by random reweighting]
\label{thm:main}
Assume \eqref{eq:model} with fixed $d$, fixed compact
$K\subset B(0,S)$, and $G^*\in\Pcal(K)$.  Let the weights satisfy
\eqref{eq:weights} with the concentration in \eqref{eq:scales}.  For every
$b>0$, there are constants $C_b<\infty$ and $n_0$ depending only on
$d,K,S,b$ such that, uniformly over $G^*\in\Pcal(K)$, the following event has
probability at least $1-C_bn^{-b}$ for every $n\ge n_0$:
\begin{enumerate}[label=\textup{(\roman*)}]
\item The weighted NPMLE is unique and
\[
  \#\supp(\Ghat_W)\le C_b\bar r_n.
\]
\item The perturbation is uniformly small:
\[
  \max_{1\le i\le n}\abs{W_i-1}\le \frac{C_b}{\sqrt{\bar r_n}}.
\]
\item For every ordinary NPMLE $\Ghat_0$,
\[
  0\le L_n(\Ghat_0)-L_n(\Ghat_W)\le\frac{C_b}{\log n},
\]
and
\[
 \sum_{i=1}^n
 \left\{\log\frac{f_{\Ghat_W}(X_i)}{f_{\Ghat_0}(X_i)}\right\}^2
 \le\frac{C_b}{\log n}.
\]
\item The fitted density obeys the global risk bound
\[
 H^2(f_{\Ghat_W},f_{G^*})
 \le C_b\frac{(\log n)^{d+1}}
 {n(\log\log n)^d}.
\]
\end{enumerate}
For $d\ge2$, the support bound in part \textup{(i)} is
$O\{(\log n/\log\log n)^d\}$; for $d=1$, it is $O(\log n)$.
\end{theorem}
```

## 9. Compiler-printed readable complete type

This is the actual `#check @ReweightedNPMLE.gaussian_exact_regularization_main` output from the successful helper; no theorem parameter is suppressed:

```text
@ReweightedNPMLE.gaussian_exact_regularization_main : ∀ {d : ℕ},
  0 < d →
    ∀ (K : Set (ReweightedNPMLE.Point d)),
      IsCompact K →
        K.Nonempty →
          ∀ {S b : ℝ},
            0 ≤ S →
              0 < b →
                (∀ u ∈ K, ‖u‖ ≤ S) →
                  ∃ (C : ℝ),
                    0 < C ∧
                      ∀ᶠ (n : ℕ) in Filter.atTop,
                        ∀ (Gstar : MeasureTheory.ProbabilityMeasure ↑K),
                          ∃ (G : Set (ReweightedNPMLE.GaussianDataWeight d n)),
                            MeasurableSet G ∧
                              (ReweightedNPMLE.gaussianDataWeightMeasure Gstar n
                                        (ReweightedNPMLE.gaussianPaperBalancedShape d n)).real
                                    Gᶜ ≤
                                  C * ↑n ^ (-b) ∧
                                ∀ p ∈ G,
                                  (∀ (i : Fin n),
                                      |p.2 i - 1| ≤ C / √(ReweightedNPMLE.gaussianPaperAugmentedDimension d n)) ∧
                                    p.2 ∈ ReweightedNPMLE.positiveVectors n ∧
                                      ∃ (μ : MeasureTheory.ProbabilityMeasure ↑K),
                                        ReweightedNPMLE.gaussianProbabilityOptimizerSet (fun (a : ↑K) => ↑a) p = {μ} ∧
                                          (↑μ).support.Finite ∧
                                            ↑(↑μ).support.ncard ≤
                                                C * ReweightedNPMLE.gaussianPaperAugmentedDimension d n ∧
                                              (∀
                                                  μ₀ ∈
                                                    ReweightedNPMLE.gaussianProbabilityOptimizerSet (fun (a : ↑K) => ↑a)
                                                      (p.1, 1),
                                                  0 ≤
                                                      ReweightedNPMLE.gaussianOrdinaryLikelihoodGap (fun (a : ↑K) => ↑a)
                                                        (p, μ, μ₀) ∧
                                                    ReweightedNPMLE.gaussianOrdinaryLikelihoodGap (fun (a : ↑K) => ↑a)
                                                          (p, μ, μ₀) ≤
                                                        C / Real.log ↑n ∧
                                                      ReweightedNPMLE.gaussianSquaredLogRatioGap (fun (a : ↑K) => ↑a)
                                                          (p, μ, μ₀) ≤
                                                        C / Real.log ↑n) ∧
                                                ReweightedNPMLE.hellingerSq MeasureTheory.volume
                                                    (ReweightedNPMLE.compactGaussianMixtureDensity μ)
                                                    (ReweightedNPMLE.compactGaussianMixtureDensity Gstar) ≤
                                                  C * ReweightedNPMLE.gaussianPaperRiskScale d n
```
