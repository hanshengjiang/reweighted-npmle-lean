# Trusted statement and definition map

The reference is the frozen [`docs/manuscript/paper.tex`](../../docs/manuscript/paper.tex),
Theorem `thm:main` (lines 373–409), with the model, objective, weights, and Hellinger
convention at lines 274–312 and scales at lines 364–369. The challenge is not
based on `paper_v2.tex` or `paper_v3.tex`.

[`Challenge.lean`](Challenge.lean) imports only 11 Mathlib modules. It redeclares
24 definitions under their original `ReweightedNPMLE` qualified names, then
states `ComparatorAudit.main` with a single intentional `sorry` placeholder.
There are no project theorem imports, additional postulates, or assumed
intermediate mathematical results in the challenge. The solution does not
import the challenge. [`Solution.lean`](Solution.lean) repeats the entire type
and proves it by applying the unchanged
`ReweightedNPMLE.gaussian_exact_regularization_main` from
[`GaussianMainTheorem.lean:56`](../../ReweightedNPMLE/GaussianMainTheorem.lean#L56).

These definition bodies were copied from the production source, then read
against the manuscript's meanings below. This is an isolated, explicitly
reviewable specification, not a claim that independently copying or comparing
Lean syntax proves its correspondence with prose. The expected statement and
its mathematical interpretation remain part of the trusted audit input.
Comparator's role is to check that the submitted solution proves this fixed
statement with the same dependent definitions and permitted axioms.

## Project definitions fixed by the challenge

Every project-specific definition in the type is expanded here, recursively.
No production definition is supplied by an import. No project instance is needed
to elaborate this statement: the measurable, topological, algebraic, and volume
instances come from the pinned Mathlib imports. Source comments beside each
challenge definition give the same line ranges as this table.

| Definition (`ReweightedNPMLE.` prefix) | Production source | Meaning |
|---|---|---|
| `Point` | [Gaussian.lean:21–21](../../ReweightedNPMLE/Gaussian.lean#L21) | Euclidean space $\mathbb R^d$ with its Euclidean norm. |
| `gaussianScore` | [Gaussian.lean:24–25](../../ReweightedNPMLE/Gaussian.lean#L24) | $\langle x,\theta\rangle-\|\theta\|^2/2$; included before the Gaussian constant to preserve the generated numeral-proof name (see below). |
| `gaussianConstant` | [Gaussian.lean:28–29](../../ReweightedNPMLE/Gaussian.lean#L28) | $c_d=(2\pi)^{-d/2}$ (real exponent). |
| `gaussianKernel` | [Gaussian.lean:36–37](../../ReweightedNPMLE/Gaussian.lean#L36) | $\phi_d(x-u)=c_d\exp(-\|x-u\|^2/2)$, identity covariance. |
| `gaussianMixture` | [GaussianMixtureMeasure.lean:19–21](../../ReweightedNPMLE/GaussianMixtureMeasure.lean#L19) | $f_{\mu,\theta}(x)=\int\phi_d(x-\theta(a))\,d\mu(a)$. |
| `compactGaussianMixtureDensity` | [GaussianNearMLE.lean:22–24](../../ReweightedNPMLE/GaussianNearMLE.lean#L22) | $f_\mu(x)=\int_K\phi_d(x-u)\,d\mu(u)$ for a probability measure on the subtype $K$. |
| `weightedLogLikelihood` | [Weights.lean:26–27](../../ReweightedNPMLE/Weights.lean#L26) | $\sum_i w_i\log v_i$, a total sum. |
| `IsMaxOn` | [Weights.lean:30–31](../../ReweightedNPMLE/Weights.lean#L30) | $v\in C$ and $\forall u\in C, f(u)\le f(v)$. |
| `positiveVectors` | [Weights.lean:34–35](../../ReweightedNPMLE/Weights.lean#L34) | All coordinates are strictly positive; no sum normalization. |
| `probabilityMixtureValue` | [ProbabilityOptimizerFiber.lean:24–26](../../ReweightedNPMLE/ProbabilityOptimizerFiber.lean#L24) | $i\mapsto\int A(u,i)\,d\mu(u)$. |
| `GaussianDataWeight` | [GaussianJointEvents.lean:18–18](../../ReweightedNPMLE/GaussianJointEvents.lean#L18) | Data–weight pairs $p=(x,w)\in(\mathbb R^d)^n\times\mathbb R^n$. |
| `gaussianProbabilityLogLikelihood` | [GaussianJointEvents.lean:20–23](../../ReweightedNPMLE/GaussianJointEvents.lean#L20) | $L_w(\mu;x)=\sum_i w_i\log f_\mu(x_i)$. |
| `gaussianProbabilityOptimizerSet` | [GaussianJointEvents.lean:25–27](../../ReweightedNPMLE/GaussianJointEvents.lean#L25) | All maximizers over the entire type of probability measures on the given parameter domain. |
| `gaussianOrdinaryLikelihoodGap` | [GaussianJointEvents.lean:82–86](../../ReweightedNPMLE/GaussianJointEvents.lean#L82) | $\Delta(\mu,\mu_0;x)=L_1(\mu_0;x)-L_1(\mu;x)$. |
| `gaussianSquaredLogRatioGap` | [GaussianJointEvents.lean:113–118](../../ReweightedNPMLE/GaussianJointEvents.lean#L113) | $Q(\mu,\mu_0;x)=\sum_i[\log(f_\mu(x_i)/f_{\mu_0}(x_i))]^2$. |
| `gaussianPaperLogScale` | [GaussianNearMLERate.lean:24–25](../../ReweightedNPMLE/GaussianNearMLERate.lean#L24) | $q_n=\log n/\log\log n$. |
| `gaussianPaperEffectiveDimension` | [GaussianPaperScales.lean:19–20](../../ReweightedNPMLE/GaussianPaperScales.lean#L19) | $r_n=q_n^d$. |
| `gaussianPaperAugmentedDimension` | [GaussianPaperScales.lean:22–23](../../ReweightedNPMLE/GaussianPaperScales.lean#L22) | $\bar r_n=r_n+\log n$. |
| `gaussianPaperBalancedShape` | [GaussianPaperScales.lean:25–26](../../ReweightedNPMLE/GaussianPaperScales.lean#L25) | $\alpha_n=\bar r_n\log n$. |
| `gaussianPaperRiskScale` | [GaussianMainTheorem.lean:15–16](../../ReweightedNPMLE/GaussianMainTheorem.lean#L15) | $R_n=q_n^d\log n/n=(\log n)^{d+1}/[n(\log\log n)^d]$. |
| `compactGaussianSampleMeasure` | [GaussianSampling.lean:18–21](../../ReweightedNPMLE/GaussianSampling.lean#L18) | Product of $n$ copies of $f_{G_*}(x)\,dx$. |
| `gammaProductMeasure` | [DirichletIndependence.lean:115–117](../../ReweightedNPMLE/DirichletIndependence.lean#L115) | Product of $n$ Gamma laws with shape $a$ and rate $r$. |
| `gaussianDataWeightMeasure` | [GaussianJointTheorems.lean:19–21](../../ReweightedNPMLE/GaussianJointTheorems.lean#L19) | Product of the data law and independent Gamma weights with shape and rate both $\alpha$. |
| `hellingerSq` | [Hellinger.lean:23–25](../../ReweightedNPMLE/Hellinger.lean#L23) | $H^2(f,g)=\int(\sqrt f-\sqrt g)^2\,dx$; no factor $1/2$. |

`gaussianScore` is an additional explicit algebraic definition included for
elaboration compatibility. The first Comparator run rejected `gaussianKernel`:
the identical formula had different references to automatically generated
proofs that the numeral 2 is at least 2. The production module first creates
`gaussianScore._proof_1`, reused by `gaussianConstant` and `gaussianKernel`;
the initial standalone challenge first created `gaussianConstant._proof_1`.
Putting the original `gaussianScore` definition before `gaussianConstant`
reproduces the production helper name and proof without changing any formula,
assuming any lemma, adding definition holes, or weakening Comparator. The
initial `pp.all` diagnostic difference is retained in
[`diagnostics/initial-definition-difference.patch`](diagnostics/initial-definition-difference.patch).

The machine-readable source ranges are in [`definition-map.json`](definition-map.json).

## Ordinary mathematical reading of the complete type

For any positive integer $d$, nonempty compact $K\subset\mathbb R^d$, $S\ge0$,
$b>0$, and $\|u\|\le S$ for all $u\in K$, there is a finite positive real constant
$C$ and a threshold $n_0$ such that, for every $n\ge n_0$ and every Borel
probability law $G_*\in\mathcal P(K)$, there is a measurable set
$G\subset(\mathbb R^d)^n\times\mathbb R^n$ with

$$
P_{G_*,n}(G^c)\le Cn^{-b},\qquad
P_{G_*,n}=(f_{G_*}(x)\,dx)^{\otimes n}
\otimes\operatorname{Gamma}(\alpha_n,\operatorname{rate}\alpha_n)^{\otimes n},
$$

such that every $(x,w)\in G$ satisfies all of the following, simultaneously:

1. $|w_i-1|\le C/\sqrt{\bar r_n}$ and $w_i>0$ for every $i$.
2. There is a probability measure $\mu\in\mathcal P(K)$ such that
   $\operatorname{argmax}_{\nu\in\mathcal P(K)}L_w(\nu;x)=\{\mu\}$,
   its topological support is finite, and $\#\operatorname{supp}\mu\le C\bar r_n$.
3. For every $\mu_0\in\operatorname{argmax}_{\nu\in\mathcal P(K)}L_1(\nu;x)$,
   $0\le\Delta(\mu,\mu_0;x)\le C/\log n$ and
   $Q(\mu,\mu_0;x)\le C/\log n$.
4. $H^2(f_\mu,f_{G_*})\le CR_n$.

The same $C$ occurs in the failure probability and all bounds. Both $C$ and
$n_0$ precede the quantifier over $G_*$ and therefore are uniform over all true
mixing laws on $K$. The good set may depend on $G_*$ and $n$; the optimizer
may depend on the realized data and weights. The theorem's implicit parameters
are `{d : ℕ}` and `{S b : ℝ}`. There are no section parameters or extra typeclass
hypotheses beyond the explicit compactness, nonemptiness, positivity, and bound
hypotheses displayed in `Challenge.lean`. Generic helper definitions carry the
`[MeasurableSpace Θ]` or `[MeasurableSpace Ω]` parameters shown in their source;
these are instantiated with Mathlib's usual Borel structures at the target.

The optimizer domain is the full space of probability measures on $K$, not a
finite grid or an a priori atomic family. `support.Finite` explicitly accompanies
`support.ncard`, preventing the totalized cardinality of an infinite set from
making the support bound vacuous. Hellinger integrates over all Euclidean space,
not the observed sample or a bounded subset. Lean's `ProbabilityMeasure`,
`Measure.real`, `Measure.support`, and `Set.ncard` are Mathlib definitions, not
project-specific wrappers.

## Interpretation qualifications retained from the original audit

- The type gives a measurable good subset on which all conclusions hold; it does
  not assert that the entire property set is measurable or construct a global
  measurable optimizer selection.
- Ordinary optimizer existence is not an explicit conjunct of this main type.
  It is established separately in the production development; it is not inserted
  as an unproved premise in the challenge. The new comparison deliberately keeps
  the existing exact theorem type rather than silently strengthening it.
- The closed norm bound $\|u\|\le S$ is sufficient even if the paper's $B(0,S)$
  is read as an open ball. The manuscript explicitly assumes nonemptiness and $d\ge1$ at line 275;
  these hypotheses are explicit in Lean as well.
- The scale definitions use total real logarithms and division at small sample
  sizes. The target is eventual in $n$; production proofs establish positive
  Gamma shape eventually, genuine probability laws, and positive normalized
  Gaussian mixture densities. Comparator fixes the definitions but does not
  replace these semantic observations or turn the target into a statement for
  all small $n$.
- The concluding asymptotic discussion for $d\ge2$ and $d=1$ follows from the
  displayed $\bar r_n$ bound; it is not an additional conjunct of this target.

The original expanded statement audit remains at
[`audit/main-result-2026-09-29/README.md`](../main-result-2026-09-29/README.md).
No claim in this map is a substitute for the actual Comparator result, tool
versions, command logs, or trust limitations recorded alongside it.
