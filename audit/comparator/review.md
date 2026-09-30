# Source review of the Comparator challenge

Reviewed on 29 September 2026 by a separate audit agent. This is an additional
source and statement review, not an independent human referee report or a
claim that an independent implementation formalized the paper from scratch.
The challenge deliberately reproduces the existing definition bodies, with
only Mathlib imports; the mathematical meaning was checked separately against
the frozen [paper.tex](../../docs/manuscript/paper.tex#L273).

**Finding:** the challenge preserves the four displayed conclusions of
`thm:main`, their domains, constant dependencies, and quantifier order. It
does not introduce a finite candidate grid, a finite true mixture, or an
assumed intermediate mathematical lemma. The qualifications below remain
part of the interpretation.

## Reviewed inputs

| File | SHA-256 at review |
| --- | --- |
| [Challenge.lean](Challenge.lean) | `dce44bcfe399d2f4fb6fde981e59144644e775971b271993fec112def53a7db9` |
| [Solution.lean](Solution.lean) | `27058585df21d8752b1cfe8f9f447a99da389e6fa0a4bd06e51f0b90a76fd4ab` |
| [paper.tex](../../docs/manuscript/paper.tex) | `4166c2e5db94f7fd267b79a97e3ef6ed7803709a3ea3a9ce2fc603002b76f385` |

The primary comparison is the model and conventions at manuscript lines
273–305, Gamma weights at 309–320, scales at 363–369, and `thm:main` at
373–409. Versions 2 and 3 are not substituted for this reference.

## Meaning and clause comparison

Write `P(K)` for all Borel probability measures on the compact subtype K,
identified with ambient probability measures carried by K. The challenge's
`Point d` is Euclidean real d-space with the Euclidean norm. Its density and
objective are exactly

\[
 f_\mu(x)=\int_K(2\pi)^{-d/2}e^{-\|x-\theta\|^2/2}\,d\mu(\theta),
 \qquad L_w(\mu;x)=\sum_{i=1}^n w_i\log f_\mu(x_i).
\]

`gaussianProbabilityOptimizerSet` uses `IsMaxOn univ`: optimization is over
every `ProbabilityMeasure K`, not over an atomic representation or a numerical
grid. The full source and definition map are in [Challenge.lean](Challenge.lean)
and [DEFINITION_MAP.md](DEFINITION_MAP.md).

| Paper requirement | Challenge meaning and assessment |
| --- | --- |
| Fixed positive dimension and nonempty compact K in a bounded Euclidean ball | `hd`, `hKcompact`, `hKnonempty`, and `hKbound` encode these assumptions. `S ≥ 0` is redundant given nonempty K and the norm bound, not a stronger substantive hypothesis. |
| Correctly specified iid Gaussian location-mixture data | `compactGaussianSampleMeasure` is the product of the mixture-density laws. The latent-variable formulation is represented by its induced data law; [GaussianSampling.lean](../../ReweightedNPMLE/GaussianSampling.lean#L23) proves that equality. |
| Independent Gamma weights, shape and rate both alpha | `gaussianDataWeightMeasure` is a product of the data measure and a product of Mathlib `gammaMeasure alpha alpha`. Inspection of the pinned Gamma density gives `r^a / Gamma(a) * x^(a-1) * exp(-r*x)` on nonnegative x, so the second parameter is the rate. |
| Balanced concentration | The copied scale definitions give `r = (log n / log(log n))^d`, `rbar = r + log n`, and `alpha = rbar * log n`. |
| One common high-probability event | One measurable set G has complement probability at most `C * n^(-b)`, and all four conclusions hold for each point in G. The eventual sample-size restriction ensures positive Gamma shape; this is a probability law, not an arbitrary infinite measure whose `.real` could erase an infinite value. |
| (i) Existence, uniqueness, and finite support | `∃ μ` and `optimizerSet = {μ}` provide existence and uniqueness together. `support.Finite` is explicit before the `ncard` bound, so the convention for infinite-set `ncard` is not used to simulate sparsity. Subtype support agrees with ambient support under the closed inclusion of compact K. |
| (ii) Uniformly small perturbation | `∀ i, abs(w_i - 1) ≤ C / sqrt(rbar)` is exactly the finite-coordinate maximum bound. Positive weights are an additional valid conclusion. |
| (iii) Every ordinary NPMLE | The universal quantifier over ordinary optimizers is inside the same event and follows the unique weighted optimizer. The gap subtracts the weighted optimizer's ordinary likelihood from the ordinary optimizer's ordinary likelihood; both use weights one. There is no division by n. The second expression is the sum of squared log density ratios, not a squared sum or an average. |
| (iv) Global Hellinger risk | `hellingerSq volume` integrates `(sqrt(p)-sqrt(q))^2` over all Euclidean space, with no factor 1/2 and no restriction to data points or a bounded region. Its rate is `(log n / log(log n))^d * log n / n`, algebraically the displayed paper rate. |
| Final dimension-specific support orders | The explicit `C * rbar` bound implies the stated asymptotic regimes; a separately proved [support refinement](../../ReweightedNPMLE/GaussianSupportRefinements.lean#L29) exports these orders. That corollary is not an additional target of this Comparator configuration. |

The complete quantifier order is

\[
 \exists C>0\;\exists n_0\;\forall n\ge n_0\;\forall G^*\in P(K)\;
 \exists E\;\forall(x,w)\in E\;\exists\widehat G_w\;
 \forall\widehat G_0\in\operatorname{argmax}_{\mu\in P(K)}L_1(\mu;x).
\]

Thus C and the sample threshold may depend on fixed d, K, S, b, but not on n,
the true mixing law, the data, weights, or either optimizer. The event may
depend on n and the true law. It is a guarantee for each sufficiently large n,
not one event simultaneous over all n. The challenge has implicit parameters
d, S, b; it has no surrounding section assumptions or caller-supplied
typeclass assumptions. The concrete measurable and topological instances are
inherited from the Euclidean space and its subtype.

## Qualifications and proof boundary

- The formal conclusion supplies a measurable good subset. It does not
  separately assert measurability of the entire set defined by all four
  properties, or provide a globally measurable estimator selection. This
  agrees with the usual high-probability reading used in the original audit.
- Ordinary-NPMLE existence is not a separate conjunct of this challenge.
  Its existence is proved by the unchanged project and is checked in the
  previously compiled [SemanticChecks.lean](../main-result-2026-09-29/SemanticChecks.lean).
  This review inspected that helper and the underlying optimizer domain; it
  did not compile the helper again. The universal ordinary-optimizer clause
  is not evidence of existence by itself.
- No intermediate lemma is assumed in the challenge: the only theorem is
  the target, with the intentional `sorry` expected for a challenge. The
  solution imports the production theorem, contains no `sorry`, and proves
  the explicitly written target by a direct application. The challenge's
  placeholder must not enter the solution; forbidden axiom dependencies and
  recursive declaration agreement are for the actual Comparator run to
  check. Source inspection alone is not a replacement for that run.
- This challenge is a separately elaborated copy of the mathematical
  definitions, not an independently invented encoding. Comparator agreement
  does not itself establish correspondence with prose. The clause review
  above is the additional interpretation check; it is not a machine proof
  of the LaTeX-to-Lean translation.

## Source checks actually run

The final challenge includes 24 definitions: the 23 definitions needed to
explain the statistical type, plus the original explicit algebraic definition
`gaussianScore x theta = inner x theta - norm(theta)^2 / 2`, inserted in its
original position before `gaussianConstant`. This reproduces the automatically
generated numeral proof name `gaussianScore._proof_1`. It is not an assumed
lemma or an additional statistical hypothesis.

The first actual Comparator run rejected the initial challenge despite
identical source formulas: its elaborated `gaussianKernel` referenced the
generated helper `gaussianConstant._proof_1`, while the production definition
referenced `gaussianScore._proof_1`. I inspected the
[initial diagnostic difference](diagnostics/initial-definition-difference.patch)
and the final inserted source definition. This correction changes neither
the target type nor any statistical definition body. It illustrates why the
source checks below do not establish Comparator's exact declaration equality.

From the package root, the following final Python command exited 0. It checks exact
source copies and the explicitly written statement. It does not check Lean
elaboration, recursive compiled-declaration equality, or kernel validity.
Those results belong in the [Comparator run record](README.md).

```sh
python3 - <<'PY'
from pathlib import Path
import re
root = Path.cwd()
challenge = (root / 'audit/comparator/Challenge.lean').read_text()
blocks = re.findall(
    r'-- Source: ([^:]+):(\d+)-(\d+)\n(.*?)(?=\n-- Source:|\nend ReweightedNPMLE)',
    challenge, re.S)
assert len(blocks) == 24
for source, start, end, body in blocks:
    original = '\n'.join((root / source).read_text().splitlines()[int(start)-1:int(end)])
    body = re.sub(r'^--[^\n]*\n', '', body, flags=re.M)
    assert body.strip() == original.strip(), source
print('PASS: all 24 Challenge definition bodies are exact source copies at their stated locations')
imports = re.findall(r'^import (.*)$', challenge, re.M)
assert len(imports) == 11 and all(x.startswith('Mathlib.') for x in imports)
print('PASS: exactly 11 imports, all from Mathlib; no project imports')
assert len(re.findall(r'\bsorry\b', challenge)) == 1
assert not re.findall(r'^\s*(?:axiom|opaque|instance|variable)\b', challenge, re.M)
print('PASS: one target proof placeholder; no axiom, opaque, instance, or variable declarations')
solution = (root / 'audit/comparator/Solution.lean').read_text()
original = (root / 'ReweightedNPMLE/GaussianMainTheorem.lean').read_text()
def typ(text, name):
    return text.split('theorem ' + name, 1)[1].split(':= by', 1)[0].strip()
assert typ(challenge, 'main') == typ(solution, 'main') == typ(original, 'gaussian_exact_regularization_main')
assert solution.split(':= by', 1)[1].split('end ComparatorAudit', 1)[0].strip() == \
    'exact gaussian_exact_regularization_main hd K hKcompact hKnonempty hS hb hKbound'
assert 'sorry' not in solution and 'import audit.comparator.Challenge' not in solution
print('PASS: Challenge/Solution/production statement texts identical after theorem name; adapter applies existing theorem directly')
PY
```

Output:

```text
PASS: all 24 Challenge definition bodies are exact source copies at their stated locations
PASS: exactly 11 imports, all from Mathlib; no project imports
PASS: one target proof placeholder; no axiom, opaque, instance, or variable declarations
PASS: Challenge/Solution/production statement texts identical after theorem name; adapter applies existing theorem directly
```

The reviewed hashes above were obtained with:

```sh
shasum -a 256 audit/comparator/Challenge.lean audit/comparator/Solution.lean docs/manuscript/paper.tex
```

I also ran this comparison of the diagnostic output supplied by the challenge
preparation step; it exited 0 with no output:

```sh
cmp audit/comparator/diagnostics/corrected-challenge-definitions.log audit/comparator/diagnostics/production-definitions.log
```

Those files print the original 23 semantic definitions and the relevant
generated numeral helper. Their equality is a diagnostic observation, not a
substitute for the complete Comparator run. No Lean compiler or independent
kernel was newly invoked by this source-review subtask.

### Historical initial source check

The initial challenge had SHA-256
`a36360ad2638215328e20e0967c5ced21db37529b60b4b29dbaaa1b85e155cb4`
and 23 definitions. Before the first Comparator run, the Python command above
was run with both occurrences of `24` replaced by `23` and without the line
removing definition comments. It exited 0 and printed:

```text
PASS: all 23 Challenge definition bodies are exact source copies at their stated locations
PASS: exactly 11 imports, all from Mathlib; no project imports
PASS: one target proof placeholder; no axiom, opaque, instance, or variable declarations
PASS: Challenge/Solution/production statement texts identical after theorem name; adapter applies existing theorem directly
```

This historical result correctly checked source text; it did not anticipate
or rule out the subsequently detected compiled declaration mismatch. The
final source check and reviewed hash supersede it for the released challenge.

No production Lean source or frozen manuscript was modified for this review.
