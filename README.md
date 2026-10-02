# Reweighted Gaussian-mixture NPMLE: Lean 4 companion

The primary document is **[`paper.tex`](docs/manuscript/paper.tex)**. An updated version is available on **[arXiv](https://arxiv.org/abs/2610.01088)**.

This package contains Lean 4 proofs of its main exact-regularization theorem and supporting results.

The main declaration is
[`ReweightedNPMLE.gaussian_exact_regularization_main`](ReweightedNPMLE/GaussianMainTheorem.lean#L56).
It optimizes over all probability measures on a compact parameter space and
proves uniqueness, finite topological support, perturbation and likelihood
bounds, and a global Hellinger bound on a common high-probability event.

## Build and verify

Install Git and [elan](https://github.com/leanprover/elan). This package pins
Lean **v4.30.0** and mathlib **v4.30.0**, including exact transitive dependency
revisions in `lake-manifest.json`.

From this directory:

```sh
lake exe cache get
python3 scripts/verify.py
python3 -m unittest discover -s tests -v
python3 scripts/check_release.py
```

Python 3.10+ is needed for the verification and packaging utilities. The Lean
proof checks themselves can instead be run directly:

```sh
lake build
lake env lean Verification.lean
```

The cache command obtains compiled **mathlib dependencies**. It does not supply
compiled versions of this project's proofs. Both `ReweightedNPMLE` and
`Verification` are default build targets. The verifier checks all 621 listed
axiom reports and exact reproduction of the bundled numerical certificate
sources. Allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.

See [RELEASE_CHECKS.md](RELEASE_CHECKS.md) for the checks actually performed on
this release, raw logs, and limitations. The included GitHub workflow will
run after upload; a future GitHub Actions run is not claimed as completed.

## Statement correspondence and frozen manuscript

- [Main theorem audit](audit/main-result-2026-09-29/README.md): complete formal
  type, all implicit assumptions, recursive definition expansions, mathematical
  translation, clause comparison, and actual compiler/axiom output.
- [Main theorem Comparator audit](audit/comparator/README.md): separately
  specified challenge, wrapper using the existing theorem, tool configuration,
  reproduction instructions, and the scope and outcome of recorded checks.
- [Release coverage review](audit/release-checks/coverage-review.md): additional
  source review of the other named mathematical statements and version differences.
- [Paper coverage map](PAPER_COVERAGE.md): label-to-declaration mapping from the
  earlier full development audit; read it with the release review.
- [Frozen manuscript snapshots](docs/manuscript/README.md): byte-for-byte copies
  of `paper.tex`, `paper_v2.tex`, and `paper_v3.tex` as of 29 September 2026,
  with SHA-256 hashes. The original [`paper.tex`](docs/manuscript/paper.tex)
  is the primary release reference.
- [Reference provenance](docs/PAPER_REFERENCE.md): identifies the older bundled
  snapshot and the current release reference.

Later writing revisions such as v4 or v5 should not silently replace these
snapshots. Cite this release with the paper; if assumptions, definitions,
quantifiers, constants, or conclusions change, record a new correspondence
review. The LaTeX sources are reference text: figure assets and the full paper
build environment are not bundled.

Compilation checks the encoded propositions. The separate source audits
address their correspondence to the manuscript; neither is a claim of an
independent human review of every proof. The main theorem gives a measurable
good subset and pointwise unique optimizer existence. Its type does not
separately export a global measurable estimator selection.

The main theorem passed Comparator's separate-statement comparison, its axiom
allowlist check, Nanoda's independent kernel, and Lean's kernel replay. This
local macOS run used the upstream unsandboxed development shim; it is not a
Linux sandbox verification or Palomar registration. This does not mechanically establish
that the challenge expresses the LaTeX statement; the challenge and its
definitions remain part of the statement review. Read its audit record for
the exact tool versions, execution conditions, and checks actually completed.

## Main interfaces

All names below are in namespace `ReweightedNPMLE`.

| Result | Declaration | File |
| --- | --- | --- |
| Main theorem | `gaussian_exact_regularization_main` | [GaussianMainTheorem](ReweightedNPMLE/GaussianMainTheorem.lean) |
| Tiny perturbations | `gaussian_exact_regularization_tiny` | [GaussianMainTheorem](ReweightedNPMLE/GaussianMainTheorem.lean) |
| Weak consistency | `gaussian_reweighted_optimizer_weak_consistency` | [GaussianJointConsistency](ReweightedNPMLE/GaussianJointConsistency.lean) |
| Approximate optimizers | `gaussian_approximate_optimizer_joint_robustness` | [GaussianApproxTheorem](ReweightedNPMLE/GaussianApproxTheorem.lean) |
| Uniform near-MLE risk | `gaussian_uniform_nearMLE_paper_theorem` | [GaussianNearMLETheorem](ReweightedNPMLE/GaussianNearMLETheorem.lean) |
| Effective dimension | `effective_dimension_full_support` | [FullEffectiveDimension](ReweightedNPMLE/FullEffectiveDimension.lean) |

The umbrella [ReweightedNPMLE.lean](ReweightedNPMLE.lean) also imports finite
recorded-numerical certificates. Those certify recorded data and reporting
arithmetic; they do not prove correctness of floating-point optimizers,
quadrature, continuous searches, or algorithmic convergence. See
[data/README.md](data/README.md) and the
[numerical correction record](docs/NUMERICAL_CORRECTIONS_NOTE.md).

## License and publication

The code and package/audit documentation are **Apache-2.0**; see [LICENSE](LICENSE)
and [LICENSE_SCOPE.md](LICENSE_SCOPE.md). The reference manuscripts retain their
copyright and are outside the code license.

[PUBLICATION.md](PUBLICATION.md) explains how to upload the extracted package
as a repository root and create a tagged release. No repository has been
created or uploaded by the packaging process. `.lake/`, Git metadata, the
original scratch `Check.lean`, and Python bytecode are excluded from exports.
