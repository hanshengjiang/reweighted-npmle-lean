# Release checks — 29 September 2026

**Verified source package:** `reweighted_npmle` version `0.1.0`, prepared for a
separate GitHub repository. The original checkout was at commit
`e8bf8f2832b3d3dfb94ebdf3e9d718ad3434eeb4`. The new repository, remote, release tag,
and hosted CI run have not been created by this task.

All **112 production Lean files are byte-for-byte unchanged** from the original
formalization. The release adds portable audits, frozen manuscript snapshots,
Apache-2.0 licensing, release integrity tooling, and updated publication docs.
The initial 17 integrity tests supplement the 11 existing tooling tests;
the later Comparator addendum expands the release checks further.

## Fresh standalone build

The package was staged outside the original checkout at:

```text
/private/tmp/npmle-release-2026-09-29/reweighted-npmle-lean
```

This directory initially contained no `.lake/`. `lake exe cache get` cloned all
nine pinned dependency repositories from their remote sources. It decompressed
official mathlib artifacts from an existing global download cache; it did not
redownload those cached artifact archives. The installed Lean toolchain was
reused. **No original project `.lake/` or compiled project proofs were copied.**
Before the build, the project `.olean` count was zero; the dependency directory
was a real directory, not a link to the author's checkout. See the
[environment record](audit/release-checks/fresh-environment.json) and
[dependency/cache log](audit/release-checks/fresh-cache-get.log).

Actual commands, run from the staged package root (each exit 0):

```sh
lake exe cache get > audit/release-checks/fresh-cache-get.log 2>&1
lake build > audit/release-checks/fresh-build.log 2>&1
```

The fresh build's final line was:

```text
Build completed successfully (3822 jobs).
```

The [complete build log](audit/release-checks/fresh-build.log) records **111
`Built ReweightedNPMLE...` entries and the built `Verification` target**, covering
all 112 production modules. It has no `Replayed ReweightedNPMLE...` entry.
Existing linter warnings were retained; no proof source was edited to suppress them.
Dependencies were cached, while the project's own sources were rebuilt.
This is a fresh standalone project build on the author's macOS machine, not
an independent-machine or Linux CI result.

Toolchain output:

```text
Lean (version 4.30.0, arm64-apple-darwin24.6.0, commit d024af099ca4bf2c86f649261ebf59565dc8c622, Release)
```

The manifest's mathlib commit is
`c5ea00351c28e24afc9f0f84379aa41082b1188f` (`v4.30.0`).

## Full verifier, independent axiom log, and data reproduction

Actual commands (each exit 0):

```sh
python3 scripts/verify.py > audit/release-checks/full-verifier.log 2>&1
lake env lean Verification.lean > audit/release-checks/fresh-verification.log 2>&1
python3 audit/main-result-2026-09-29/check_axiom_output.py --log audit/release-checks/fresh-verification.log > audit/release-checks/fresh-axiom-summary.log
python3 scripts/generate_numerical_data.py --check --audit-numerics > audit/release-checks/recorded-numerical-audit.log 2>&1
```

The complete [full-verifier output](audit/release-checks/full-verifier.log) was:

```text
Building both default Lean targets...
lake build passed
7 declarations: []
613 declarations: [Classical.choice, Quot.sound, propext]
1 declarations: [Quot.sound, propext]
Independent axiom audit passed: 621 unique declarations
All three numerical Lean artifacts exactly match all six source files
```

The build inside this later verifier was incremental, after the fresh build
above. The [independent raw axiom log](audit/release-checks/fresh-verification.log)
and [parsed inventory result](audit/release-checks/fresh-axiom-summary.log) are
also included. No unexpected axiom or `sorryAx` was reported.

The [extra numerical audit](audit/release-checks/recorded-numerical-audit.log)
checks recorded data and historical range semantics. Its six `literal bounds
FAIL` lines are the expected historical false exact-interval interpretations;
the corrected manuscript reports rounded extrema instead. The command exited
successfully, the precision checks passed, and all three generated Lean files
matched their six recorded inputs. See the
[correction record](docs/NUMERICAL_CORRECTIONS_NOTE.md). These checks do not
rerun or validate floating-point optimizers, quadrature, or simulations.

## Statement and semantic checks in the fresh build

Actual commands (each exit 0):

```sh
lake env lean audit/main-result-2026-09-29/StatementAudit.lean > audit/release-checks/release-main-type-axioms.log 2>&1
lake env lean audit/main-result-2026-09-29/FullType.lean > audit/release-checks/release-full-type.log 2>&1
lake env lean audit/main-result-2026-09-29/SemanticChecks.lean > audit/release-checks/release-semantic-checks.log 2>&1
lake env lean audit/release-checks/StatementCoverageChecks.lean > audit/release-checks/statement-coverage-types-axioms.log 2>&1
```

The first helper prints the main type and axiom dependencies. The second prints
its unabridged `pp.all` type. The semantic helper compiles ordinary optimizer
existence and probability-law checks and prints relevant supporting axioms.
The coverage helper checks **40 interfaces** used for the original paper's
18 named mathematical blocks; its 40 axiom lists all contain only `propext`,
`Classical.choice`, and `Quot.sound`. The full
[coverage output](audit/release-checks/statement-coverage-types-axioms.log) and
[summary](audit/release-checks/statement-coverage-summary.log) are retained.

Main axiom output:

```text
'ReweightedNPMLE.gaussian_exact_regularization_main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Read the [main statement audit](audit/main-result-2026-09-29/README.md) and the
[additional coverage review](audit/release-checks/coverage-review.md). The latter
records qualifications that a successful build cannot resolve on its own:

- The explicit tiny-perturbation theorem preserves separate constant dependencies;
  the common-constant wrapper alone allows more dependence on `L`.
- The conditional theorem permits dependence on fixed radius coefficient `C₀`
  and holds for sufficiently large sample sizes. Future prose should state this clearly.
- Dirichlet is defined by normalized Gamma weights, and finite empirical TV by
  grouped atom-mass differences. Separate identities to other possible library
  definitions are not claimed.
- The statistical interfaces give measurable good subsets; they do not all
  export exact-property-set measurability or a global measurable estimator map.
- V2/V3 merge matrix sensitivity into the expanded Hessian statement. The original
  has 18 named blocks, while each later version has 17. The main theorem's four
  conclusions and quantifiers remain unchanged.

No new Lean proof was supplied to bridge these wording/definition qualifications.
The appropriate existing stronger interfaces and their assumptions are identified
in the coverage review. The source review is not an independent human reproof of
every module.

## Comparator and independent-kernel addendum

The main theorem has now also passed a separate-statement Comparator check,
Nanoda's independent Rust kernel, and Lean's kernel replay. The target is
`ComparatorAudit.main`, a complete restatement proved by directly applying the
unchanged `ReweightedNPMLE.gaussian_exact_regularization_main`.
The [trusted challenge](audit/comparator/Challenge.lean) imports only Mathlib,
copies 24 explicit algebraic/statistical definitions, and has one intentional
placeholder for the challenged theorem. The [solution](audit/comparator/Solution.lean)
does not import that placeholder. The configuration has no definition holes
and permits only the same three foundational axioms.

Actual command (exit 0):

```sh
python3 scripts/run_comparator.py --comparator /private/tmp/npmle-comparator-tools/comparator/.lake/build/bin/comparator --exporter /private/tmp/npmle-comparator-tools/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export --landrun /private/tmp/npmle-comparator-tools/comparator/scripts/fake-landrun.sh --nanoda /private/tmp/npmle-comparator-tools/nanoda_lib/target/release/nanoda_bin --unsandboxed-development --output-dir audit/comparator/runs/02-nanoda-lean
```

The [raw log](audit/comparator/runs/02-nanoda-lean/comparator.log) ends:

```text
Running nanoda kernel on solution
Nanoda kernel accepts the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

The [run record](audit/comparator/runs/02-nanoda-lean/result.json) includes exact
commands, binary fingerprints, and unchanged before/after hashes for all 119
tracked inputs. The [audit addendum](audit/comparator/README.md) documents the
tool revisions, full reproduction steps, additional axiom output, and the
initial rejected challenge. That rejection came from differing Lean-generated
numeral-proof names; copying the original preceding algebraic definition fixed
it without changing the mathematical formula or weakening any check.

**Execution limitation:** the Mac run used upstream `fake-landrun.sh`, explicitly
unsandboxed. The comparison and both kernel checks actually ran; Linux Landrun
isolation did not. No Palomar submission, registration, or editorial review was
performed. The challenge's correspondence to `paper.tex` remains a source-level
mathematical review, not a consequence of Comparator alone.

The later `python3 scripts/verify.py > audit/comparator/final-verifier.log 2>&1`
also exited 0: incremental default build, all 621 axiom reports, and all three
generated numerical files passed again. See its [complete output](audit/comparator/final-verifier.log).
Production sources and the pinned Lean/Mathlib revisions remain unchanged.

Two [negative controls](audit/comparator/controls/README.md) were actually run:
doubling the risk-scale definition was rejected with a declaration mismatch,
and replacing the solution proof with `sorry` was rejected as an illegal
`sorryAx`. Each Comparator invocation exited 1 as expected; the control runner
exited 0 only after checking the exact diagnostics and unchanged sources.
Complete commands and outputs are preserved with the
[control records](audit/comparator/runs/03-negative-controls/summary.json).

The updated suite passed all **43 tests**, including two new Comparator-artifact
checks and 13 tests of the recorded-evidence validator. The final rerun is retained at
[audit/comparator/packaging-tests.log](audit/comparator/packaging-tests.log).
The portable `scripts/check_comparator_record.py` validates the preserved
successful run against the packaged sources; this checks recorded evidence
integrity and does not rerun a kernel. ZIP requirements include the actual
success log/record and negative-control evidence, not only the source setup.

Actual final integrity commands (exit 0):

```sh
python3 -m unittest discover -s tests -v > audit/comparator/packaging-tests.log 2>&1
python3 scripts/check_comparator_record.py > audit/comparator/record-integrity.log
python3 scripts/check_release.py > audit/comparator/release-integrity.log
python3 audit/main-result-2026-09-29/verify_sources.py > audit/comparator/source-preservation.log
```

The [record check](audit/comparator/record-integrity.log) reports 119 matching
source hashes and agreement of the recorded exit, both kernel acceptances,
log, configuration, and tool hashes. The [release integrity check](audit/comparator/release-integrity.log)
also verifies all 112 unchanged production sources and three frozen manuscripts.
These checks are repeated on the extracted final ZIP; their final output and
the ZIP's own SHA-256 are delivered beside the archive.

## Packaging, source integrity, and portability

Actual commands (each exit 0):

```sh
python3 -m unittest discover -s tests -v > audit/release-checks/packaging-tests.log 2>&1
python3 scripts/check_release.py > audit/release-checks/release-integrity.log 2>&1
python3 audit/main-result-2026-09-29/verify_sources.py > audit/release-checks/source-preservation.log
python3 audit/main-result-2026-09-29/compare_manuscripts.py > audit/release-checks/manuscript-main-comparison.log
```

All **28 tests passed**, including rejection of tampered proof/manuscript files,
unsafe or incomplete ZIPs, missing audits, checksum mismatches, and broken or
escaping documentation links. See the [test log](audit/release-checks/packaging-tests.log).
The [release integrity log](audit/release-checks/release-integrity.log) confirms
112 unchanged production Lean sources, the three frozen manuscript hashes, and
portable local Markdown links. The original main audit's raw logs are preserved
unchanged and clearly labeled as historical; their author-machine paths are not
required to rerun the portable helpers.

The [current original paper](docs/manuscript/paper.tex), v2 and v3 are frozen with
[full-file hashes](docs/manuscript/SHA256SUMS). The older `docs/paper.tex` is retained
so previous records remain interpretable. Future v4/v5 writing revisions should
not silently replace this release's reference texts.

The final export is produced with `scripts/export_repository.py`; it contains
an `EXPORT_MANIFEST.sha256` covering every payload file. The delivered ZIP is
also checked with `scripts/check_release.py --zip ...` and extracted for
relocation checks. The final ZIP's own hash and extraction-validation log are
delivered alongside it, since a ZIP cannot contain its own full-file checksum.
To repeat these checks:

```sh
python3 scripts/check_release.py --zip /path/to/reweighted-npmle-lean-v0.1.0.zip
python3 -m unittest discover -s tests -v
```

Neither `.lake/`, the parent checkout's Git metadata, scratch `Check.lean`, nor
Python bytecode is shipped. The proof sources in the ZIP can therefore be built
using its own pinned dependencies. The license is [Apache-2.0](LICENSE), with
[separate manuscript/input scope](LICENSE_SCOPE.md).

## Checks not claimed

No GitHub repository was created, no content was uploaded, and no hosted CI run
or release tag was created. No fresh Lean compiler installation, cache-free
mathlib rebuild, Linux Landrun isolation, Palomar registration, independent human review, simulation
rerun, or LaTeX/PDF build was performed in this release task. The manuscript
sources are reference material rather than a complete PDF-build bundle.
