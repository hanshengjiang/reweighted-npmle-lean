# Separate statement and exported-proof audit

This adds Comparator verification to the earlier source-level audit of
`ReweightedNPMLE.gaussian_exact_regularization_main`. The reference remains
the frozen [paper.tex](../../docs/manuscript/paper.tex), Theorem `thm:main`.
No production Lean source or dependency revision is changed.

## Actual result

**Passed on 29 September 2026:** separate statement/declaration comparison,
the three-axiom policy, Nanoda independent-kernel checking, and Lean kernel
replay, for `ComparatorAudit.main` proved by the original main theorem.
The [full run log](runs/02-nanoda-lean/comparator.log) and
[machine-readable record](runs/02-nanoda-lean/result.json) preserve the evidence.
The record shows exit 0 and unchanged hashes for all 119 fingerprinted inputs,
including all 112 production Lean files, the challenge, solution, configuration,
toolchain, dependency pins, Lake configuration, and primary manuscript.

Actual command, from the staged package root:

```sh
python3 scripts/run_comparator.py \
  --comparator /private/tmp/npmle-comparator-tools/comparator/.lake/build/bin/comparator \
  --exporter /private/tmp/npmle-comparator-tools/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export \
  --landrun /private/tmp/npmle-comparator-tools/comparator/scripts/fake-landrun.sh \
  --nanoda /private/tmp/npmle-comparator-tools/nanoda_lib/target/release/nanoda_bin \
  --unsandboxed-development \
  --output-dir audit/comparator/runs/02-nanoda-lean
```

The log ends:

```text
Running nanoda kernel on solution
Nanoda kernel accepts the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

This run took approximately 107 seconds. It used upstream's **unsandboxed
development shim on macOS**. The log explicitly warns about this; successful
mathematical comparison and kernel checks do not establish sandbox isolation.

Additional command (exit 0):

```sh
lake env lean audit/comparator/PrintAxioms.lean > audit/comparator/axioms.log 2>&1
```

Complete [axiom output](axioms.log):

```text
'ComparatorAudit.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReweightedNPMLE.gaussian_exact_regularization_main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The [full verifier rerun](final-verifier.log) also passed: `lake build`, all
621 expected axiom reports, and exact regeneration of all three numerical
certificate files. That build was incremental, following the earlier fresh
standalone build recorded in [RELEASE_CHECKS.md](../../RELEASE_CHECKS.md).

## Initial rejected challenge and correction

The [first run](runs/01-lean-replay/comparator.log), explicitly requested with
`--skip-nanoda`, exited 1 before kernel replay:

```text
uncaught exception: Const does not match between challenge and target 'ReweightedNPMLE.gaussianKernel'
```

The printed Gaussian formula was unchanged, but elaborating its numeral `2`
reused differently named generated proof constants. In the production module,
the earlier `gaussianScore` definition creates `gaussianScore._proof_1`.
The initial challenge omitted that preceding definition and instead generated
`gaussianConstant._proof_1`. Comparator compares these dependencies exactly.

The corrected challenge includes the original algebraic `gaussianScore`
definition in its original relative order. It now contains 24 copied
definitions; no production proof, statistical formula, assumption, axiom
allowlist, or Comparator implementation was changed. No definition hole was
introduced. The diagnostic printouts and renewed source review are preserved
in [the definition map](DEFINITION_MAP.md) and [review](review.md).

## Negative controls

Two deliberately invalid inputs were also checked. Both actual Comparator
processes exited 1 for the intended reason, so the negative-control runner
exited 0. The [summary](runs/03-negative-controls/summary.json) and complete
[definition-drift log](runs/03-negative-controls/changed-definition.log) and
[unproved-solution log](runs/03-negative-controls/unproved-solution.log) are retained.

```text
Const does not match between challenge and target 'ReweightedNPMLE.gaussianPaperRiskScale'
Illegal axiom detected: 'sorryAx'
```

The first control multiplies the risk-scale definition by two while retaining
the outer theorem syntax. The second replaces the solution proof with `sorry`.
They demonstrate rejection of definition drift and an unproved solution.
The [control modules and instructions](controls/README.md) are isolated from
production imports and default build targets. Nanoda was disabled for these
controls because rejection occurs before kernel replay. All normal source
hashes remained unchanged during both runs.

## Statement and proof separation

- [Challenge.lean](Challenge.lean) imports only Mathlib, explicitly defines the
  mathematical quantities, and states the complete expected proposition as
  `ComparatorAudit.main`. Its one intentional `sorry` marks the theorem to be
  proved. It is not an assumption available to the solution.
- [Solution.lean](Solution.lean) imports the existing production theorem, repeats
  the complete expected type, and proves it by applying that theorem. It never
  imports the challenge.
- [config.json](config.json) names the two separate environments and the target,
  permits only `propext`, `Quot.sound`, and `Classical.choice`, and enables Nanoda.
  There are no definition holes or extra permitted axioms.
- The [definition map](DEFINITION_MAP.md) expands the statistical definitions
  and quantifiers. A [separate source review](review.md) compares them with the
  original manuscript. This is an AI-assisted review, not independent human
  mathematical peer review.

The challenge fixes all probability measures on compact K as the optimization
domain, the full Gaussian density, independent Gamma shape/rate weights, the
total likelihood sums, finite topological support, and global Hellinger loss.
The existing qualifications about measurable good subsets and separately
proved ordinary-optimizer existence remain recorded in the definition map.

Comparator compares the target types and recursively compares the declarations
used by those types. It checks the proof's axiom dependencies and replays the
exported proof through Lean's kernel. The configured Nanoda pass checks the
export through an independent Rust implementation of the kernel. The linked
Lean4Checker replay alone is not an independent kernel implementation.

## Reproduce the check

Build the exact external tools listed in
[tooling/TOOL_SETUP.md](tooling/TOOL_SETUP.md). That file preserves the actual
build commands and native-Mac setup. Its absolute temporary paths describe the
recorded run; tools may be installed elsewhere for reproduction. Exact source
revisions, versions, and binary fingerprints are in
[tool-provenance.json](tooling/tool-provenance.json).

From the package root, after installing the pinned dependencies:

```sh
lake exe cache get
python3 scripts/run_comparator.py \
  --comparator /path/to/comparator/.lake/build/bin/comparator \
  --exporter /path/to/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export \
  --landrun /path/to/landrun \
  --nanoda /path/to/nanoda_lib/target/release/nanoda_bin \
  --output-dir audit/comparator/runs/my-linux-run
```

Use a new output directory: the runner refuses to replace an existing record.
It preserves the effective configuration, full stdout/stderr, exact executed
command, binary hashes, and source hashes before/after. A successful exit also
requires both kernel acceptance messages and unchanged source hashes.
`--skip-nanoda` explicitly requests the narrower Lean-only replay; it does not
qualify as an independent-kernel check.

The upstream development option for macOS is explicit:

```sh
python3 scripts/run_comparator.py \
  --comparator /path/to/comparator/.lake/build/bin/comparator \
  --exporter /path/to/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export \
  --landrun /path/to/comparator/scripts/fake-landrun.sh \
  --nanoda /path/to/nanoda_lib/target/release/nanoda_bin \
  --unsandboxed-development \
  --output-dir audit/comparator/runs/my-macos-run
```

**The development shim provides no sandbox.** It does not replace any
comparison or kernel check, but it removes the protection against malicious
build scripts and metaprograms. Use it only with trusted sources. The recorded
Mac run uses this mode. For adversarial inputs, follow the upstream Linux
Landrun isolation instructions, including its operating-system requirements;
merely running this command with a binary named `landrun` is not a security
audit of that environment.

The ordinary `scripts/verify.py` and GitHub Lean workflow do not install or run
these external checkers. Compiling Challenge and Solution alone is not a
Comparator check. The default production build does not import the challenge
or its placeholder.

To validate the preserved successful record against the current packaged
source, configuration, log, and binary fingerprints, run:

```sh
python3 scripts/check_comparator_record.py
```

This is a portable integrity check of recorded evidence, not a fresh kernel
execution. The included GitHub workflow runs this check and compiles the
separate interfaces; it does not claim a fresh Comparator or Nanoda run.

## Scope and trust

Comparator establishes agreement with the trusted **formal** statement. It
does not mechanically prove that this statement expresses the intended LaTeX.
Read the challenge and definition map against `paper.tex`; the original
[expanded statement audit](../main-result-2026-09-29/README.md) remains relevant.

This audit is local verification, not Palomar registration or Palomar's
automated editorial review. No GitHub upload or hosted CI execution is implied.
Mathlib's cached artifacts and the installed Lean compiler were reused; Mathlib
and Lean were not rebuilt from source. The exact tools and actual run records,
rather than a generic claim of formal verification, define the evidence.

Primary tool documentation: [Comparator](https://github.com/leanprover/comparator/tree/1cfc5d8ad183bf65efe7accd0efc175b6b8f25b6),
[Nanoda](https://github.com/ammkrn/nanoda_lib/tree/3a2407216ee84a75f9e1aead6803d0578be06ae7),
and [Palomar's scope](https://palomar-registry.org/about.html).
