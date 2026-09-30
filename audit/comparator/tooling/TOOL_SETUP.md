# Comparator tooling used on 2026-09-29

These records describe tools installed under `/private/tmp/npmle-comparator-tools`;
tool binaries and build caches are not bundled in the release. The mathematical
formalization was not edited by this tooling setup.

## Pinned sources and binaries

| Tool | Revision | Binary relative to this directory |
| --- | --- | --- |
| Comparator | `1cfc5d8ad183bf65efe7accd0efc175b6b8f25b6` | `comparator/.lake/build/bin/comparator` |
| lean4export | `a3e35a584f59b390667db7269cd37fca8575e4bf` | `comparator/.lake/packages/lean4export/.lake/build/bin/lean4export` |
| Lean4Checker (same-Lean-kernel replay dependency) | `b7398199245524275543dec6113229c9bb4902e5` | linked into Comparator |
| Nanoda | `3a2407216ee84a75f9e1aead6803d0578be06ae7` | `nanoda_lib/target/release/nanoda_bin` |

Comparator is the upstream revision targeting the package's Lean 4.30.0. Its checked-in manifest pins both Lean dependencies. The selected exporter emits format 3.1.0, supported by the selected Nanoda. Comparator, both dependencies, and Nanoda all had empty `git status --short` after building. The exact command output and binary fingerprints are in `tool-provenance.json`. Native macOS binaries are not portable to Linux and need rebuilding there.

## Build commands actually run

The commands below are displayed with their actual temporary directory paths. The initial un-escalated Git clone could not resolve github.com; the approved network-enabled retry succeeded. Dependency downloads/builds likewise used approved network-enabled execution. Git clone/checkout output was inspected in the tool transcript; the redirected build/install logs are saved alongside this file.

```sh
cd /private/tmp/npmle-comparator-tools
git clone https://github.com/leanprover/comparator.git comparator
cd comparator
git checkout 1cfc5d8ad183bf65efe7accd0efc175b6b8f25b6
lake build lean4export comparator > /private/tmp/npmle-comparator-tools/tool-build.log 2>&1
```

Exit 0; `Build completed successfully (25 jobs).` No project source edits were needed.

Rust was not installed on the machine. Rust 1.90.0 was installed solely under this temporary tools directory, with no shell startup-file modifications:

```sh
cd /private/tmp/npmle-comparator-tools
git clone https://github.com/ammkrn/nanoda_lib.git nanoda_lib
curl --fail --location --output rustup-init https://static.rust-lang.org/rustup/dist/aarch64-apple-darwin/rustup-init
chmod +x rustup-init
env RUSTUP_HOME=/private/tmp/npmle-comparator-tools/rustup \
  CARGO_HOME=/private/tmp/npmle-comparator-tools/cargo \
  ./rustup-init -y --no-modify-path --profile minimal --default-toolchain 1.90.0 \
  > rust-install.log 2>&1
cd nanoda_lib
env RUSTUP_HOME=/private/tmp/npmle-comparator-tools/rustup \
  CARGO_HOME=/private/tmp/npmle-comparator-tools/cargo \
  /private/tmp/npmle-comparator-tools/cargo/bin/cargo build --locked --release \
  > /private/tmp/npmle-comparator-tools/nanoda-build.log 2>&1
```

The clone's HEAD was recorded as `3a2407216ee84a75f9e1aead6803d0578be06ae7`; for reproduction, explicitly `git checkout` that revision before the Cargo command. Cargo build exited 0 and reported `Finished release profile [optimized] target(s) in 9.88s`. No checker code or Cargo lockfile was modified.

## Integration smoke check actually run

The upstream `simple_match` test's `Challenge.lean`, `Solution.lean`, and `config.json` were copied to a separate `smoke-match/` project. A two-library Lake configuration and the Lean 4.30.0 toolchain file were added there. `config-nanoda.json` copies the upstream configuration with `enable_nanoda` changed to `true`. This test proves commutativity of natural-number addition, not the NPMLE main result. The main-result check has its own separate log.

```sh
cd /private/tmp/npmle-comparator-tools/smoke-match
env COMPARATOR_LANDRUN=/private/tmp/npmle-comparator-tools/comparator/scripts/fake-landrun.sh \
  COMPARATOR_LEAN4EXPORT=/private/tmp/npmle-comparator-tools/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export \
  COMPARATOR_NANODA=/private/tmp/npmle-comparator-tools/nanoda_lib/target/release/nanoda_bin \
  lake env /private/tmp/npmle-comparator-tools/comparator/.lake/build/bin/comparator \
  config-nanoda.json > /private/tmp/npmle-comparator-tools/smoke-nanoda.log 2>&1
```

Exit 0. The log ends:

```text
Running nanoda kernel on solution
Nanoda kernel accepts the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

The historical Comparator configuration requires the boolean field `enable_nanoda` and does not support the newer `external_kernels` field. To invoke without Nanoda, set `enable_nanoda` to `false`. Do not silently drop failed external checking or expand the axiom allowlist. The permitted axioms used were exactly `propext`, `Quot.sound`, and `Classical.choice`.

## Execution limitation

The actual smoke check used upstream `scripts/fake-landrun.sh`, which prints explicit `THIS IS NOT REAL LANDRUN` warnings. **This is unsandboxed development mode, not Linux Landrun security verification.** The source was trusted for this audit; no claim of protection from adversarial Lean metaprograms is made. No Docker, Podman, Colima, Lima, QEMU, Go, or Rust executable was initially available in PATH or checked conventional locations. A bare native `sandbox-exec` echo probe succeeded only with an approved escalation, but no macOS sandbox adapter was implemented, security-tested, or used for Comparator. No Linux Landrun run was performed. Nanoda is genuinely an independent Rust kernel implementation; the linked Lean4Checker is a second replay through Lean's kernel, not an independent kernel.

No full Comparator regression suite or Nanoda test suite was run here. The integration smoke check and the separately logged actual main-result check are the evidence for this task. No Palomar submission, automated editorial review, or registry certification was performed.

Primary sources: [Comparator at the pinned revision](https://github.com/leanprover/comparator/tree/1cfc5d8ad183bf65efe7accd0efc175b6b8f25b6), [lean4export at the pinned revision](https://github.com/leanprover/lean4export/tree/a3e35a584f59b390667db7269cd37fca8575e4bf), [Nanoda at the pinned revision](https://github.com/ammkrn/nanoda_lib/tree/3a2407216ee84a75f9e1aead6803d0578be06ae7).
