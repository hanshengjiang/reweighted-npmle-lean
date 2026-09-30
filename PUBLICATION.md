# Upload this standalone package

The code and documentation are licensed under Apache-2.0; the manuscript and
recorded-input scope is explained in [LICENSE_SCOPE.md](LICENSE_SCOPE.md).

1. Extract the ZIP and enter its `reweighted-npmle-lean/` directory.
2. Upload **that directory's contents** as your new GitHub repository root.
   `lakefile.toml`, `lean-toolchain`, `ReweightedNPMLE/`, `audit/`, `docs/`, and
   the hidden `.github/` directory must be at the root. Do not add an extra
   `formalization/` wrapper or upload only the ZIP as the repository contents.
3. Inspect the first GitHub Actions run. A local release check does not imply
   that this future hosted run has already succeeded.
4. Create a release tag, for example `v0.1.0`, identifying these exact files.
   Add your actual repository/release URL to the paper. No tag is created here.
5. Preserve the frozen manuscript snapshots for this release when preparing
   later prose versions. See [docs/manuscript/README.md](docs/manuscript/README.md).

A command-line upload can preserve hidden files reliably. Run Git initialization
only in your extracted standalone directory, not in the original parent project:

```sh
git init -b main
git add .
git commit -m "Release Lean formalization and statement audit"
```

Then use the remote URL and push instructions from the repository you create.
The packaging task does not choose a GitHub repository, change visibility,
create a remote, or upload anything.

## Reproduce checks

```sh
lake exe cache get
python3 scripts/verify.py
python3 -m unittest discover -s tests -v
python3 scripts/check_release.py
```

See [RELEASE_CHECKS.md](RELEASE_CHECKS.md) for actual release-check results,
command logs, and distinctions between historical and fresh checks.
The standard library verifier checks the build, all listed axiom reports,
and exact generated-data reproduction. It does not rerun numerical solvers.

The [main theorem Comparator audit](audit/comparator/README.md) includes a
separately specified challenge, a solution wrapper, pinned-tool instructions,
and the recorded verification results. Follow that audit's instructions to
reproduce the additional check. Running the ordinary commands above does not
by itself run Comparator or an independent kernel checker. Review the stated
execution conditions before describing a new run as equivalent to the
recorded one. This package has not been submitted to the Palomar registry.

## Re-export

```sh
python3 scripts/export_repository.py
python3 scripts/check_release.py --zip dist/reweighted-npmle-lean.zip
```

The ZIP includes the proof sources, Comparator challenge and solution,
audit scripts and recorded logs, other audit and release records, manuscript
snapshots, bundled certificate inputs, Apache license, and CI configuration.
Its SHA-256 manifest covers every included payload file. Exports exclude
`.lake/`, `.git/`, bytecode, scratch `Check.lean`, and prior packaging output.
Use `--force` only when intentionally replacing an existing archive.
