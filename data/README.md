# Bundled numerical certificate inputs

`results/` contains exact copies of the six recorded CSV/JSON/LaTeX inputs
used by the generator. They were copied without numerical modification from
the original paper directory on 16 September 2026.

- `monte_carlo_1d.csv`
- `monte_carlo_2d.csv`
- `path_results.csv`
- `key_findings.json`
- `multistart_stability.json`
- `numerical_summary.tex`

The generator resolves this directory relative to its own script, never to
the process working directory or an assumed parent repository. Run
`python3 scripts/generate_numerical_data.py --check` from the package root.
The SHA-256 digests encoded in the generated Lean artifacts remain unchanged.

These are recorded simulation outputs, not newly certified simulation code.
The mathematical Lean proofs do not require regenerating these artifacts.
Historical literal-range counterexamples and approved reporting corrections
are documented separately in `PAPER_COVERAGE.md` and
`docs/NUMERICAL_CORRECTIONS_NOTE.md` at the package root.
