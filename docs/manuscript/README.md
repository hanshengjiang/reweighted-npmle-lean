# Frozen manuscript references — 29 September 2026

These files are unchanged copies from the author's source checkout at commit
`e8bf8f2832b3d3dfb94ebdf3e9d718ad3434eeb4`:

- [paper.tex](paper.tex): the primary original manuscript reference for this
  release and the main statement audit.
- [paper_v2.tex](paper_v2.tex) and [paper_v3.tex](paper_v3.tex): subsequent writing
  versions retained for provenance and comparison.
- [SHA256SUMS](SHA256SUMS): SHA-256 of each complete source file.

The main `thm:main` has the same conclusions and quantifiers across the three
versions; v2/v3 express its assumptions through a standing-assumption reference.
That fact alone does not establish that every other statement is textually or
mathematically identical. See the
[release coverage review](../../audit/release-checks/coverage-review.md) for
other statement differences and their formal interfaces.

The earlier standalone formalization's [September 16 snapshot](../paper.tex)
is retained byte-for-byte so older audit records remain interpretable.

These snapshots are scholarly reference text, not a promise of a self-contained
LaTeX build. Paper figures, bibliography inputs where external, and numerical
simulation programs are not all included. The Lean build does not require TeX.
The manuscripts retain their copyright; see [license scope](../../LICENSE_SCOPE.md).

## Later manuscript revisions

Keep these release snapshots immutable. Future v4/v5 prose can refer to the
same Lean release when the mathematical meaning is unchanged. Check model
assumptions and definitions as well as labeled theorem bodies: a theorem can
change meaning without its displayed conclusion changing. Record any changed
mathematical claim and update its Lean correspondence before claiming coverage.

`python3 scripts/check_release.py`, run at the package root, verifies these
snapshot hashes and the unchanged production Lean sources. It checks integrity,
not semantic equivalence to an arbitrary future manuscript.
