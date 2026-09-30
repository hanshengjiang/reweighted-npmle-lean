# Completion audit - verified corrected paper

Historical development record (16 September 2026). For the independently rerun
29 September release checks and current scope qualifications, see
[RELEASE_CHECKS.md](RELEASE_CHECKS.md) and the
[release statement review](audit/release-checks/coverage-review.md).

Final verification date: 16 September 2026. The author approved correction
of the numerical reporting and required a separate note. The approved edits
are applied, and `docs/NUMERICAL_CORRECTIONS_NOTE.md` separately records them.
The mathematical and corrected recorded-report formalization requirements
are verified. No theoretical paper correction was identified or applied.

Source inspected: the manuscript snapshot in `docs/paper.tex`, including all 18 named mathematical
statement blocks, the model definitions, the numerical section, and the
appendix statements. Current Lean statement types were compared with these
requirements, not inferred from a successful build alone.

## Mathematical requirements

The label-by-label mapping in `PAPER_COVERAGE.md` covers all 18 named blocks.
The actual inspected interfaces preserve their quantifiers and conclusions:
full probability-law optimizer fibers, actual finite topological support,
simultaneous possibly data-dependent atom lists, common joint events,
uniform true-law thresholds, literal rates and constants, and the complete
appendix regularity/localization/net assertions. No finite-dictionary
surrogate or assumed support/moment/genericity estimate substitutes for a
paper conclusion.

The audit additionally made convexity of the **actual canonical** optimized
value explicit in `canonical_fitted_value_convexOn_univ`; the previous
generic convexity theorem is supplied with the already-proved canonical
maximizer property. Both are included in the central axiom audit.

For the tiny corollary, `gaussian_exact_regularization_joint_tiny_explicit`
also shows that the probability and density-rate constants do not depend on
`L`; only its support constant and eventual threshold need depend on `L`.
The common-constant wrapper is not the sole evidence for this correspondence.

## Numerical and definition requirements

The verified artifacts cover all 48 table means and 42 actual square-root
standard errors, 12 explicitly displayed path quantiles, all four actual raw
median/log regressions and their global least-squares optimality, all 11
whole-design summaries, 920 support pairs, all 4160 recorded fit diagnostics,
the multistart maxima and design/path counts. Real logarithm, mean and
interval-soundness theorems connect the rational checks to the displayed real
arithmetic. All three generated artifacts reproduce the six source files
under `python3 scripts/generate_numerical_data.py --check --audit-numerics`.

The Gaussian kernels, full-law criteria, Hellinger convention and exact
paper concentration/rate definitions are identified in `PAPER_COVERAGE.md`.
The three experimental mixing laws are genuine probability laws with the
literal locations, masses and uniform interval. Their compact parameter
boxes, support constraints and density normalization are proved. The tiny
`L=1/2` specialization and average-one normalization/optimizer invariance
are explicit.

The numerical proof scope is the paper's **recorded data and finite-precision
reports**. It does not certify floating-point solvers, numerical integration,
continuous-oracle accuracy or correctness of visual rendering. No general
algorithm-convergence theorem is asserted by the source paper.

## Original contradictions and approved reconciliation

The original source asserted that every balanced path draw had three atoms.
The raw CSV and Lean counterexample prove otherwise: 28 have three atoms and
two have four. A proof of the original universal assertion cannot be supplied.

Six of the eight printed whole-design ranges are false as literal enclosing
bounds. Their endpoints are verified rounded extrema, which are different
propositions. The real log-scaled likelihood maximum also exceeds `0.532`
literally, although it rounds to that value. The all-fit KKT maximum is
certified with upward-bound semantics, not nearest-rounding semantics.

The corrected source states the median and actual 28/2 balanced counts and
all-three tiny draws; explicitly describes all nine affected numerical
endpoint pairs as rounded minimum/maximum summaries; and describes the
recorded all-fit KKT maximum as a conservatively upward-rounded upper bound.
These propositions match the checked numerical interfaces, rather than
claiming a proof of a false original statement. The exact support-difference
bound, all displayed numerical values and all 18 named mathematical statement
blocks are retained. `PROPOSED_NUMERICAL_CORRECTIONS.md` preserves the approved
proposal; `docs/NUMERICAL_CORRECTIONS_NOTE.md` records its separate application.
Original counterexample theorems and literal-interval FAIL labels are retained
for traceability; they do not describe failures of the corrected statements.

## Dependency, verification and preservation requirements

`lakefile.toml` has only the mathlib v4.30.0 dependency and both default
targets; `lean-toolchain` selects Lean v4.30.0. Both targets must pass
`lake build`, and `lake env lean Verification.lean` independently checks the
listed theorem dependencies. Production-source scans have only English
comment matches for placeholder/axiom/native/unsafe terms; the excluded
preexisting `Check.lean` is not imported. The axiom-list entries are unique.

Final checks after applying the source corrections: `lake build` passed all
3822 jobs, and the independent
`lake env lean Verification.lean` pass checked all 621 unique listed
declarations: 613 use only `propext`, `Classical.choice`, `Quot.sound`, one
uses only `propext`, `Quot.sound`, and seven use no axioms.

`python3 scripts/generate_numerical_data.py --check --audit-numerics` also
passed exact reproduction of all three Lean artifacts from all six source
files. All reported path and raw-regression precision checks passed; the
original literal-range failure pattern is intentionally retained.

Only approved numerical manuscript/README wording, the rebuilt manuscript,
the separate corrections note and corresponding status/audit documentation
were changed during this correction pass. Raw results, simulation code,
figures, the numerical table, theoretical statements and unrelated user work
are preserved. No commit or remote mutation is required or requested.

In the original paper directory,
`latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex` completed
successfully. The final manuscript has 29 pages; all page layouts were checked
in rendered contact sheets, and the affected pages 12-15 were separately
inspected at readable resolution. Corrected text, figures, table, headers,
page numbering and section transitions are legible without clipping or
overlap. The final log has no undefined references or overfull/underfull box
warnings; its sole microtype footnote-patch warning is non-fatal. That PDF and
its figure assets are not dependencies of, or bundled with, this Lean package.

The umbrella `ReweightedNPMLE.lean` imports both theory and numerical
certificates. Successful compilation and the axiom audit establish the
encoded propositions; the label-by-label audit independently checks their
correspondence to the paper. Compilation alone is not used to infer that
the prose or an unverified numerical algorithm has been proved.

Historical terminal cleanup is complete: the task-owned `caffeinate -i` session 87217
(PID 16271) was stopped with Ctrl-C and its terminal exited. A process-table
check confirmed that PID 16271 is no longer present. Display sleep was allowed
throughout. Task-created LaTeX intermediates and PDF QA scratch files were
removed. Keep-awake settings are not required by the standalone package.

Completion verdict: all requested formalization, corrected-source audit,
separate-note, verification, manuscript-rebuild and keep-awake cleanup
requirements are satisfied within the numerical proof scope stated above.
