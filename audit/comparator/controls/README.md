# Deliberately invalid Comparator submissions

These two files are **negative controls**, never production imports and never
proofs offered as completed mathematics. The normal challenge and solution are
not modified when these controls run.

| Control | Deliberate defect | Required Comparator diagnostic |
|---|---|---|
| `ChangedDefinition.lean` | The challenge's `gaussianPaperRiskScale` is multiplied by 2; the theorem's surface syntax is retained. | `Const does not match between challenge and target 'ReweightedNPMLE.gaussianPaperRiskScale'` |
| `UnprovedSolution.lean` | The correct solution statement is admitted with `sorry`, despite importing the existing proved theorem. | `Illegal axiom detected: 'sorryAx'` |

The first verifies that checking extends into statistical definitions rather
than only comparing the theorem's outer text. The second verifies rejection of
an unproved solution under the permitted axiom policy
`[propext, Quot.sound, Classical.choice]`. No definition holes are configured.
The placeholder proof in a *challenge* is intentional; the placeholder in a
*solution* must fail.

With the separately installed pinned tools available on `PATH`, run from the
package root:

```sh
python3 scripts/check_comparator_controls.py --output-dir /tmp/npmle-controls-new-run
```

The script accepts `--comparator`, `--exporter`, and `--landrun` executable paths.
On macOS the upstream `scripts/fake-landrun.sh` development shim requires the
explicit `--unsandboxed-development` flag. Such a run provides no isolation or
adversarial-sandbox assurance. It does not claim Linux Landrun was used.

The control configs disable Nanoda: both inputs should be rejected before
kernel replay. The positive Comparator/Nanoda check is recorded separately.
Each control succeeds as a test only if the actual Comparator process exits
nonzero, emits the exact expected diagnostic, never prints its acceptance
marker, and leaves the fingerprinted sources unchanged. Unexpected build or
tooling failures therefore do not count as expected rejection.

[`scripts/check_comparator_controls.py`](../../../scripts/check_comparator_controls.py)
records the actual executable command, environment overrides, binary hashes,
config, source hashes, complete combined output, exit code, and diagnostic match.
The retained run is [`runs/03-negative-controls`](../runs/03-negative-controls).
