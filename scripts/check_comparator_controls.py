#!/usr/bin/env python3
"""Run two deliberately invalid Comparator submissions and require rejection.

Uses separately installed Comparator tooling. The production formalization,
normal challenge/solution, and Lake configuration are never rewritten.
The controls contain intentional sorry placeholders and are audit fixtures only.
"""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import platform
import shlex
import subprocess
import sys

from run_comparator import ROOT, executable, sha, source_hashes

CONTROLS = (
    ("changed-definition", "audit.comparator.controls.ChangedDefinition", "audit.comparator.Solution",
     "Const does not match between challenge and target 'ReweightedNPMLE.gaussianPaperRiskScale'"),
    ("unproved-solution", "audit.comparator.Challenge", "audit.comparator.controls.UnprovedSolution",
     "Illegal axiom detected: 'sorryAx'"),
)


def fingerprints():
    hashes = source_hashes()
    for path in sorted((ROOT / "audit/comparator/controls").glob("*")):
        if path.suffix in {".lean", ".json"}:
            hashes[str(path.relative_to(ROOT))] = sha(path)
    hashes["scripts/check_comparator_controls.py"] = sha(Path(__file__))
    return hashes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--comparator", default="comparator")
    parser.add_argument("--exporter", default="lean4export")
    parser.add_argument("--landrun", default="landrun")
    parser.add_argument("--unsandboxed-development", action="store_true")
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    try:
        if platform.system() != "Linux" and not args.unsandboxed_development:
            raise ValueError("Landrun requires Linux; a development run requires --unsandboxed-development.")
        binaries = {"comparator": executable(args.comparator), "exporter": executable(args.exporter),
                    "landrun_or_development_shim": executable(args.landrun)}
        output = args.output_dir.resolve()
        if output.exists() and any(output.iterdir()):
            raise ValueError(f"Refusing to overwrite evidence directory: {output}")
        output.mkdir(parents=True, exist_ok=True)
        env = os.environ.copy()
        env["COMPARATOR_LEAN4EXPORT"] = binaries["exporter"]
        env["COMPARATOR_LANDRUN"] = binaries["landrun_or_development_shim"]
        records = []
        for name, challenge, solution, diagnostic in CONTROLS:
            config_path = ROOT / f"audit/comparator/controls/{name}.json"
            config = json.loads(config_path.read_text())
            if (config.get("challenge_module") != challenge or config.get("solution_module") != solution
                    or config.get("theorem_names") != ["ComparatorAudit.main"]
                    or config.get("definition_names") or config.get("enable_nanoda") is not False
                    or set(config.get("permitted_axioms", [])) != {"propext", "Quot.sound", "Classical.choice"}):
                raise ValueError(f"Unexpected negative-control config: {config_path}")
            before = fingerprints()
            command = ["lake", "env", binaries["comparator"], str(config_path)]
            log_path = output / f"{name}.log"
            record = {"control": name, "started_utc": datetime.now(timezone.utc).isoformat(),
                      "working_directory": str(ROOT), "platform": platform.platform(),
                      "command": command,
                      "environment_overrides": {k: env[k] for k in ("COMPARATOR_LEAN4EXPORT", "COMPARATOR_LANDRUN")},
                      "sandbox_mode": "unsandboxed-development" if args.unsandboxed_development else "landrun",
                      "nanoda_requested": False, "expected_diagnostic": diagnostic,
                      "config": config, "source_sha256_before": before,
                      "binary_sha256": {k: sha(Path(v)) for k, v in binaries.items()}}
            print(shlex.join(command), flush=True)
            with log_path.open("w") as log:
                result = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
            transcript = log_path.read_text()
            after = fingerprints()
            accepted = "Your solution is okay!" in transcript
            passed = result.returncode != 0 and diagnostic in transcript and not accepted and before == after
            record.update({"finished_utc": datetime.now(timezone.utc).isoformat(),
                           "exit_code": result.returncode, "expected_diagnostic_found": diagnostic in transcript,
                           "unexpected_acceptance": accepted, "sources_unchanged": before == after,
                           "source_sha256_after": after, "log_sha256": sha(log_path),
                           "expected_rejection_verified": passed})
            (output / f"{name}.json").write_text(json.dumps(record, indent=2) + "\n")
            records.append(record)
            print(f"{name}: exit={result.returncode}; expected rejection verified={passed}", flush=True)
            if not passed:
                print(transcript, end="")
        summary = {"all_expected_rejections_verified": all(r["expected_rejection_verified"] for r in records),
                   "controls": [{k: r[k] for k in ("control", "exit_code", "expected_diagnostic",
                     "expected_diagnostic_found", "sources_unchanged", "expected_rejection_verified")} for r in records]}
        (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
        return 0 if summary["all_expected_rejections_verified"] else 1
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(f"Comparator negative controls failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
