#!/usr/bin/env python3
"""Run the separately installed, pinned Comparator and retain actual evidence.

See audit/comparator/README.md for tool installation and the trust boundary.
This does not install tools, upload anything, or change production Lean sources.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import shlex
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def executable(value):
    found = shutil.which(value)
    if not found:
        raise ValueError(f"Executable not found: {value}")
    return str(Path(found).resolve())


def source_hashes():
    names = set(json.loads((ROOT / "audit/release-checks/original-lean-sources.json").read_text()))
    names.update({"lakefile.toml", "lake-manifest.json", "lean-toolchain",
                  "audit/comparator/Challenge.lean", "audit/comparator/Solution.lean",
                  "audit/comparator/config.json", "docs/manuscript/paper.tex"})
    return {name: sha(ROOT / name) for name in sorted(names)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--comparator", default="comparator")
    parser.add_argument("--exporter", default="lean4export")
    parser.add_argument("--landrun", default="landrun")
    parser.add_argument("--nanoda", default="nanoda_bin")
    parser.add_argument("--skip-nanoda", action="store_true",
                        help="explicitly run only statement/axiom comparison and Lean kernel replay")
    parser.add_argument("--unsandboxed-development", action="store_true",
                        help="explicitly use the upstream development shim; no sandbox assurance")
    parser.add_argument("--output-dir", type=Path, required=True,
                        help="new or empty directory for this run's log, config and JSON evidence")
    args = parser.parse_args()
    try:
        config = json.loads((ROOT / "audit/comparator/config.json").read_text())
        if (config.get("theorem_names") != ["ComparatorAudit.main"]
                or config.get("definition_names")
                or set(config.get("permitted_axioms", [])) != {"propext", "Quot.sound", "Classical.choice"}
                or config.get("challenge_module") != "audit.comparator.Challenge"
                or config.get("solution_module") != "audit.comparator.Solution"):
            raise ValueError("Unexpected target, definition holes, modules or axiom policy in config.json")
        config["enable_nanoda"] = not args.skip_nanoda
        if platform.system() != "Linux" and not args.unsandboxed_development:
            raise ValueError("Landrun requires Linux. A development run requires --unsandboxed-development.")
        binaries = {"comparator": executable(args.comparator), "exporter": executable(args.exporter),
                    "landrun_or_development_shim": executable(args.landrun)}
        if config["enable_nanoda"]:
            binaries["nanoda"] = executable(args.nanoda)
        output = args.output_dir.resolve()
        if output.exists() and any(output.iterdir()):
            raise ValueError(f"Refusing to overwrite an existing evidence directory: {output}")
        output.mkdir(parents=True, exist_ok=True)
        effective = output / "effective-config.json"
        effective.write_text(json.dumps(config, indent=2) + "\n")
        before = source_hashes()
        env = os.environ.copy()
        env["COMPARATOR_LEAN4EXPORT"] = binaries["exporter"]
        env["COMPARATOR_LANDRUN"] = binaries["landrun_or_development_shim"]
        if "nanoda" in binaries:
            env["COMPARATOR_NANODA"] = binaries["nanoda"]
        command = ["lake", "env", binaries["comparator"], str(effective)]
        record = {"started_utc": datetime.now(timezone.utc).isoformat(),
                  "platform": platform.platform(), "working_directory": str(ROOT),
                  "command": command,
                  "environment_overrides": {k: env[k] for k in
                      ("COMPARATOR_LEAN4EXPORT", "COMPARATOR_LANDRUN", "COMPARATOR_NANODA") if k in env},
                  "sandbox_mode": "unsandboxed-development" if args.unsandboxed_development else "landrun",
                  "nanoda_requested": config["enable_nanoda"],
                  "binary_sha256": {k: sha(Path(v)) for k, v in binaries.items()},
                  "source_sha256_before": before,
                  "toolchain": subprocess.check_output(["lake", "env", "lean", "--version"], cwd=ROOT, text=True).strip()}
        print(shlex.join(command), flush=True)
        print(f"Sandbox mode: {record['sandbox_mode']}; Nanoda requested: {config['enable_nanoda']}", flush=True)
        with (output / "comparator.log").open("w") as log:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        transcript = (output / "comparator.log").read_text()
        after = source_hashes()
        lean_ok = "Lean default kernel accepts the solution" in transcript
        nanoda_ok = "Nanoda kernel accepts the solution" in transcript
        success = (result.returncode == 0 and "Your solution is okay!" in transcript
                   and lean_ok and (nanoda_ok or not config["enable_nanoda"]) and before == after)
        record.update({"finished_utc": datetime.now(timezone.utc).isoformat(),
                       "exit_code": result.returncode, "source_sha256_after": after,
                       "sources_unchanged": before == after, "lean_kernel_accepted": lean_ok,
                       "nanoda_accepted": nanoda_ok, "success": success,
                       "log_sha256": sha(output / "comparator.log")})
        (output / "result.json").write_text(json.dumps(record, indent=2) + "\n")
        print(transcript, end="")
        print(f"Recorded {output / 'result.json'}")
        return 0 if success else 1
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(f"Comparator runner failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
