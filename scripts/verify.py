#!/usr/bin/env python3
"""Check the standalone build, listed axiom allowlist, and bundled inputs."""

import argparse
from collections import Counter
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REPORT = re.compile(
    r"'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
)


def audit_output(output, expected):
    if not expected or len(set(expected)) != len(expected):
        raise ValueError("Verification.lean must list distinct, nonempty declarations")
    reports = REPORT.findall(output)
    if Counter(name for name, _ in reports) != Counter(expected):
        raise ValueError("Axiom output is missing, repeated, or unexpected")
    counts = Counter()
    for name, axioms in reports:
        used = frozenset(a.strip() for a in axioms.split(",") if a.strip())
        if used - ALLOWED_AXIOMS:
            raise ValueError(f"Unexpected axioms for {name}: {sorted(used - ALLOWED_AXIOMS)}")
        counts[used] += 1
    return counts


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        print("\n".join((result.stdout + result.stderr).splitlines()[-80:]), file=sys.stderr)
        raise RuntimeError(f"Command failed ({result.returncode}): {' '.join(command)}")
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-build", action="store_true", help="use only after a successful build")
    args = parser.parse_args()
    if not args.skip_build:
        print("Building both default Lean targets...", flush=True)
        run(["lake", "build"])
        print("lake build passed", flush=True)
    expected = re.findall(r"^#print axioms (\S+)\s*$", (ROOT / "Verification.lean").read_text(), re.M)
    counts = audit_output(run(["lake", "env", "lean", "Verification.lean"]), expected)
    for used, count in sorted(counts.items(), key=lambda item: sorted(item[0])):
        print(f"{count} declarations: [{', '.join(sorted(used))}]")
    print(f"Independent axiom audit passed: {len(expected)} unique declarations", flush=True)
    print(run([sys.executable, str(ROOT / "scripts/generate_numerical_data.py"), "--check"]).strip())


if __name__ == "__main__":
    try:
        main()
    except (ValueError, RuntimeError, OSError) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
        sys.exit(1)
