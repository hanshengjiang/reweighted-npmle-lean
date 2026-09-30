#!/usr/bin/env python3
"""Check portable recorded evidence; do not rerun Comparator or either kernel.

This verifies internal consistency and matching source bytes in this package.
The JSON/log files are unsigned records, not an independent certification.
"""

import argparse
from datetime import datetime
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_RECORD = "audit/comparator/runs/02-nanoda-lean/result.json"
PRODUCTION_MANIFEST = "audit/release-checks/original-lean-sources.json"
PROVENANCE = "audit/comparator/tooling/tool-provenance.json"
EXTRA_SOURCES = {
    "lakefile.toml", "lake-manifest.json", "lean-toolchain",
    "audit/comparator/Challenge.lean", "audit/comparator/Solution.lean",
    "audit/comparator/config.json", "docs/manuscript/paper.tex",
}
TOOL_PATHS = {
    "comparator": "comparator/.lake/build/bin/comparator",
    "exporter": "comparator/.lake/packages/lean4export/.lake/build/bin/lean4export",
    "landrun_or_development_shim": "comparator/scripts/fake-landrun.sh",
    "nanoda": "nanoda_lib/target/release/nanoda_bin",
}
ACCEPTANCE_LINES = (
    "Nanoda kernel accepts the solution",
    "Lean default kernel accepts the solution",
    "Your solution is okay!",
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def package_file(root, name):
    """Read only normalized relative paths, with no symlink components."""
    require(isinstance(name, str) and name, "Missing relative package path")
    path = PurePosixPath(name)
    require(not path.is_absolute() and path.as_posix() == name
            and not any(part in {".", ".."} for part in path.parts)
            and "\\" not in name and ":" not in name,
            f"Invalid relative package path: {name}")
    candidate = root
    for part in path.parts:
        candidate /= part
        require(not candidate.is_symlink(), f"Symlink in recorded package path: {name}")
    require(candidate.is_file(), f"Required evidence/source file missing: {name}")
    return candidate


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"Duplicate JSON key: {key}")
        result[key] = value
    return result


def read_json(root, name):
    return json.loads(package_file(root, name).read_text(), object_pairs_hook=unique_object)


def hash_map(value, label):
    require(isinstance(value, dict), f"{label} must be a SHA256 map")
    require(all(isinstance(k, str) and isinstance(v, str)
                and re.fullmatch(r"[0-9a-f]{64}", v) for k, v in value.items()),
            f"Invalid SHA256 in {label}")
    return value


def check_config(config):
    require(isinstance(config, dict), "Comparator configuration must be an object")
    required = {"challenge_module", "solution_module", "theorem_names",
                "permitted_axioms", "enable_nanoda"}
    require(required <= set(config) <= required | {"definition_names"},
            "Unexpected configuration fields")
    require(config["challenge_module"] == "audit.comparator.Challenge"
            and config["solution_module"] == "audit.comparator.Solution"
            and config["theorem_names"] == ["ComparatorAudit.main"],
            "Unexpected Comparator target or modules")
    axioms = config["permitted_axioms"]
    require(isinstance(axioms, list) and len(axioms) == 3
            and all(isinstance(x, str) for x in axioms)
            and set(axioms) == {"propext", "Quot.sound", "Classical.choice"},
            "Unexpected axiom policy")
    require(config.get("definition_names", []) == [], "Definition holes are not permitted")
    require(config["enable_nanoda"] is True, "Independent Nanoda checking must be enabled")


def check_record(root=ROOT, record_name=DEFAULT_RECORD):
    root = Path(root).resolve()
    record = read_json(root, record_name)
    require(isinstance(record, dict), "Comparator record must be an object")
    for flag in ("success", "sources_unchanged", "lean_kernel_accepted",
                 "nanoda_accepted", "nanoda_requested"):
        require(record.get(flag) is True, f"Recorded {flag} is not true")
    require(type(record.get("exit_code")) is int and record["exit_code"] == 0,
            "Recorded Comparator command did not exit 0")
    start = datetime.fromisoformat(record.get("started_utc", ""))
    finish = datetime.fromisoformat(record.get("finished_utc", ""))
    require(start.utcoffset() is not None and finish.utcoffset() is not None and finish >= start,
            "Invalid or incomplete recorded run timestamps")
    require(record.get("sandbox_mode") == "unsandboxed-development",
            "This packaged record expects the disclosed unsandboxed development run")

    production = hash_map(read_json(root, PRODUCTION_MANIFEST), "production manifest")
    actual_production = {"ReweightedNPMLE.lean", "Verification.lean"} | {
        p.relative_to(root).as_posix() for p in (root / "ReweightedNPMLE").rglob("*.lean")}
    require(set(production) == actual_production, "Production source inventory differs")
    expected_names = set(production) | EXTRA_SOURCES
    before = hash_map(record.get("source_sha256_before"), "source_sha256_before")
    after = hash_map(record.get("source_sha256_after"), "source_sha256_after")
    require(set(before) == expected_names and set(after) == expected_names,
            "Recorded source inventory differs from the required production and audit inputs")
    require(before == after, "Recorded source hashes changed during the run")
    for name in sorted(expected_names):
        require(sha(package_file(root, name)) == before[name], f"Current source differs: {name}")
        if name in production:
            require(production[name] == before[name], f"Original production source differs: {name}")

    record_dir = PurePosixPath(record_name).parent
    config = read_json(root, "audit/comparator/config.json")
    effective = read_json(root, (record_dir / "effective-config.json").as_posix())
    check_config(config)
    check_config(effective)
    require(effective == config, "Effective configuration differs from the packaged configuration")
    log_path = package_file(root, (record_dir / "comparator.log").as_posix())
    require(sha(log_path) == record.get("log_sha256"), "Comparator log SHA256 differs")
    lines = [line.strip() for line in log_path.read_text().splitlines()]
    positions = []
    for accepted in ACCEPTANCE_LINES:
        require(lines.count(accepted) == 1, f"Missing or repeated acceptance line: {accepted}")
        positions.append(lines.index(accepted))
    require(positions == sorted(positions), "Kernel acceptance lines are out of order")
    require(any("THIS IS NOT REAL LANDRUN" in line for line in lines),
            "Development sandbox warning missing from the recorded log")

    provenance = read_json(root, PROVENANCE)
    require(isinstance(provenance, dict) and isinstance(provenance.get("sha256"), list),
            "Missing tool hash provenance")
    tool_hashes = {}
    for item in provenance["sha256"]:
        require(isinstance(item, dict) and isinstance(item.get("path"), str)
                and "sha256" in item, "Invalid tool hash provenance entry")
        require(item["path"] not in tool_hashes, "Duplicate tool provenance path")
        tool_hashes[item["path"]] = item["sha256"]
    hash_map(tool_hashes, "tool provenance")
    binaries = hash_map(record.get("binary_sha256"), "binary_sha256")
    require(set(binaries) == set(TOOL_PATHS), "Recorded checker binary inventory differs")
    for tool, path in TOOL_PATHS.items():
        require(binaries[tool] == tool_hashes.get(path), f"Recorded binary hash differs: {tool}")
    return len(expected_names)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", default=DEFAULT_RECORD,
                        help="record JSON path relative to this package root")
    args = parser.parse_args(argv)
    try:
        count = check_record(record_name=args.record)
    except (ValueError, OSError, TypeError) as error:
        print(f"Recorded Comparator evidence integrity FAILED: {error}", file=sys.stderr)
        return 1
    print(f"PASS: recorded Comparator evidence integrity; {count} source hashes match.")
    print("Recorded exit 0, Nanoda/Lean acceptance, log, configuration, and tool hashes agree.")
    print("Recorded-evidence integrity only: no checker was rerun and no certification is implied.")
    print("The recorded run used unsandboxed development mode; original absolute paths are metadata only.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
