"""Integrity failure cases for the portable, unsigned Comparator record."""

import hashlib
import json
from pathlib import Path
import tempfile
import unittest

from scripts.check_comparator_record import (
    ACCEPTANCE_LINES, DEFAULT_RECORD, EXTRA_SOURCES, PRODUCTION_MANIFEST,
    PROVENANCE, TOOL_PATHS, check_record,
)


def digest(content):
    return hashlib.sha256(content).hexdigest()


class ComparatorRecordTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "relocated-package"
        self.root.mkdir()
        self.directory = str(Path(DEFAULT_RECORD).parent)
        sources = {"ReweightedNPMLE.lean", "ReweightedNPMLE/Main.lean", "Verification.lean"}
        for name in sources | EXTRA_SOURCES:
            self.write(name, b"fixture source\n")
        self.config = {
            "challenge_module": "audit.comparator.Challenge",
            "solution_module": "audit.comparator.Solution",
            "theorem_names": ["ComparatorAudit.main"],
            "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
            "enable_nanoda": True,
        }
        self.save("audit/comparator/config.json", self.config)
        self.save(f"{self.directory}/effective-config.json", self.config)
        manifest = {name: digest(self.read(name)) for name in sources}
        self.save(PRODUCTION_MANIFEST, manifest)
        self.log = "THIS IS NOT REAL LANDRUN\n" + "\n".join(ACCEPTANCE_LINES) + "\n"
        self.write(f"{self.directory}/comparator.log", self.log.encode())
        hashes = {name: digest(self.read(name)) for name in sources | EXTRA_SOURCES}
        self.record = {
            "started_utc": "2026-09-29T00:00:00+00:00",
            "finished_utc": "2026-09-29T00:01:00+00:00",
            "success": True, "sources_unchanged": True,
            "lean_kernel_accepted": True, "nanoda_accepted": True,
            "nanoda_requested": True, "exit_code": 0,
            "sandbox_mode": "unsandboxed-development",
            "source_sha256_before": hashes, "source_sha256_after": dict(hashes),
            "binary_sha256": {key: digest(key.encode()) for key in TOOL_PATHS},
            "log_sha256": digest(self.log.encode()),
            "working_directory": "/this/old/absolute/path/does/not/exist",
            "command": ["/also/nonexistent/comparator"],
        }
        self.save(DEFAULT_RECORD, self.record)
        self.save(PROVENANCE, {"sha256": [
            {"path": path, "sha256": self.record["binary_sha256"][key]}
            for key, path in TOOL_PATHS.items()]})

    def write(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)

    def read(self, name):
        return (self.root / name).read_bytes()

    def save(self, name, value):
        self.write(name, json.dumps(value).encode())

    def reject_record(self, pattern):
        self.save(DEFAULT_RECORD, self.record)
        with self.assertRaisesRegex(ValueError, pattern):
            check_record(self.root)

    def test_relocated_record_uses_no_original_paths_or_installed_tools(self):
        self.assertEqual(check_record(self.root), 10)

    def test_missing_unfinished_and_failed_records_rejected(self):
        (self.root / DEFAULT_RECORD).unlink()
        with self.assertRaisesRegex(ValueError, "missing"):
            check_record(self.root)
        self.record.pop("finished_utc")
        self.reject_record("Invalid isoformat")
        self.record["finished_utc"] = "2026-09-29T00:01:00+00:00"
        self.record["success"] = False
        self.reject_record("success")

    def test_each_acceptance_flag_and_exit_code_required(self):
        for flag in ("success", "sources_unchanged", "lean_kernel_accepted",
                     "nanoda_accepted", "nanoda_requested"):
            with self.subTest(flag=flag):
                self.record[flag] = False
                self.reject_record(flag)
                self.record[flag] = True
        self.record["exit_code"] = 1
        self.reject_record("exit 0")

    def test_omitted_source_in_both_maps_rejected(self):
        for phase in ("before", "after"):
            self.record[f"source_sha256_{phase}"].pop("ReweightedNPMLE/Main.lean")
        self.reject_record("inventory")

    def test_extra_production_file_rejected(self):
        self.write("ReweightedNPMLE/Extra.lean", b"new source")
        with self.assertRaisesRegex(ValueError, "inventory"):
            check_record(self.root)

    def test_changed_source_and_manuscript_rejected(self):
        for name in ("ReweightedNPMLE/Main.lean", "docs/manuscript/paper.tex"):
            with self.subTest(name=name):
                original = self.read(name)
                self.write(name, b"changed")
                with self.assertRaisesRegex(ValueError, "Current source differs"):
                    check_record(self.root)
                self.write(name, original)

    def test_before_after_mismatch_rejected(self):
        self.record["source_sha256_after"]["Verification.lean"] = "0" * 64
        self.reject_record("changed during")

    def test_effective_config_cannot_weaken_target_or_axioms(self):
        for field, replacement in (("enable_nanoda", False),
                                   ("definition_names", ["aHole"]),
                                   ("permitted_axioms", ["propext", "sorryAx", "Quot.sound"]),
                                   ("theorem_names", ["SomeOtherTheorem"])):
            with self.subTest(field=field):
                config = dict(self.config, **{field: replacement})
                self.save(f"{self.directory}/effective-config.json", config)
                with self.assertRaises(ValueError):
                    check_record(self.root)

    def test_tampered_log_rejected(self):
        self.write(f"{self.directory}/comparator.log", b"shortened log")
        with self.assertRaisesRegex(ValueError, "log SHA256"):
            check_record(self.root)

    def test_missing_acceptance_rejected_even_with_updated_log_hash(self):
        log = self.log.replace(ACCEPTANCE_LINES[0], "Nanoda rejected")
        self.write(f"{self.directory}/comparator.log", log.encode())
        self.record["log_sha256"] = digest(log.encode())
        self.reject_record("acceptance line")

    def test_binary_hash_mismatch_rejected(self):
        self.record["binary_sha256"]["nanoda"] = "0" * 64
        self.reject_record("binary hash differs: nanoda")

    def test_absolute_escape_and_symlink_paths_rejected(self):
        for name in ("/tmp/result.json", "../result.json"):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, "relative package path"):
                check_record(self.root, name)
        source = self.root / "Verification.lean"
        source.unlink()
        source.symlink_to(self.root / "ReweightedNPMLE.lean")
        with self.assertRaisesRegex(ValueError, "Symlink"):
            check_record(self.root)

    def test_duplicate_json_keys_rejected(self):
        self.write(DEFAULT_RECORD, b'{"success": false, "success": true}')
        with self.assertRaisesRegex(ValueError, "Duplicate JSON key"):
            check_record(self.root)


if __name__ == "__main__":
    unittest.main()
