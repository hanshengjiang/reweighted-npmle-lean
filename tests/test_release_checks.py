"""Failure-path tests for portable, immutable release inputs and ZIP payloads."""

import hashlib
import json
from pathlib import Path
import tempfile
import unittest
import zipfile

from scripts.check_release import (
    COMPARATOR_FILES, LEAN_HASHES, MANUSCRIPT_HASHES, MANUSCRIPTS, PREFIX, REQUIRED,
    check_lean_sources, check_manuscripts, check_markdown_links, check_required,
    check_zip,
)
from scripts.export_repository import (
    DIRECTORIES, REQUIRED as EXPORT_REQUIRED, export_repository,
)


def sha(content):
    return hashlib.sha256(content).hexdigest()


class ReleaseIntegrityTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name) / "package"
        self.root.mkdir()
        for name in REQUIRED:
            self.write(name, b"fixture\n")
        sources = ["ReweightedNPMLE.lean", "Verification.lean"] + [
            f"ReweightedNPMLE/Module{i:03}.lean" for i in range(110)]
        for name in sources:
            self.write(name, b"-- immutable proof source\n")
        self.write(LEAN_HASHES, json.dumps({name: sha(self.read(name)) for name in sources}).encode())
        self.write(MANUSCRIPT_HASHES, "".join(
            f"{sha(self.read('docs/manuscript/' + name))}  {name}\n"
            for name in sorted(MANUSCRIPTS)).encode())

    def write(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)

    def read(self, name):
        return (self.root / name).read_bytes()

    def payload(self):
        return {path.relative_to(self.root).as_posix(): path.read_bytes()
                for path in self.root.rglob("*") if path.is_file()}

    def make_zip(self, payload=None, extra_members=(), mutate_manifest=None):
        payload = self.payload() if payload is None else payload
        manifest = "".join(f"{sha(content)}  {name}\n" for name, content in sorted(payload.items()))
        if mutate_manifest:
            manifest = mutate_manifest(manifest)
        path = Path(self.temporary.name) / "release.zip"
        with zipfile.ZipFile(path, "w") as archive:
            for name, content in payload.items():
                archive.writestr(f"{PREFIX}/{name}", content)
            archive.writestr(f"{PREFIX}/EXPORT_MANIFEST.sha256", manifest)
            for name, content in extra_members:
                archive.writestr(name, content)
        return path

    def test_valid_package_and_zip(self):
        check_required(self.root)
        self.assertEqual(check_lean_sources(self.root), 112)
        self.assertEqual(check_manuscripts(self.root), 3)
        self.assertGreater(check_zip(self.make_zip()), 112)

    def test_tampered_lean_source_rejected(self):
        self.write("ReweightedNPMLE/Module001.lean", b"-- changed proof\n")
        with self.assertRaisesRegex(ValueError, "Original Lean source changed"):
            check_lean_sources(self.root)

    def test_missing_or_extra_lean_source_rejected(self):
        (self.root / "Verification.lean").unlink()
        with self.assertRaisesRegex(ValueError, "inventory differs"):
            check_lean_sources(self.root)
        self.write("Verification.lean", b"-- immutable proof source\n")
        self.write("ReweightedNPMLE/Unrecorded.lean", b"-- extra\n")
        with self.assertRaisesRegex(ValueError, "inventory differs"):
            check_lean_sources(self.root)

    def test_tampered_manuscript_rejected(self):
        self.write("docs/manuscript/paper.tex", b"different theorem\n")
        with self.assertRaisesRegex(ValueError, "Frozen manuscript changed"):
            check_manuscripts(self.root)

    def test_missing_manuscript_hash_rejected(self):
        self.write(MANUSCRIPT_HASHES, f"{sha(self.read('docs/manuscript/paper.tex'))}  paper.tex\n".encode())
        with self.assertRaisesRegex(ValueError, "inventory differs"):
            check_manuscripts(self.root)

    def test_missing_audit_rejected(self):
        (self.root / "audit/main-result-2026-09-29/README.md").unlink()
        with self.assertRaisesRegex(ValueError, "Required release file missing.*audit"):
            check_required(self.root)
        with self.assertRaisesRegex(ValueError, "missing required release content"):
            check_zip(self.make_zip())

    def test_missing_comparator_artifact_rejected(self):
        for name in sorted(COMPARATOR_FILES):
            with self.subTest(name=name):
                original = self.read(name)
                (self.root / name).unlink()
                with self.assertRaisesRegex(ValueError, "Required release file missing"):
                    check_required(self.root)
                with self.assertRaisesRegex(ValueError, "missing required release content"):
                    check_zip(self.make_zip())
                self.write(name, original)

    def test_comparator_sources_runner_and_logs_exported(self):
        for name in EXPORT_REQUIRED:
            if not (self.root / name).exists():
                self.write(name, b"fixture\n")
        for directory in DIRECTORIES:
            (self.root / directory).mkdir(exist_ok=True)
        log_name = "audit/comparator/logs/comparator.log"
        self.write(log_name, b"recorded comparator output\n")
        output = Path(self.temporary.name) / "comparator-release.zip"
        count = export_repository(self.root, output)
        with zipfile.ZipFile(output) as archive:
            for name in COMPARATOR_FILES | {log_name}:
                with self.subTest(name=name):
                    self.assertEqual(archive.read(f"{PREFIX}/{name}"), self.read(name))
        self.assertEqual(check_zip(output), count)

    def test_symlink_source_rejected_even_when_bytes_match(self):
        content = self.read("Verification.lean")
        (self.root / "Verification.lean").unlink()
        external = Path(self.temporary.name) / "verification.txt"
        external.write_bytes(content)
        (self.root / "Verification.lean").symlink_to(external)
        with self.assertRaisesRegex(ValueError, "escapes|symlink"):
            check_lean_sources(self.root)

    def test_nested_audit_links_and_line_anchors(self):
        self.write("audit/main-result-2026-09-29/README.md", (
            "[proof](../../Verification.lean#L1)\n"
            "[web](https://example.org/) [heading](#theorem)\n"
            "[reference][proof]\n[proof]: ../../Verification.lean#L1 \"proof\"\n"
            "[angle](<../../docs/manuscript/paper.tex>)\n"
            "```markdown\n[example](missing.md)\n```\n"
            "`[example](also-missing.md)`\n").encode())
        for name in (".lake", ".git", "dist"):
            self.write(f"{name}/ignored.md", b"[bad](missing.md)\n")
        documents, links = check_markdown_links(self.root)
        self.assertGreater(documents, 0)
        self.assertEqual(links, 3)

    def test_broken_and_escaping_markdown_links_rejected(self):
        for target in ("missing.md", "../outside.md", "/etc/hosts", "file:///etc/hosts"):
            with self.subTest(target=target):
                self.write("README.md", f"[bad]({target})\n".encode())
                with self.assertRaisesRegex(ValueError, "local link"):
                    check_markdown_links(self.root)

    def test_bad_line_anchor_and_build_link_rejected(self):
        self.write("README.md", b"[bad](Verification.lean#L2)\n")
        with self.assertRaisesRegex(ValueError, "Invalid line anchor"):
            check_markdown_links(self.root)
        self.write(".lake/build/present.md", b"exists\n")
        self.write("README.md", b"[bad](.lake/build/present.md)\n")
        with self.assertRaisesRegex(ValueError, "excluded build"):
            check_markdown_links(self.root)

    def test_unsafe_zip_paths_rejected(self):
        for name in (f"{PREFIX}/../escape", "/absolute", f"{PREFIX}\\escape",
                     f"{PREFIX}/./ambiguous", "other-root/payload"):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, "Unsafe|Unexpected ZIP root"):
                check_zip(self.make_zip(extra_members=[(name, b"bad")]))

    def test_excluded_zip_content_rejected(self):
        for relative in (".lake/build/Foo.olean", ".git/config", "Check.lean",
                         "scripts/__pycache__/x.pyc", "scripts/x.pyc"):
            with self.subTest(relative=relative), self.assertRaisesRegex(ValueError, "Excluded content"):
                check_zip(self.make_zip(extra_members=[(f"{PREFIX}/{relative}", b"bad")]))

    def test_zip_symlink_rejected(self):
        link = zipfile.ZipInfo(f"{PREFIX}/link")
        link.create_system = 3
        link.external_attr = 0o120777 << 16
        with self.assertRaisesRegex(ValueError, "not a regular file"):
            check_zip(self.make_zip(extra_members=[(link, b"README.md")]))

    def test_zip_unmanifested_member_rejected(self):
        with self.assertRaisesRegex(ValueError, "ZIP manifest inventory differs"):
            check_zip(self.make_zip(extra_members=[(f"{PREFIX}/unlisted.txt", b"extra")]))

    def test_zip_missing_member_rejected(self):
        with self.assertRaisesRegex(ValueError, "ZIP manifest inventory differs"):
            check_zip(self.make_zip(mutate_manifest=lambda text: text + f"{'0' * 64}  absent.txt\n"))

    def test_zip_tampered_checksum_rejected(self):
        with self.assertRaisesRegex(ValueError, "ZIP checksum mismatch"):
            check_zip(self.make_zip(mutate_manifest=lambda text: "0" * 64 + text[64:]))

    def test_zip_frozen_sources_checked_independently_of_export_manifest(self):
        for name in ("Verification.lean", "docs/manuscript/paper.tex"):
            payload = self.payload()
            payload[name] = b"tampered, with freshly recomputed export checksum\n"
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, "changed"):
                check_zip(self.make_zip(payload))


if __name__ == "__main__":
    unittest.main()
