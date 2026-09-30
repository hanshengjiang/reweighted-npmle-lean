from pathlib import Path
import hashlib
import re
import tempfile
import unittest
import zipfile

from scripts.export_repository import DIRECTORIES, PREFIX, REQUIRED, export_repository, repository_files
from scripts.verify import audit_output


class AxiomAuditTests(unittest.TestCase):
    def test_standard_and_axiom_free(self):
        result = audit_output("'Foo' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"
                              "'Bar' does not depend on any axioms\n", ["Foo", "Bar"])
        self.assertEqual(sum(result.values()), 2)

    def test_unexpected_axiom_rejected(self):
        with self.assertRaises(ValueError):
            audit_output("'Foo' depends on axioms: [sorryAx]", ["Foo"])

    def test_missing_duplicate_or_unknown_report_rejected(self):
        for output in ("", "'Foo' does not depend on any axioms\n" * 2,
                       "'Other' does not depend on any axioms"):
            with self.subTest(output=output), self.assertRaises(ValueError):
                audit_output(output, ["Foo"])

    def test_invalid_expected_list_rejected(self):
        for expected in ([], ["Foo", "Foo"]):
            with self.subTest(expected=expected), self.assertRaises(ValueError):
                audit_output("", expected)


class ExportTests(unittest.TestCase):
    def fixture(self, root):
        for name in REQUIRED:
            (root / name).write_text("fixture\n")
        for name in DIRECTORIES:
            (root / name).mkdir()
            (root / name / "included.txt").write_text("included\n")
        (root / "Check.lean").write_text("scratch\n")
        for name in (".git", ".lake", "scripts/__pycache__"):
            (root / name).mkdir(parents=True, exist_ok=True)
            (root / name / "excluded.txt").write_text("excluded\n")

    def test_clean_export_and_manifest(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            count = export_repository(root, root / "dist/export.zip")
            with zipfile.ZipFile(root / "dist/export.zip") as archive:
                names = archive.namelist()
                self.assertEqual(len(names), count + 1)
                self.assertIn(f"{PREFIX}/.gitignore", names)
                self.assertIn(f"{PREFIX}/.github/included.txt", names)
                self.assertTrue(all("Check.lean" not in n and "/.lake/" not in n and
                                    "/.git/" not in n and "__pycache__" not in n for n in names))
                self.assertIn(f"{PREFIX}/EXPORT_MANIFEST.sha256", names)
                manifest = archive.read(f"{PREFIX}/EXPORT_MANIFEST.sha256").decode()
                for line in manifest.splitlines():
                    digest, relative = line.split("  ", 1)
                    self.assertEqual(digest, hashlib.sha256(archive.read(f"{PREFIX}/{relative}")).hexdigest())

    def test_overwrite_requires_force(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            output = root / "export.zip"
            export_repository(root, output)
            original = output.read_bytes()
            with self.assertRaises(ValueError):
                export_repository(root, output)
            export_repository(root, output, force=True)
            self.assertEqual(original, output.read_bytes())

    def test_missing_root_file_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(ValueError):
                repository_files(Path(directory))

    def test_symlink_input_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            (root / "docs/link.txt").symlink_to(root / "README.md")
            with self.assertRaises(ValueError):
                repository_files(root)

    def test_output_inside_sources_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.fixture(root)
            with self.assertRaises(ValueError):
                export_repository(root, root / "docs/export.zip")


class StandalonePathsTests(unittest.TestCase):
    def test_generator_inputs_are_bundled(self):
        from scripts import generate_numerical_data as generator
        root = Path(__file__).resolve().parents[1]
        self.assertEqual(generator.FORMALIZATION, root)
        self.assertEqual(generator.ROOT, root / "data")
        for source in generator.SOURCES + [generator.PATH_SOURCE, generator.KEY_FINDINGS_SOURCE,
                                          generator.MULTISTART_SOURCE, generator.TABLE_SOURCE]:
            self.assertTrue(source.is_file())
            self.assertTrue(source.is_relative_to(root))

    def test_markdown_file_links_stay_inside_package(self):
        root = Path(__file__).resolve().parents[1]
        documents = list(root.glob("*.md")) + list((root / "docs").glob("*.md"))
        documents += list((root / "data").glob("*.md"))
        documents += list((root / "audit").rglob("*.md"))
        documents += list((root / "docs/manuscript").glob("*.md"))
        for document in documents:
            for target in re.findall(r"\[[^\]]+\]\(([^)]+)\)", document.read_text()):
                if target.startswith(("http://", "https://", "#")):
                    continue
                path = (document.parent / target.split("#")[0]).resolve()
                with self.subTest(document=document.name, target=target):
                    self.assertTrue(path.is_relative_to(root))
                    self.assertTrue(path.exists())


if __name__ == "__main__":
    unittest.main()
