#!/usr/bin/env python3
"""Create a clean standalone ZIP without creating or uploading a repository."""

import argparse
import hashlib
import os
from pathlib import Path
import tempfile
import zipfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "reweighted-npmle-lean"
REQUIRED = (
    ".gitignore", "README.md", "PUBLICATION.md", "lakefile.toml", "lake-manifest.json",
    "lean-toolchain", "ReweightedNPMLE.lean", "Verification.lean",
)
OPTIONAL = ("PAPER_COVERAGE.md", "FORMALIZATION_STATUS.md", "COMPLETION_AUDIT.md",
            "PROPOSED_NUMERICAL_CORRECTIONS.md", "LICENSE", "LICENSE.md", "LICENSE_SCOPE.md",
            "RELEASE_CHECKS.md", "CITATION.cff")
DIRECTORIES = ("ReweightedNPMLE", "scripts", "tests", "data", "docs", ".github", "audit")
EXCLUDED = {".git", ".lake", "__pycache__", ".DS_Store", "Check.lean"}


def repository_files(root):
    for name in REQUIRED:
        if not (root / name).is_file():
            raise ValueError(f"Required repository file missing: {name}")
    files = [root / name for name in REQUIRED + OPTIONAL if (root / name).is_file()]
    if any(path.is_symlink() for path in files):
        raise ValueError("Root repository files must not be symlinks")
    for directory in DIRECTORIES:
        base = root / directory
        if not base.is_dir():
            raise ValueError(f"Required repository directory missing: {directory}")
        if base.is_symlink():
            raise ValueError(f"Repository directories must not be symlinks: {directory}")
        for current, directories, names in os.walk(base, followlinks=False):
            if any((Path(current) / name).is_symlink() for name in directories if name not in EXCLUDED):
                raise ValueError(f"Symlink directory is not a portable input: {current}")
            directories[:] = [d for d in directories if d not in EXCLUDED]
            for name in names:
                path = Path(current) / name
                if name in EXCLUDED or path.suffix in {".pyc", ".pyo"}:
                    continue
                if path.is_symlink():
                    raise ValueError(f"Symlinks are not portable export inputs: {path}")
                files.append(path)
    return sorted(files, key=lambda path: path.relative_to(root).as_posix())


def export_repository(root, output, force=False):
    if output.suffix != ".zip":
        raise ValueError("The export output must be a .zip file")
    if output.exists() and not force:
        raise ValueError(f"Refusing to overwrite {output}; use --force if intended")
    files = repository_files(root)
    if output.is_relative_to(root) and output.relative_to(root).parts[0] in DIRECTORIES:
        raise ValueError("Export output must not be inside a source directory")
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(dir=output.parent, suffix=".zip", delete=False) as handle:
            temporary = Path(handle.name)
        with zipfile.ZipFile(temporary, "w", compression=zipfile.ZIP_DEFLATED) as archive:
            def write(relative, content):
                info = zipfile.ZipInfo(f"{PREFIX}/{relative}")
                info.compress_type = zipfile.ZIP_DEFLATED
                info.create_system = 3
                info.external_attr = 0o100644 << 16
                archive.writestr(info, content)

            manifest = []
            for path in files:
                relative = path.relative_to(root).as_posix()
                content = path.read_bytes()
                write(relative, content)
                manifest.append(f"{hashlib.sha256(content).hexdigest()}  {relative}")
            write("EXPORT_MANIFEST.sha256", "\n".join(manifest) + "\n")
        os.replace(temporary, output)
        temporary = None
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)
    return len(files)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "dist" / f"{PREFIX}.zip")
    parser.add_argument("--force", action="store_true", help="intentionally replace an existing export")
    args = parser.parse_args()
    output = args.output.resolve()
    try:
        count = export_repository(ROOT, output, args.force)
    except (ValueError, OSError) as error:
        parser.exit(1, f"Export failed: {error}\n")
    print(f"Created {output}: {count} repository files plus SHA-256 manifest; nothing uploaded")


if __name__ == "__main__":
    main()
