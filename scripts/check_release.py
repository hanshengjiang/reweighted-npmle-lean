#!/usr/bin/env python3
"""Check frozen sources, portable documentation links, and an optional release ZIP.

This checks integrity and packaging only; it does not run Lean or establish
mathematical correspondence. The recorded hashes are a change detector, not a
cryptographic signature from an independent authority.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
from urllib.parse import unquote, urlsplit
import zipfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "reweighted-npmle-lean"
LEAN_HASHES = "audit/release-checks/original-lean-sources.json"
MANUSCRIPT_HASHES = "docs/manuscript/SHA256SUMS"
MANUSCRIPTS = {"paper.tex", "paper_v2.tex", "paper_v3.tex"}
COMPARATOR_FILES = {
    "audit/comparator/Challenge.lean", "audit/comparator/Solution.lean",
    "audit/comparator/config.json", "audit/comparator/README.md",
    "audit/comparator/DEFINITION_MAP.md", "audit/comparator/review.md",
    "audit/comparator/tooling/tool-provenance.json",
    "audit/comparator/runs/02-nanoda-lean/result.json",
    "audit/comparator/runs/02-nanoda-lean/comparator.log",
    "audit/comparator/runs/02-nanoda-lean/effective-config.json",
    "audit/comparator/runs/03-negative-controls/summary.json",
    "audit/comparator/runs/03-negative-controls/changed-definition.json",
    "audit/comparator/runs/03-negative-controls/changed-definition.log",
    "audit/comparator/runs/03-negative-controls/unproved-solution.json",
    "audit/comparator/runs/03-negative-controls/unproved-solution.log",
    "scripts/run_comparator.py", "scripts/check_comparator_controls.py",
    "scripts/check_comparator_record.py",
}
REQUIRED = {
    "LICENSE", "LICENSE_SCOPE.md", "RELEASE_CHECKS.md", "README.md",
    "lean-toolchain", "lakefile.toml", "lake-manifest.json",
    "audit/main-result-2026-09-29/README.md", LEAN_HASHES, MANUSCRIPT_HASHES,
    *{f"docs/manuscript/{name}" for name in MANUSCRIPTS},
    *COMPARATOR_FILES,
}
EXCLUDED = {".lake", ".git", "dist", "__pycache__", ".DS_Store", "Check.lean"}
HEX_DIGEST = re.compile(r"[0-9a-f]{64}\Z")


def digest(content):
    return hashlib.sha256(content).hexdigest()


def safe_relative(name):
    """Reject ambiguous names before they can be used as filesystem paths."""
    if (not isinstance(name, str) or not name or "\\" in name or ":" in name
            or "\x00" in name or name.startswith("/")
            or any(part in {"", ".", ".."} for part in name.split("/"))):
        raise ValueError(f"Unsafe relative path: {name!r}")
    return PurePosixPath(name)


def checked_file(root, relative):
    safe_relative(relative)
    path = root / relative
    if not path.resolve().is_relative_to(root.resolve()):
        raise ValueError(f"Path escapes the release: {relative}")
    # Inspect the package-relative path, not system aliases such as /tmp.
    if any((root / Path(*Path(relative).parts[:i])).is_symlink()
           for i in range(1, len(Path(relative).parts) + 1)):
        raise ValueError(f"Release input is a symlink: {relative}")
    if not path.is_file():
        raise ValueError(f"Required release file missing: {relative}")
    return path


def parse_checksums(content):
    entries = {}
    for line in content.splitlines():
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        if match is None:
            raise ValueError(f"Malformed SHA-256 manifest line: {line!r}")
        checksum, name = match.groups()
        safe_relative(name)
        if name in entries:
            raise ValueError(f"Duplicate manifest entry: {name}")
        entries[name] = checksum
    if not entries:
        raise ValueError("Empty SHA-256 manifest")
    return entries


def lean_hashes(content):
    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"Duplicate original Lean source: {key}")
            result[key] = value
        return result

    entries = json.loads(content, object_pairs_hook=unique_object)
    if not isinstance(entries, dict) or len(entries) != 112:
        raise ValueError("Original Lean source manifest must contain exactly 112 files")
    for name, checksum in entries.items():
        safe_relative(name)
        if not is_production_lean(name) or not isinstance(checksum, str) or not HEX_DIGEST.fullmatch(checksum):
            raise ValueError(f"Invalid original Lean source entry: {name}")
    return entries


def is_production_lean(name):
    return name in {"ReweightedNPMLE.lean", "Verification.lean"} or (
        name.startswith("ReweightedNPMLE/") and name.endswith(".lean"))


def compare_inventory(expected, actual, description):
    missing, extra = set(expected) - set(actual), set(actual) - set(expected)
    if missing or extra:
        raise ValueError(f"{description} inventory differs: missing={sorted(missing)}, extra={sorted(extra)}")


def check_required(root):
    for name in sorted(REQUIRED):
        checked_file(root, name)


def check_lean_sources(root):
    expected = lean_hashes(checked_file(root, LEAN_HASHES).read_text())
    actual = {p.relative_to(root).as_posix() for p in (root / "ReweightedNPMLE").rglob("*.lean")}
    actual.update(name for name in ("ReweightedNPMLE.lean", "Verification.lean") if (root / name).is_file())
    compare_inventory(expected, actual, "Production Lean source")
    for name, checksum in expected.items():
        if digest(checked_file(root, name).read_bytes()) != checksum:
            raise ValueError(f"Original Lean source changed: {name}")
    return len(expected)


def check_manuscripts(root):
    expected = parse_checksums(checked_file(root, MANUSCRIPT_HASHES).read_text())
    compare_inventory(MANUSCRIPTS, expected, "Frozen manuscript manifest")
    actual = {p.name for p in (root / "docs/manuscript").glob("*.tex")}
    compare_inventory(MANUSCRIPTS, actual, "Frozen manuscript")
    for name, checksum in expected.items():
        if digest(checked_file(root, f"docs/manuscript/{name}").read_bytes()) != checksum:
            raise ValueError(f"Frozen manuscript changed: {name}")
    return len(expected)


def prose_only(text):
    """Exclude Markdown fenced code and inline code from link inspection."""
    lines, fence = [], None
    for line in text.splitlines(keepends=True):
        marker = re.match(r"^ {0,3}(`{3,}|~{3,})", line)
        if fence:
            if marker and marker[1][0] == fence[0] and len(marker[1]) >= len(fence):
                fence = None
            lines.append("\n")
        elif marker:
            fence = marker[1]
            lines.append("\n")
        else:
            lines.append(line)
    return re.sub(r"(`+).*?\1", "", "".join(lines), flags=re.DOTALL)


def markdown_targets(text):
    """Find inline, reference-style, and angle-bracket Markdown destinations.

    Supports escaped characters, parenthesized file names, optional link titles,
    and reference definitions. Heading fragments are checked as file links;
    GitHub #L line anchors are additionally checked against file length.
    """
    text = prose_only(text)
    # Reference definitions are destinations even when currently unused.
    for match in re.finditer(r"^ {0,3}\[[^\]\n]+\]:\s*(?:<([^>]+)>|(\S+))", text, re.MULTILINE):
        yield match[1] or match[2]
    for match in re.finditer(r"\]\(\s*", text):
        start = match.end()
        if text[start:start + 1] == "<":
            end = text.find(">", start + 1)
            if end >= 0:
                yield text[start + 1:end]
            continue
        end, depth = start, 0
        while end < len(text):
            char = text[end]
            if char == "\\" and end + 1 < len(text):
                end += 2
                continue
            if char == "(":
                depth += 1
            elif char == ")":
                if depth == 0:
                    break
                depth -= 1
            elif char.isspace() and depth == 0:
                break
            end += 1
        if end > start:
            yield text[start:end]
    # CommonMark autolinks are absolute URIs or email addresses. URI schemes
    # other than external web/email links must not hide a local absolute path.
    for match in re.finditer(r"<((?:[A-Za-z][A-Za-z0-9+.-]*:)[^<>\s]*)>", text):
        yield match[1]


def check_markdown_links(root):
    root = root.resolve()
    document_count, link_count = 0, 0
    for current, directories, names in os.walk(root, followlinks=False):
        directories[:] = sorted(name for name in directories if name not in EXCLUDED)
        for name in sorted(names):
            if not name.lower().endswith(".md"):
                continue
            document = checked_file(root, (Path(current) / name).relative_to(root).as_posix())
            document_count += 1
            for raw in markdown_targets(document.read_text()):
                target = re.sub(r"\\([!\"#$%&'()*+,\-./:;<=>?@\[\\\]^_`{|}~])", r"\1", raw)
                if target.startswith(("https://", "http://", "mailto:", "#")):
                    continue
                parsed = urlsplit(target)
                if parsed.scheme or parsed.netloc or not parsed.path:
                    raise ValueError(f"Nonportable local link in {document.relative_to(root)}: {raw}")
                local = (document.parent / unquote(parsed.path)).resolve()
                if not local.is_relative_to(root) or not local.exists():
                    raise ValueError(f"Broken or escaping local link in {document.relative_to(root)}: {raw}")
                if any(part in EXCLUDED for part in local.relative_to(root).parts):
                    raise ValueError(f"Link to excluded build/scratch content in {document.relative_to(root)}: {raw}")
                line = re.fullmatch(r"L([1-9][0-9]*)(?:-L?([1-9][0-9]*))?", parsed.fragment)
                if line:
                    start, end = int(line[1]), int(line[2] or line[1])
                    if not local.is_file() or start > end or end > len(local.read_bytes().splitlines()):
                        raise ValueError(f"Invalid line anchor in {document.relative_to(root)}: {raw}")
                link_count += 1
    return document_count, link_count


def check_zip(path):
    with zipfile.ZipFile(path) as archive:
        payload = {}
        for info in archive.infolist():
            name = safe_relative(info.filename)
            if len(name.parts) < 2 or name.parts[0] != PREFIX:
                raise ValueError(f"Unexpected ZIP root: {info.filename}")
            relative = PurePosixPath(*name.parts[1:]).as_posix()
            if any(part in EXCLUDED for part in name.parts) or name.suffix in {".pyc", ".pyo"}:
                raise ValueError(f"Excluded content in ZIP: {info.filename}")
            mode = info.external_attr >> 16
            if stat.S_ISLNK(mode) or info.is_dir() or (stat.S_IFMT(mode) not in {0, stat.S_IFREG}):
                raise ValueError(f"ZIP member is not a regular file: {info.filename}")
            if relative in payload:
                raise ValueError(f"Duplicate ZIP member: {relative}")
            payload[relative] = archive.read(info)
    if "EXPORT_MANIFEST.sha256" not in payload:
        raise ValueError("ZIP is missing EXPORT_MANIFEST.sha256")
    manifest = parse_checksums(payload.pop("EXPORT_MANIFEST.sha256").decode("utf-8"))
    compare_inventory(manifest, payload, "ZIP manifest")
    for name, checksum in manifest.items():
        if digest(payload[name]) != checksum:
            raise ValueError(f"ZIP checksum mismatch: {name}")
    missing = REQUIRED - payload.keys()
    if missing:
        raise ValueError(f"ZIP is missing required release content: {sorted(missing)}")
    sources = lean_hashes(payload[LEAN_HASHES])
    compare_inventory(sources, {name for name in payload if is_production_lean(name)}, "ZIP Lean source")
    for name, checksum in sources.items():
        if digest(payload[name]) != checksum:
            raise ValueError(f"ZIP original Lean source changed: {name}")
    manuscripts = parse_checksums(payload[MANUSCRIPT_HASHES].decode("utf-8"))
    compare_inventory(MANUSCRIPTS, manuscripts, "ZIP manuscript manifest")
    compare_inventory({f"docs/manuscript/{name}" for name in MANUSCRIPTS},
                      {name for name in payload if name.startswith("docs/manuscript/") and name.endswith(".tex")},
                      "ZIP frozen manuscript")
    for name, checksum in manuscripts.items():
        if digest(payload[f"docs/manuscript/{name}"]) != checksum:
            raise ValueError(f"ZIP frozen manuscript changed: {name}")
    return len(payload)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="package directory to check")
    parser.add_argument("--zip", type=Path, help="also check an exported ZIP without extracting it")
    args = parser.parse_args()
    try:
        root = args.root.resolve()
        check_required(root)
        lean_count = check_lean_sources(root)
        manuscript_count = check_manuscripts(root)
        documents, links = check_markdown_links(root)
        print(f"PASS: {lean_count} production Lean source hashes match the original snapshot")
        print(f"PASS: {manuscript_count} frozen manuscript hashes match SHA256SUMS")
        print(f"PASS: required audit and license files; {links} local links in {documents} Markdown files")
        if args.zip:
            files = check_zip(args.zip)
            print(f"PASS: ZIP paths, regular files, exact manifest inventory, {files} checksums, and frozen sources")
    except (ValueError, OSError, UnicodeError, zipfile.BadZipFile) as error:
        parser.exit(1, f"Release integrity check failed: {error}\n")


if __name__ == "__main__":
    main()
