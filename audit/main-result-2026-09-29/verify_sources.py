"""Compare production Lean sources and dependency pins with historical audit hashes.

This is intentionally narrower than the original 120-file author-machine check.
The omitted Check.lean was scratch code; release packaging and reference files
are outside this source-only comparison. See historical/verify_sources.py.
"""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
PACKAGE_ROOT = HERE.parents[1]
before = json.loads((HERE / 'source-hashes-before.json').read_text())
selected = {name: digest for name, digest in before.items()
            if (name.endswith('.lean') and name != 'Check.lean')
            or name in {'lean-toolchain', 'lake-manifest.json'}}
actual_lean = {path.relative_to(PACKAGE_ROOT).as_posix()
               for path in (PACKAGE_ROOT / 'ReweightedNPMLE').rglob('*.lean')}
actual_lean.update({'ReweightedNPMLE.lean', 'Verification.lean'})
expected_lean = {name for name in selected if name.endswith('.lean')}
if actual_lean != expected_lean:
    raise SystemExit(f'FAIL: production Lean file set differs: {sorted(actual_lean ^ expected_lean)}')
missing = [name for name in selected if not (PACKAGE_ROOT / name).is_file()]
changed = [name for name, digest in selected.items()
           if (PACKAGE_ROOT / name).is_file()
           and hashlib.sha256((PACKAGE_ROOT / name).read_bytes()).hexdigest() != digest]
print(f'Historical manifest entries: {len(before)}')
print(f'Checked production Lean sources: {len(expected_lean)}')
print(f'Checked toolchain/dependency pins: {len(selected) - len(expected_lean)}')
print(f'Excluded historical entries: {len(before) - len(selected)}')
for name in sorted(set(before) - set(selected)):
    print(f'  excluded: {name}')
print(f'Missing: {len(missing)}')
print(f'Changed: {len(changed)}')
if missing or changed:
    raise SystemExit(f'FAIL: missing={missing}, changed={changed}')
print('PASS: packaged production Lean sources and dependency pins match historical hashes.')
print('Release documentation, data, and lakefile metadata are outside this comparison.')
