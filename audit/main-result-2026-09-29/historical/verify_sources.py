from pathlib import Path
import hashlib,json
before=json.loads(Path('/private/tmp/npmle-statement-audit/source-hashes-before.json').read_text())
missing=[name for name in before if not Path(name).is_file()]
changed=[name for name,h in before.items() if Path(name).is_file() and hashlib.sha256(Path(name).read_bytes()).hexdigest()!=h]
print(f'Fingerprinted source/config/reference files: {len(before)}')
print(f'Missing: {len(missing)}')
print(f'Changed: {len(changed)}')
assert not missing and not changed, (missing,changed)
print('PASS: every fingerprinted formalization file is unchanged.')
