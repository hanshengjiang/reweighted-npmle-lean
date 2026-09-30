"""Check a Lean Verification log; without --log, inspect the historical audit log."""
from argparse import ArgumentParser
from collections import Counter
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
PACKAGE_ROOT = HERE.parents[1]
parser = ArgumentParser(description=__doc__)
parser.add_argument('--log', type=Path, default=HERE / 'verification.log')
args = parser.parse_args()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
expected = re.findall(r'^#print axioms (\S+)\s*$', (PACKAGE_ROOT / 'Verification.lean').read_text(), re.M)
output = args.log.read_text()
reports = re.findall(r"'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", output)
if not expected or len(expected) != len(set(expected)):
    raise SystemExit('FAIL: Verification.lean must contain distinct axiom requests.')
if Counter(name for name, _ in reports) != Counter(expected):
    raise SystemExit('FAIL: Missing, repeated, or unexpected axiom reports.')
counts = Counter()
for name, axioms in reports:
    used = frozenset(a.strip() for a in axioms.split(',') if a.strip())
    if not used <= allowed:
        raise SystemExit(f'FAIL: {name} uses disallowed axioms: {sorted(used - allowed)}')
    counts[used] += 1
for used, count in sorted(counts.items(), key=lambda item: sorted(item[0])):
    print(f'{count} declarations: [{", ".join(sorted(used))}]')
print(f'Independent axiom audit passed: {len(expected)} unique declarations')
print('This checks the supplied log; it does not run Lean or establish how that log was generated.')
