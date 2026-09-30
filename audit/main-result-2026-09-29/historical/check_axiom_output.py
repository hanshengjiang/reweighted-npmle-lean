from collections import Counter
from pathlib import Path
import re
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
expected = re.findall(r'^#print axioms (\S+)\s*$', Path('Verification.lean').read_text(), re.M)
output = Path('/private/tmp/npmle-statement-audit/verification.log').read_text()
reports = re.findall(r"'([^'\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", output)
assert len(expected) == len(set(expected)) and expected
assert Counter(name for name, _ in reports) == Counter(expected)
counts = Counter()
for name, axioms in reports:
    used = frozenset(a.strip() for a in axioms.split(',') if a.strip())
    assert used <= allowed, (name, used - allowed)
    counts[used] += 1
for used, count in sorted(counts.items(), key=lambda item: sorted(item[0])):
    print(f'{count} declarations: [{", ".join(sorted(used))}]')
print(f'Independent axiom audit passed: {len(expected)} unique declarations')
