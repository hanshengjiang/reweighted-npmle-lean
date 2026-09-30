"""Print exact main-theorem differences for the frozen manuscript snapshots."""
from pathlib import Path
import difflib
import hashlib

PACKAGE_ROOT = Path(__file__).resolve().parents[2]
paths = [PACKAGE_ROOT / 'docs/manuscript' / name for name in ('paper.tex', 'paper_v2.tex', 'paper_v3.tex')]
paths.append(PACKAGE_ROOT / 'docs/paper.tex')

def block(path):
    source = path.read_text()
    label = source.index(r'\label{thm:main}')
    start = source.rfind(r'\begin{theorem}', 0, label)
    if start < 0:
        raise ValueError(f'Missing theorem start: {path}')
    end = source.index(r'\end{theorem}', label) + len(r'\end{theorem}')
    return source[start:end]

base = block(paths[0])
for path in paths:
    name = path.relative_to(PACKAGE_ROOT).as_posix()
    print(f'{name}: sha256={hashlib.sha256(path.read_bytes()).hexdigest()}')
    text = block(path)
    print('thm:main identical to paper.tex:', text == base)
    if text != base:
        print(''.join(difflib.unified_diff(base.splitlines(True), text.splitlines(True),
            fromfile='paper.tex theorem', tofile=f'{name} theorem')))
