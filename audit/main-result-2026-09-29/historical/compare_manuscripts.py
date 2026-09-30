from pathlib import Path
import difflib, hashlib
root=Path('..')
paths=[root/'paper.tex',root/'paper_v2.tex',root/'paper_v3.tex',Path('docs/paper.tex')]
def block(p):
    s=p.read_text()
    label=s.index(r'\label{thm:main}')
    a=s.rfind(r'\begin{theorem}',0,label)
    b=s.index(r'\end{theorem}',label)+len(r'\end{theorem}')
    return s[a:b]
base=block(paths[0])
for p in paths:
    print(f'{p}: sha256={hashlib.sha256(p.read_bytes()).hexdigest()}')
    b=block(p)
    print('thm:main identical to paper.tex:',b==base)
    if b!=base:
        print(''.join(difflib.unified_diff(base.splitlines(True),b.splitlines(True),fromfile='paper.tex theorem',tofile=f'{p} theorem')))
