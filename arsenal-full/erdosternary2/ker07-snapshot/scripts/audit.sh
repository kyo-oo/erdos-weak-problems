# ======================================================================
# CHRONOLOGICAL LABEL -- #0012 / 1132
#    Path         : scripts/audit.sh
#    Ref          : main
#    First-commit : 2026-08-14 14:37:30 +0530  (bf72afc)
#    Last-commit  : 2026-08-14 14:37:30 +0530  (bf72afc)
#    Total commits: 1
# ======================================================================
# GIT HISTORY (chronological, oldest first)
# ======================================================================
# [01/1] 2026-08-14 14:37:30 +0530  bf72afc  (ker07-dev)
#        test: add active Lean source audit
# ======================================================================

#!/usr/bin/env bash
set -euo pipefail
python3 - <<'PY'
from pathlib import Path
import re, sys
p=Path('ErdosTernary2.lean')
s=p.read_text(encoding='utf-8')
out=[]; i=0; depth=0; instr=False; esc=False
while i < len(s):
    if depth:
        if s.startswith('/-',i): depth+=1; out.extend('  '); i+=2; continue
        if s.startswith('-/',i): depth-=1; out.extend('  '); i+=2; continue
        out.append('\n' if s[i]=='\n' else ' '); i+=1; continue
    if instr:
        c=s[i]; out.append('\n' if c=='\n' else ' ')
        if esc: esc=False
        elif c=='\\': esc=True
        elif c=='"': instr=False
        i+=1; continue
    if s.startswith('--',i):
        while i<len(s) and s[i]!='\n': out.append(' '); i+=1
        continue
    if s.startswith('/-',i): depth=1; out.extend('  '); i+=2; continue
    if s[i]=='"': instr=True; out.append(' '); i+=1; continue
    out.append(s[i]); i+=1
active=''.join(out)
patterns={
 'sorry':r'\bsorry\b', 'admit':r'\badmit\b', 'mkSorry':r'\bmkSorry\b',
 'axiom_decl':r'^\s*axiom\b', 'native_decide':r'\bnative_decide\b'}
bad=False
for name,pat in patterns.items():
    ms=list(re.finditer(pat,active,re.M))
    print(f'{name}: {len(ms)}')
    for m in ms:
        ln=active.count('\n',0,m.start())+1
        print(f'  line {ln}')
    if ms: bad=True
sys.exit(1 if bad else 0)
PY
