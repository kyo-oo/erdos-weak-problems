# ======================================================================
# CHRONOLOGICAL LABEL -- #0016 / 1132
#    Path         : scripts/materialize-source.sh
#    Ref          : main
#    First-commit : 2026-08-14 14:41:31 +0530  (614b74d)
#    Last-commit  : 2026-08-15 01:12:42 +0530  (4669bb5)
#    Total commits: 7
# ======================================================================
# GIT HISTORY (chronological, oldest first)
# ======================================================================
# [01/7] 2026-08-14 14:41:31 +0530  614b74d  (ker07-dev)
#        build: materialize exact saved Lean sources
# [02/7] 2026-08-14 14:59:51 +0530  0d6b342  (ker07-dev)
#        build: reconstruct exact Lean sources from verified chunks
# [03/7] 2026-08-14 15:02:49 +0530  c5d7f34  (ker07-dev)
#        build: use verified replacement subchunks for exact source
# [04/7] 2026-08-14 23:52:42 +0530  1f687b9  (ker07-dev)
#        Use zero-sorry Sol checkpoint for comparator
# [05/7] 2026-08-15 00:27:57 +0530  28ab599  (ker07-dev)
#        Reactivate complete residual theorem chain
# [06/7] 2026-08-15 01:08:55 +0530  2b0178a  (ker07-dev)
#        Reframe final bridge as GST spacetime recurrence
# [07/7] 2026-08-15 01:12:42 +0530  4669bb5  (ker07-dev)
#        Normalize payload line endings before decoding
# ======================================================================

#!/usr/bin/env bash
set -euo pipefail

cat \
  payload/ErdosTernary2.parts/00 \
  payload/ErdosTernary2.parts/01 \
  payload/ErdosTernary2.parts/02 \
  payload/ErdosTernary2.parts/03 \
  payload/ErdosTernary2.parts/04a \
  payload/ErdosTernary2.parts/04b0 \
  payload/ErdosTernary2.parts/04b1 \
  payload/ErdosTernary2.parts/05a \
  payload/ErdosTernary2.parts/05b \
  | tr -d '\r\n' | base64 -d | gzip -d > ErdosTernary2.lean

tr -d '\r\n' < payload/GSTTactic.lean.gz.b64 | base64 -d | gzip -d > GSTTactic.lean

python3 - <<'PY'
from pathlib import Path
import hashlib, sys
expected = {
    'ErdosTernary2.lean': '9cfd86dfeaeea18fafbe5f339654553896d2cfa1959e37874021bb006abdf272',
    'GSTTactic.lean': '5ec0347da6b6a7d8e19696461761d505bf748523c4b6b6a1d93f439d1493de05',
}
for name, want in expected.items():
    p = Path(name)
    got = hashlib.sha256(p.read_bytes()).hexdigest()
    print(f'{name}: {p.stat().st_size} bytes sha256={got}')
    if got != want:
        print(f'SHA mismatch for {name}: expected {want}', file=sys.stderr)
        raise SystemExit(1)
PY
