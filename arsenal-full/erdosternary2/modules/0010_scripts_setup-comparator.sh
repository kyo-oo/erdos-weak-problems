/- ======================================================================
/- CHRONOLOGICAL LABEL — #0010 / 1133
/-    Path         : scripts/setup-comparator.sh
/-    Ref          : main
/-    First-commit : 2026-08-14 14:37:03 +0530
/-    Last-commit  : 2026-08-14 15:52:04 +0530
/-    Total commits: 5
/- ======================================================================
/- GIT HISTORY (chronological, oldest first)
/- ======================================================================
/- ====================================================================== -/

# ======================================================================
# CHRONOLOGICAL LABEL -- #0010 / 1132
#    Path         : scripts/setup-comparator.sh
#    Ref          : main
#    First-commit : 2026-08-14 14:37:03 +0530  (132f8ea)
#    Last-commit  : 2026-08-14 15:52:04 +0530  (0b6e702)
#    Total commits: 5
# ======================================================================
# GIT HISTORY (chronological, oldest first)
# ======================================================================
# [01/5] 2026-08-14 14:37:03 +0530  132f8ea  (ker07-dev)
#        build: install Lean, mathlib, lean4export and comparator
# [02/5] 2026-08-14 14:42:45 +0530  7918212  (ker07-dev)
#        build: materialize exact saved Lean sources before comparator build
# [03/5] 2026-08-14 15:37:20 +0530  1e8f756  (ker07-dev)
#        fix: pin judge tools using official lean-eval setup pattern
# [04/5] 2026-08-14 15:44:33 +0530  3e3cefc  (ker07-dev)
#        fix: use verified v4.33.0-rc2 judge commits
# [05/5] 2026-08-14 15:52:04 +0530  0b6e702  (ker07-dev)
#        fix: pin Comparator internal lean4export dependency
# ======================================================================

#!/usr/bin/env bash
set -euo pipefail
source "$HOME/.elan/env" 2>/dev/null || true
mkdir -p .tools

bash scripts/materialize-source.sh

if ! command -v elan >/dev/null 2>&1; then
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
  source "$HOME/.elan/env"
fi
elan toolchain install "$(cat lean-toolchain)" || true
elan default "$(cat lean-toolchain)"

lake update
lake exe cache get
lake build GSTTactic ErdosTernary2 Challenge Solution

LEAN4EXPORT_REV=9fb131bb100eb32ccf6836f14e4f8328d13b6792
COMPARATOR_REV=75c730e9b6ef5c2c3b334fad7c3d51fe20624c88

rm -rf .tools/lean4export .tools/comparator

git clone https://github.com/leanprover/lean4export.git .tools/lean4export
(
  cd .tools/lean4export
  git checkout "$LEAN4EXPORT_REV"
  cp ../../lean-toolchain lean-toolchain
  lake update
  lake build lean4export
)

git clone https://github.com/leanprover/comparator.git .tools/comparator
(
  cd .tools/comparator
  git checkout "$COMPARATOR_REV"
  python3 - <<'PY'
from pathlib import Path
p = Path('lakefile.toml')
s = p.read_text()
s = s.replace('rev = "master"', 'rev = "9fb131bb100eb32ccf6836f14e4f8328d13b6792"')
p.write_text(s)
PY
  cp ../../lean-toolchain lean-toolchain
  lake update
  lake build comparator
)
