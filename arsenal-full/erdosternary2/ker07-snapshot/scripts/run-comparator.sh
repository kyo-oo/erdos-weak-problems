# ======================================================================
# CHRONOLOGICAL LABEL -- #0011 / 1132
#    Path         : scripts/run-comparator.sh
#    Ref          : main
#    First-commit : 2026-08-14 14:37:16 +0530  (bd8ddb1)
#    Last-commit  : 2026-08-14 15:37:30 +0530  (42cebb6)
#    Total commits: 2
# ======================================================================
# GIT HISTORY (chronological, oldest first)
# ======================================================================
# [01/2] 2026-08-14 14:37:16 +0530  bd8ddb1  (ker07-dev)
#        build: add comparator runner
# [02/2] 2026-08-14 15:37:30 +0530  42cebb6  (ker07-dev)
#        fix: use separately pinned lean4export binary
# ======================================================================

#!/usr/bin/env bash
set -euo pipefail
ROOT="$(pwd)"
CMP_ROOT="$ROOT/.tools/comparator"
EXPORT_ROOT="$ROOT/.tools/lean4export"
CMP_BIN="$CMP_ROOT/.lake/build/bin/comparator"
EXPORT_BIN="$EXPORT_ROOT/.lake/build/bin/lean4export"
FAKE_LANDRUN="$CMP_ROOT/scripts/fake-landrun.sh"

if [ ! -x "$CMP_BIN" ]; then
  echo "Comparator is not built. Run scripts/setup-comparator.sh first." >&2
  exit 2
fi
if [ ! -x "$EXPORT_BIN" ]; then
  echo "lean4export is not built with the project toolchain." >&2
  exit 2
fi

COMPARATOR_LANDRUN="$FAKE_LANDRUN" \
COMPARATOR_LEAN4EXPORT="$EXPORT_BIN" \
lake env "$CMP_BIN" comparator_config.json
