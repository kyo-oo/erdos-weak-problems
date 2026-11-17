# ======================================================================
# CHRONOLOGICAL LABEL -- #0051 / 1132
#    Path         : branches/sol_engineering-repair-run62/scripts/assert-materialization-exact.sh
#    Ref          : origin/sol/engineering-repair-run62
#    First-commit : 2026-08-15 05:11:42 +0530  (1f4700d)
#    Last-commit  : 2026-08-15 05:11:42 +0530  (1f4700d)
#    Total commits: 1
# ======================================================================
# GIT HISTORY (chronological, oldest first)
# ======================================================================
# [01/1] 2026-08-15 05:11:42 +0530  1f4700d  (ker07-dev)
#        Add byte-identical materialization guard
# ======================================================================

#!/usr/bin/env bash
set -euo pipefail

ERDOS_EXPECTED="$(mktemp)"
GST_EXPECTED="$(mktemp)"
cleanup() {
  rm -f "$ERDOS_EXPECTED" "$GST_EXPECTED"
}
trap cleanup EXIT

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
  | tr -d '\r\n' | base64 -d | gzip -d > "$ERDOS_EXPECTED"

tr -d '\r\n' < payload/GSTTactic.lean.gz.b64 \
  | base64 -d | gzip -d > "$GST_EXPECTED"

check_exact() {
  local expected="$1"
  local actual="$2"
  if ! cmp -s "$expected" "$actual"; then
    echo "ERROR: $actual is not byte-identical to its saved payload." >&2
    echo "Decoded payload:" >&2
    sha256sum "$expected" >&2
    echo "Materialized file:" >&2
    sha256sum "$actual" >&2
    exit 1
  fi
  echo "exact materialization verified: $actual"
}

check_exact "$ERDOS_EXPECTED" ErdosTernary2.lean
check_exact "$GST_EXPECTED" GSTTactic.lean
