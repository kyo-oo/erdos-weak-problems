#!/usr/bin/env bash
# sorry_check.sh — V5 verification gate
#
# Counts `sorry` tactic occurrences in submitted solution/project .lean files.
# Excludes backups, the .lake build cache, and the intentional comparator
# question-side hole in questions/deepmind_problem_406/Challenge.lean.
#
# MUST return 0 for executable solution/proof sources BEFORE the comparator is run.

set -uo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

# Whole-word grep for the `sorry` tactic, excluding backups, .lake cache, and
# the official Problem 406 challenge file. The challenge-side `sorry` is the
# benchmark question; it is not part of the submitted solution proof.
SORRY_LINES=$(grep -rwn 'sorry' --include='*.lean' . 2>/dev/null \
  | grep -v '\.bak' \
  | grep -v '/\.lake/' \
  | grep -v '^\./questions/deepmind_problem_406/Challenge\.lean:' \
  || true)

if [ -z "$SORRY_LINES" ]; then
  echo "sorry_check: 0 submitted-solution sorries found ✓"
  echo "sorry_check: intentional Problem 406 challenge hole excluded ✓"
  exit 0
else
  SORRY_COUNT=$(printf '%s\n' "$SORRY_LINES" | wc -l | tr -d ' ')
  echo "sorry_check: $SORRY_COUNT submitted-solution sorry(s) found ✗"
  echo "$SORRY_LINES"
  exit 1
fi
