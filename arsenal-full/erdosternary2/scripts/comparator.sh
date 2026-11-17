#!/usr/bin/env bash
# comparator.sh — Lean Comparator (V5)
# V5 trigger: rerun after GSTInfiniteFourPowerNavigation tactic hardening.
#
# The final verification tool referenced by the maths-researcher V5 skill.
# Runs AFTER sorry_check.sh returns 0.
#
# Pipeline:
#   1. lake build          → 0 errors required
#   2. sorry_check.sh      → 0 sorries required
#   3. verdict             → prints "Your solution is okay!" on success
#
# Exit code 0 = CLEAN (comparator passes).
# Exit code 1 = FAIL (build errors OR sorries remain).

set -uo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

# Ensure elan is on PATH (for codespaces / fresh shells)
if [ -d "$HOME/.elan/bin" ] && ! command -v lean >/dev/null 2>&1; then
  export PATH="$HOME/.elan/bin:$PATH"
fi

CYAN='\033[0;36m'
GREEN='\033[0;32m'
RED='\033[0;31m'
BOLD='\033[1m'
RESET='\033[0m'

echo -e "${BOLD}=== LEAN COMPARATOR (V5) ===${RESET}"
echo ""

# ─── Step 1: Build ───────────────────────────────────────────────
echo -e "${CYAN}[1/3] Compiling Lean project (lake build)...${RESET}"
BUILD_LOG="$(mktemp)"
if lake build > "$BUILD_LOG" 2>&1; then
  echo -e "  ${GREEN}✓ Build succeeded (0 errors)${RESET}"
else
  echo -e "  ${RED}✗ Build FAILED${RESET}"
  echo ""
  echo "--- Build errors / failing target trail ---"
  grep -nE 'error:|Some required targets|logged failures|Build FAILED|build failed|GSTGraphV2SixAdicOntologicalGeometry' "$BUILD_LOG" | tail -120 || true
  echo ""
  echo "--- Build output (last 240 lines) ---"
  tail -240 "$BUILD_LOG"
  rm -f "$BUILD_LOG"
  echo ""
  echo -e "${RED}=== COMPARATOR RESULT: FAIL (build errors) ===${RESET}"
  exit 1
fi
rm -f "$BUILD_LOG"

# ─── Step 2: Sorry check ────────────────────────────────────────
echo -e "${CYAN}[2/3] Checking for sorries (sorry_check.sh)...${RESET}"
if bash "$(dirname "$0")/sorry_check.sh"; then
  echo -e "  ${GREEN}✓ 0 sorries confirmed${RESET}"
else
  echo -e "  ${RED}✗ Sorries remain — fix them before comparator can pass${RESET}"
  echo ""
  echo -e "${RED}=== COMPARATOR RESULT: FAIL (sorries exist) ===${RESET}"
  exit 1
fi

# ─── Step 3: Verdict ────────────────────────────────────────────
echo -e "${CYAN}[3/3] Computing verdict...${RESET}"
echo ""
echo -e "${GREEN}${BOLD}========================================${RESET}"
echo -e "${GREEN}${BOLD}  Your solution is okay!${RESET}"
echo -e "${GREEN}${BOLD}========================================${RESET}"
echo ""
echo "  Build:   0 errors"
echo "  Sorries: 0"
echo "  Status:  CLEAN ✓"
echo ""
echo -e "${GREEN}=== COMPARATOR RESULT: PASS ===${RESET}"
exit 0
