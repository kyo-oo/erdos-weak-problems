#!/bin/bash
# Validation battery for class_dp.c (task 2-b)
# Usage: bash run_battery.sh [path-to-binary]  — default ./class_dp; logs/ + results table
cd "$(dirname "$0")"
BIN=${1:-./class_dp}
mkdir -p logs
PASS=0; FAIL=0
# a  L  expected_g   (L = g+1 exactness runs and larger-L stability runs)
RUNS=(
  "4 4 3" "8 7 6" "10 7 6" "12 4 3"          # Lean-proven kills (ExactF22.lean battery)
  "2 254 253" "2 320 253"                     # f(2,2)=254 tight pair
  "6 130 129" "6 200 129"
  "16 534 533" "16 600 533"
  "18 46 45" "18 120 45"
  "24 40 39" "24 120 39"
  "30 101 100" "30 180 100"
  "38 794 793" "38 900 793"
)
printf "%6s %6s %10s %10s %8s %8s %s [%s]  bin=%s\n" a L g_exp g_got fu capped verdict "$BIN"
for r in "${RUNS[@]}"; do
  set -- $r; A=$1; L=$2; GE=$3
  LOG=logs/c_val_a${A}_L${L}.log; ERR=logs/c_val_a${A}_L${L}.err
  nice -n 10 "$BIN" "$A" 2 "$L" --witness --mem 1500 > "$LOG" 2> "$ERR"
  rc=$?
  GG=$(sed -n 's/^g([0-9]*,2) \[C class_dp\] = //p' "$LOG" | tail -1)
  FU=$(sed -n 's/^first UNREACHABLE level = //p' "$LOG" | tail -1)
  CAP=$(sed -n 's/^capped = //p' "$LOG" | tail -1)
  WIT=$(grep -m1 '^WITNESS' "$LOG" || echo "WITNESS = MISSING")
  # independent pure-Python verification of the witness subset
  WL=$(grep -m1 '^WITNESS_LIST' "$LOG" | cut -d' ' -f2-)
  PYV="n/a"
  if [ -n "$WL" ]; then
    GLEV=$(echo "$WIT" | sed -n 's/.*g-level=\([0-9]*\).*/\1/p')
    if nice -n 10 python3 verify_witness.py "$A" "$GLEV" $WL >/tmp/pyv_${A}_${L}.txt 2>&1; then
      PYV="py:PASS($(sed -n 's/.*= \([0-9]*\)  expected.*/\1/p' /tmp/pyv_${A}_${L}.txt | head -1))"
    else PYV="py:FAIL"; fi
  fi
  ok=1
  [ "$GG" = "$GE" ] || ok=0
  [ "$CAP" = "0" ] || ok=0
  echo "$WIT" | grep -q "VERIFIED" || ok=0
  [ "$PYV" != "py:FAIL" ] || ok=0
  if [ $ok -eq 1 ]; then V="PASS"; PASS=$((PASS+1)); else V="FAIL(rc=$rc)"; FAIL=$((FAIL+1)); fi
  printf "%6s %6s %10s %10s %8s %8s %s [%s]\n" "$A" "$L" "$GE" "$GG" "$FU" "$CAP" "$V" "$PYV"
done
echo "BATTERY: PASS=$PASS FAIL=$FAIL"
