#!/bin/bash
# Witness verification helper: extract WITNESS line + WITNESS_LIST from a log,
# run pure-Python verify_witness.py with the g-level as expected value.
# Usage: ./verify_from_log.sh A LOGFILE
A=$1
LOG=$2
cd /home/z/erdos-weak-problems/problem404-q3-chain || exit 1
gl=$(grep -oP 'g-level=\K[0-9]+' "$LOG" | tail -1)
wline=$(grep -m1 'WITNESS = ' "$LOG")
list=$(grep -m1 'WITNESS_LIST ' "$LOG" | cut -d' ' -f2-)
if [ -z "$gl" ] || [ -z "$list" ]; then echo "NO WITNESS in $LOG"; exit 1; fi
echo "$wline"
python3 verify_witness.py "$A" "$gl" $list
