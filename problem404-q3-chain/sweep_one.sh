#!/bin/bash
# Task 1-a driver: adaptive L doubling until death (capped=0), max L=32768 (w514).
# Usage: ./sweep_one.sh A
A=$1
cd /home/z/erdos-weak-problems/problem404-q3-chain || exit 1
for L in 300 600 1200 2400 4800 9600 19200 32768; do
  if   [ $L -le 6072  ]; then BIN=./class_dp
  elif [ $L -le 16440 ]; then BIN=./class_dp_w136
  else                       BIN=./class_dp_w514
  fi
  LOG=logs/c_sweep_a${A}_L${L}.log
  ERR=logs/c_sweep_a${A}_L${L}.err
  timeout 1000 nice -n 10 $BIN $A 2 $L --witness --mem 1500 > "$LOG" 2> "$ERR"
  rc=$?
  cap=$(grep -oP '^capped = \K[0-9]+' "$LOG" 2>/dev/null | tail -1)
  g=$(grep -oP '\[C class_dp\] = \K[0-9]+' "$LOG" 2>/dev/null | tail -1)
  fu=$(grep -oP '^first UNREACHABLE level = \K[0-9]+' "$LOG" 2>/dev/null | tail -1)
  el=$(grep -oP '^elapsed_s = \K[0-9.]+' "$LOG" 2>/dev/null | tail -1)
  rss=$(grep -oP '^peak_rss_mb = \K[0-9]+' "$LOG" 2>/dev/null | tail -1)
  echo "a=$A L=$L rc=$rc capped=$cap g=$g first_unreach=${fu:->L} elapsed=${el}s rss=${rss}MB bin=$BIN"
  if [ "$cap" = "0" ]; then echo "=== DEATH a=$A at L=$L: g=$g first_unreachable=$fu ==="; exit 0; fi
  if [ $rc -ne 0 ] && [ $rc -ne 124 ]; then echo "=== ENGINE rc=$rc (memcap/signal) at L=$L ==="; exit $rc; fi
  if [ $rc -eq 124 ]; then echo "=== TIMEOUT at L=$L ==="; exit 124; fi
done
echo "=== a=$A ALIVE at L=32768 (unbounded candidate) ==="
exit 1
