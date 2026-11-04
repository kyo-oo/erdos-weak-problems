#!/bin/bash
# run_block.sh <tag> <lo> <hi> [certin] — one frontier block (session Q1 protocol)
# war261b batch, cap 2e9, round0 1e8 x10, bits 20, tbits 23, chunk 10000,
# emitmin 1e9; nice -n 10, hard timeout 900 s; logs EXIT + peak RSS (VmHWM).
cd "$(dirname "$0")/.." || exit 9
tag=$1; lo=$2; hi=$3; certin=${4:-run261/cert_march.txt}
log="run261/${tag}_log.txt"
nice -n 10 timeout 900 ./war261b batch "$lo" "$hi" 2000000000 100000000 10 20 23 \
    10000 1000000000 "run261/${tag}_deaths.txt" "run261/${tag}_merges.txt" \
    "run261/${tag}_snap.bin" "$certin" "run261/cert_${tag}.txt" > "$log" 2>&1 &
pid=$!
peak=0
while kill -0 $pid 2>/dev/null; do
  # timeout(1) forks the engine as a child: sample the whole subtree
  for p in $pid $(cat /proc/$pid/task/$pid/children 2>/dev/null); do
    v=$(awk '/VmHWM/{print $2}' /proc/$p/status 2>/dev/null)
    [ -n "$v" ] && [ "$v" -gt "$peak" ] && peak=$v
  done
  sleep 0.5
done
wait $pid; rc=$?
echo "EXIT=$rc MAXRSS_KB=$peak" >> "$log"
exit $rc
