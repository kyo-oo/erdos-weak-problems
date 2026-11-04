#!/bin/bash
export PATH="$HOME/.elan/bin:$PATH"
OL=/home/z/f22war/olean
LOGS=/home/z/f22war/logs
cd /home/z/erdos-weak-problems
export LEAN_PATH=$OL
MODS="ExactF22 F22DataS F22DataC F22DataD1 F22DataD2 F22Chain F22SweepA F22SweepB F22Coins F22FM0 F22FM1 F22DD0 F22DD1 F22DD2 F22DD3 F22DD4 F22DD5 F22DD6 F22DD7 F22DD8 F22DD9 F22DDm0 F22DDm1 F22DDm2 F22DDm3 F22DDm4 F22DDm5 F22DDm6 F22Asm0 F22Asm1 F22AllA F22AllB F22AllC F22AllD F22AllE F22AllF F22AllG F22AllH F22All"
for M in $MODS; do
  SRC=problem404-q3-chain/$M.lean
  if [ "$FORCE" != "1" ] && [ -f $OL/$M.olean ] && [ $SRC -nt $OL/$M.olean ]; then :; fi
  if [ "$FORCE" != "1" ] && [ -f $OL/$M.olean ] && [ ! $SRC -nt $OL/$M.olean ]; then echo "=== $M === SKIP (cached)"; continue; fi
  echo "=== $M === $(date +%H:%M:%S)"
  T0=$(date +%s)
  if lean -o $OL/$M.olean $SRC > $LOGS/$M.log 2>&1; then
    T1=$(date +%s); echo "GREEN ($((T1-T0))s)"
  else
    T1=$(date +%s); echo "RED ($((T1-T0))s) — see $LOGS/$M.log"; exit 1
  fi
done
echo "ALL MODULES GREEN"
