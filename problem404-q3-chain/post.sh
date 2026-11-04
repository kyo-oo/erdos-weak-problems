#!/bin/bash
# post.sh A DEATH_L STAB_L — witness verify (death log), stability run+verify, full-res death log, structure summary.
A=$1; DL=$2; SL=$3
cd /home/z/erdos-weak-problems/problem404-q3-chain || exit 1
echo "== a=$A death L=$DL witness verify:"
./verify_from_log.sh "$A" "logs/c_sweep_a${A}_L${DL}.log"
if [ "$SL" -le 6072 ]; then BIN=./class_dp; elif [ "$SL" -le 16440 ]; then BIN=./class_dp_w136; else BIN=./class_dp_w514; fi
nice -n 10 $BIN "$A" 2 "$SL" --witness --mem 1500 > "logs/c_sweep_a${A}_L${SL}.log" 2> "logs/c_sweep_a${A}_L${SL}.err"
echo "== a=$A stability L=$SL:"
grep -E "first UNREACHABLE|\[C class_dp\]|capped = |peak_states|elapsed_s|peak_rss" "logs/c_sweep_a${A}_L${SL}.log"
./verify_from_log.sh "$A" "logs/c_sweep_a${A}_L${SL}.log"
if [ "$DL" -le 6072 ]; then BINF=./class_dp; elif [ "$DL" -le 16440 ]; then BINF=./class_dp_w136; else BINF=./class_dp_w514; fi
nice -n 10 $BINF "$A" 2 "$DL" --mem 1500 --log 1 > "logs/c_sweep_a${A}_L${DL}_full.log" 2>/dev/null
echo "== structure (full-res at L=$DL):"
python3 - "$A" "$DL" <<'EOF'
import re, sys
A, DL = sys.argv[1], sys.argv[2]
f = f'logs/c_sweep_a{A}_L{DL}_full.log'
rows = []; g = None; hist = None; peak = None
for line in open(f):
    m = re.match(r'V=\s*(\d+): coins=\s*(\d+) states=\s*(\d+) maxevent=(\d+)', line)
    if m: rows.append(tuple(map(int, m.groups()))); continue
    m = re.search(r'g\(\d+,2\) \[C class_dp\] = (\d+)', line)
    if m: g = int(m.group(1))
    if line.startswith('peak_states'): peak = int(line.split('=')[1])
    if line.startswith('final_t_hist:'): hist = line.strip()
nz = [v for v, c, s, me in rows if s > 0]
lastnz = max(nz) if nz else None
firstempty = None
seen_nz = False
for v, c, s, me in rows:
    if s > 0: seen_nz = True
    elif seen_nz: firstempty = v; break
firstg = next((v for v, c, s, me in rows if me == g), None)
d = {v: s for v, c, s, me in rows}
coins = {v: c for v, c, s, me in rows}
print(f"g={g} peak_states={peak}")
print(f"last nonzero-states class={lastnz}, first empty class after live start={firstempty}, maxevent first hits g at class={firstg}")
lo = max(0, (lastnz or 0) - 14); hi = (firstempty or 0) + 2
print("states near death: " + " ".join(f"{v}:{d.get(v,0)}" for v in range(lo, hi + 1)))
print("coins near death:  " + " ".join(f"{v}:{coins.get(v,0)}" for v in range(lo, hi + 1)))
print(hist if hist else "final_t_hist: (none)")
EOF
