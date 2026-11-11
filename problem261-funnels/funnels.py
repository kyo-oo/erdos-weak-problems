#!/usr/bin/env python3
"""FRONT-B: funnel/coalescence census. Which n-ranges die at the same N? Room stats."""
def walk(n, cap=3000000):
    if n == 1: N, v = 3, 2
    else: N, v = n + 1, n
    steps = 0
    while v != 0 and steps < cap:
        if 2 * v >= N: v = 2 * v - N
        else: v = 2 * v
        N += 1; steps += 1
    return (N if v == 0 else None), steps

dieN = {}
rooms = {}
for n in range(1, 4001):
    N, steps = walk(n)
    d = N if N else 'FAIL'
    dieN.setdefault(d, []).append(n)
    rooms[n] = (N - n - 1) if N else None
# the funnel table: death-N -> n-range
funs = sorted(((k, v) for k, v in dieN.items() if isinstance(k, int) and len(v) >= 5), key=lambda x: -len(x[1]))
print("TOP FUNNELS (death N, count, n-range):")
for k, v in funs[:12]:
    print(f"  die at N={k}: {len(v)} walks, n in [{min(v)},{max(v)}]")
# room stats
import statistics
rs = [r for r in rooms.values() if r is not None]
print(f"\nall 1..4000 terminate: {all(r is not None for r in rooms.values())}")
print(f"room: max={max(rs)} mean={statistics.mean(rs):.1f} median={statistics.median(rs)}")
big = sorted(((r, n) for n, r in rooms.items() if r), reverse=True)[:10]
print("worst rooms (room, n):", big)
# how many walks die at each N (the merge structure)
print("\ndeath-N distribution (N: count) top:")
for k, v in sorted(dieN.items(), key=lambda x: -len(x[1]))[:10]:
    print(f"  N={k}: {len(v)}")

# === BATTERY GATE (added for CI) ===
import sys
print()
expected_funnel = {12231: 2578, 4855: 475, 4993: 103, 29753: 47}
ok = True
for D, cnt in expected_funnel.items():
    got = len(dieN.get(D, []))
    if got != cnt:
        print(f"FAIL funnel {D}: expected {cnt}, got {got}"); ok = False
allterm = all(r is not None for r in rooms.values())
if not allterm: print("FAIL: some walk did not terminate"); ok = False
maxroom, maxn = max(((r, n) for n, r in rooms.items() if r is not None))
if (maxroom, maxn) != (152125, 3817):
    print(f"FAIL max room: got ({maxroom}, {maxn})"); ok = False
if not ok: sys.exit(1)
print("ALL FUNNEL CHECKS PASSED")
