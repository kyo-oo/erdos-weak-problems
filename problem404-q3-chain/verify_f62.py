#!/usr/bin/env python3
"""ERDŐS #404 f(6,2) = 133 — independent verification battery.

Re-verifies, exact integers only, deterministic:
  * the 61-element witness: v2(6! + Σ_{i∈B} i!) = 133;
  * the g-level: v2(1 + Σ_{i∈B} i!/6!) = 129;
  * the FULL scheduled-precision coin-DP death certificate at level 130
    (pure-Python twin of the C engine and the Lean obstructionCheck):
    NO subset of the (6,2) staircase reaches v2 ≥ 130;
  * the coin table wellformedness (129 coins, classes [0,127], sorted).
"""
import math, sys

def v2(n): return (n & -n).bit_length() - 1 if n else 0

F = [math.factorial(i) for i in range(140)]
checks = 0
def ck(name, cond):
    global checks
    checks += 1
    if not cond:
        print(f"FAIL: {name}"); sys.exit(1)

B6 = [7, 8, 13, 16, 19, 22, 28, 30, 31, 34, 35, 36, 38, 40, 41, 45, 46, 48,
      52, 53, 54, 55, 57, 61, 62, 64, 65, 70, 71, 73, 75, 78, 81, 87, 88,
      91, 92, 93, 95, 96, 101, 103, 104, 107, 108, 109, 111, 112, 114, 115,
      117, 118, 119, 120, 125, 127, 128, 129, 130, 132, 135]

# ---- witness ----
ck("witness size", len(B6) == 61)
ck("witness distinct", len(set(B6)) == 61)
ck("witness min >= 7", min(B6) == 7)
ck("witness max <= 135", max(B6) == 135)
S = 720 + sum(F[i] for i in B6)
ck("witness valuation = 133", v2(S) == 133)
G = 1 + sum(F[i] // 720 for i in B6)
ck("g-level = 129", v2(G) == 129)
ck("f(6,2) = v2(6!) + g = 4 + 129 = 133", v2(720) == 4 and 4 + 129 == 133)

# ---- the coin table (mirror of Lean coinList/table) ----
CP = 138
def classOf(i): return v2(F[i]) - 4
def coinUnit(i):
    c = classOf(i)
    return (F[i] // 720 // (1 << c)) % (1 << (CP - c))
coins = [(i, classOf(i), coinUnit(i)) for i in range(7, 136)]
ck("coin count = 129", len(coins) == 129)
ck("classes fill [0,127]", min(c[1] for c in coins) == 0 and max(c[1] for c in coins) == 127)
ck("coin 7 class 0", classOf(7) == 0)
ck("coin 8 class 3", classOf(8) == 3)
ck("coin 135 class 127", classOf(135) == 127)
ck("coin 136 class 130 (dead)", v2(F[136]) - 4 == 130)
# sortedness (insertion order == Lean sortCoins)
def insertCoin(c, ds):
    out, ins = [], False
    for d in ds:
        if not ins and (c[1] < d[1] or (c[1] == d[1] and c[0] < d[0])):
            out.append(c); ins = True
        out.append(d)
    if not ins: out.append(c)
    return out
tbl = []
for c in reversed(coins): tbl = insertCoin(c, tbl)
ck("table sorted", all(tbl[k][1] <= tbl[k+1][1] for k in range(len(tbl)-1)))

# ---- the DP death certificate (mirror of Lean stepCoin/dpRun) ----
def step1(V, t, u, o):
    prec = CP - V
    s = (u * (1 << (t - V)) + o) % (1 << prec)
    if s == 0: return (CP, 1)
    z = v2(s)
    return (V + z, s >> z)
def stepCoin(c, St):
    V = c[1]
    live = [st for st in St if V <= st[0]]
    stepped = []
    for st in live: stepped += [st, step1(V, st[0], st[1], c[2])]
    out = []
    for y in stepped:
        if y not in out: out.insert(0, y)
    return out
cur = [(0, 1)]
peak = 1
maxmax = 0
for c in tbl:
    cur = stepCoin(c, cur)
    peak = max(peak, len(cur))
    maxmax = max(maxmax, max(t for t, _ in cur))
ck("DP peak states = 352", peak == 352)
ck("DP death certificate: no state reaches 130", maxmax <= 129)
ck("DP final maxT = 129", max(t for t, _ in cur) == 129)
ck("DP final: all states <= 129", all(t <= 129 for t, _ in cur))

# ---- the upper-bound cross-check on random subsets (sound DP agreement) ----
import random
random.seed(40462)
for trial in range(200):
    k = random.randint(1, 20)
    B = sorted(random.sample(range(7, 136), k))
    gg = 1 + sum(F[i] // 720 for i in B)
    ck(f"subset trial {trial} bounded", v2(gg) <= 129)

print(f"VERIFY_F62 BATTERY: ALL {checks} CHECKS PASSED")
