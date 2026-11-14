#!/usr/bin/env python3
"""#708 W63-D1 THE g(4) MASTER VERIFICATION BATTERY (dual-method receipts).

Verifies EXACTLY the claims the Lean g(4) box-master (erdos708_g4_master)
is assembled from, by INDEPENDENT routes:

  (A) REGRESSION: the 8 banked K62 worst values re-derived (DP route).
  (B) THE BOX CONSTRUCTION CLAIM: for ALL 1365 four-sets A ⊆ [2,16] and
      ALL t ∈ [1,40]: an EXACTLY-4 cover exists — verified by the coverExact
      DFS mirror (the Lean `coverExact` def transcribed literally) AND by
      minB(A,t) ≤ 4 via the census DP + window-slack padding count
      (|I \\ B| = M − minB ≥ 5 − 4 ≥ 4 − minB).  Zero failures required.
  (C) THE EXCLUSION WITNESS: minB([2,3,4,5], 24) = 4 EXACT — brute force
      (gmpy2 exact products, full enumeration of ALL subsets of the window
      {25..29}) + the coverFrom ≤3 exclusion mirror + DP cross-check.
  (D) THE CENSUS CHECKPOINT RECOUNT: every row of g4_census2_ckpt.json
      ([2,25] × t ≤ 40, 10626 rows) re-derived with an INDEPENDENT
      factorization route (sympy factorint) — full row-by-row equality.
  (E) THE WIDET CHECKPOINT SPOT-RECOUNT: sample rows of
      g4_widet_ckpt.json ([2,16] × t ≤ 300) re-derived + brute spot checks.
  (F) DP-vs-BRUTE equalities on a random sample of the box + the hard A's.

Output: g4_verify_out.txt (the receipt log).
"""
import sys, json, os, time, random
from itertools import combinations

sys.set_int_max_str_digits(100000)
OUT = "/home/z/waves/w63-d1-p708/problem708-product-divisibility"
sys.path.insert(0, OUT)

import gmpy2
from sympy import factorint
from census2 import window_factors, minB_from_wf

LOG = []


def log(s=""):
    print(s, flush=True)
    LOG.append(s)


def prod(l):
    r = 1
    for x in l:
        r *= x
    return r


# ---------------------------------------------------------------- mirror DP (sympy route, independent)
def minB_sympy(A, t):
    """Independent DP: sympy factorint factorization + exponent-demand DP."""
    M = max(A)
    lo, hi = t + 1, t + M
    D = {}
    for a in A:
        for p, e in factorint(a).items():
            D[p] = D.get(p, 0) + e
    ps = sorted(D)
    k = len(ps)
    start = tuple(D[p] for p in ps)
    idx = {p: i for i, p in enumerate(ps)}
    wf = [factorint(b) for b in range(lo, hi + 1)]
    cur = {start: 0}
    zero = (0,) * k
    for fb in wf:
        v = [0] * k
        for p, c in fb.items():
            i = idx.get(p)
            if i is not None:
                v[i] = min(c, D[p])
        v = tuple(v)
        if not any(v):
            continue
        nxt = dict(cur)
        for s, c in cur.items():
            s2 = tuple(max(0, s[i] - v[i]) for i in range(k))
            if s2 == s:
                continue
            if c + 1 < nxt.get(s2, 10**9):
                nxt[s2] = c + 1
        cur = nxt
    return cur[zero] if zero in cur else len(wf) + 1


# ---------------------------------------------------------------- brute (gmpy2 route)
def minB_brute(A, t, kmax=None):
    M = max(A)
    I = list(range(t + 1, t + M + 1))
    P = gmpy2.mpz(prod(A))
    if kmax is None:
        kmax = len(I)
    for s in range(0, kmax + 1):
        for comb in combinations(I, s):
            x = gmpy2.mpz(1)
            for b in comb:
                x *= b
            if x % P == 0:
                return s, list(comb)
    return kmax + 1, None


# ---------------------------------------------------------------- coverExact mirror (the Lean def)
def coverExact(P, l, k, acc):
    if not l:
        return (acc % P == 0) if k == 0 else False
    if k == 0:
        return coverExact(P, l[1:], 0, acc)
    return coverExact(P, l[1:], k - 1, acc * l[0]) or coverExact(P, l[1:], k, acc)


# ---------------------------------------------------------------- (A) regression
BANKED = [
    ([2, 3], 2),
    ([6, 10, 15], 3),
    ([2, 3, 5], 3),
    ([6, 10, 14, 15], 4),
    ([6, 10, 15, 21], 4),
    ([2, 3, 5, 7], 3),
    ([6, 10, 14, 15, 21], 5),
    ([6, 10, 14, 15, 21, 35], 5),
]

log("=== #708 W63-D1 g(4) MASTER VERIFICATION BATTERY ===")
log("(A) banked K62 regression (census DP, t=1..40):")
okA = True
for A, w in BANKED:
    worst = 0
    for t in range(1, 41):
        worst = max(worst, minB_from_wf(A, window_factors(max(A), t)))
    st = "OK" if worst == w else "MISMATCH"
    if worst != w:
        okA = False
    log(f"   A={A}: worst={worst} (banked {w}) [{st}]")
log(f"(A) {'GREEN' if okA else 'RED'}")

# ---------------------------------------------------------------- (B) box construction
log("")
log("(B) THE BOX CONSTRUCTION [2,16] x t=1..40 (1365 A's x 40 windows):")
log("    (i) coverExact-4 mirror (the Lean def transcribed):")
t0 = time.time()
As_all = [sorted(S) for S in combinations(range(2, 17), 4)]
log(f"    box708 = all 4-subsets of [2,16]: {len(As_all)} sets (C(15,4)=1365)")
fails = 0
worst_nodes = 0
for A in As_all:
    P = prod(A)
    for t in range(1, 41):
        w = list(range(t + 1, t + max(A) + 1))
        if not coverExact(P, w, 4, 1):
            fails += 1
            log(f"    !!! coverExact FAIL: A={A} t={t}")
log(f"    coverExact(exactly-4 cover exists) over the whole box: "
    f"{len(As_all)*40} instances, {fails} failures [{ 'OK' if fails==0 else 'FAIL'}] "
    f"({time.time()-t0:.1f}s)")
log("    (ii) minB ≤ 4 via census DP (independent cross):")
fails2 = 0
for A in As_all:
    for t in range(1, 41):
        if minB_from_wf(A, window_factors(max(A), t)) > 4:
            fails2 += 1
            log(f"    !!! minB>4: A={A} t={t}")
log(f"    minB ≤ 4 over the whole box: {fails2} violations "
    f"[{'OK' if fails2==0 else 'FAIL'}] ({time.time()-t0:.1f}s)")
okB = fails == 0 and fails2 == 0

# ---------------------------------------------------------------- (C) exclusion witness
log("")
log("(C) THE EXCLUSION WITNESS A=[2,3,4,5] at t=24 (window {25..29}):")
s_br, B_br = minB_brute([2, 3, 4, 5], 24)
log(f"    brute (gmpy2, all subsets): minB = {s_br}, witness {B_br} "
    f"(prod(B)={prod(B_br)}, prod(A)=120, 120 | prod(B): {prod(B_br)%120==0})")
s_dp = minB_from_wf([2, 3, 4, 5], window_factors(5, 24))
log(f"    census DP: minB = {s_dp}")
s_sy = minB_sympy([2, 3, 4, 5], 24)
log(f"    sympy-route DP: minB = {s_sy}")
cf3 = coverExact(prod([2, 3, 4, 5]) * 1, list(range(25, 30)), 3, 1)  # coverFrom-3 mirror wrong shape; use brute no-cover below
# coverFrom mirror (≤ k):
def coverFrom_mirror(P, l, k, acc):
    if not l:
        return acc % P == 0
    if k == 0:
        return coverFrom_mirror(P, l[1:], 0, acc)
    return coverFrom_mirror(P, l[1:], k - 1, acc * l[0]) or coverFrom_mirror(P, l[1:], k, acc)
nocov3 = not coverFrom_mirror(120, list(range(25, 30)), 3, 1)
log(f"    coverFrom(≤3) = false (no 3-subset covers): {nocov3}")
# exhaustive enumeration of ALL subsets sizes 0..5 (16+... total 2^5=32):
badcov = []
for s in range(0, 6):
    for comb in combinations(range(25, 30), s):
        if prod(comb) % 120 == 0:
            badcov.append((s, comb))
log(f"    full enumeration: covering subsets = {badcov} "
    f"(min size {badcov[0][0] if badcov else None})")
okC = (s_br == 4 and s_dp == 4 and s_sy == 4 and nocov3
       and badcov and badcov[0][0] == 4)
log(f"(C) {'GREEN' if okC else 'RED'}")

# ---------------------------------------------------------------- (D) census2 recount
log("")
log("(D) CENSUS2 CHECKPOINT RECOUNT (sympy-route DP, all 10626 rows, [2,25] x t≤40):")
t0 = time.time()
d = json.load(open(os.path.join(OUT, "g4_census2_ckpt.json")))
mism = 0
n = 0
for r in d["rows"]:
    A = r["A"]
    worst = 0
    for t in range(1, 41):
        worst = max(worst, minB_sympy(A, t))
    n += 1
    if worst != r["worst"]:
        mism += 1
        if mism <= 5:
            log(f"    !!! row mismatch: A={A} ckpt worst={r['worst']} recount={worst}")
log(f"    rows recounted: {n}, mismatches: {mism} "
    f"[{'OK' if mism==0 else 'FAIL'}] ({time.time()-t0:.1f}s)")
log(f"    ckpt global claim: max={d['max']} at {d['maxA']}; "
    f"recounted global max = {max(minB_sympy(r['A'], t) for r in d['rows'][:1] for t in [1]) if False else 'see rows'}")
# recompute global max from rows
gmax = max(r["worst"] for r in d["rows"])
log(f"    rows global max: {gmax} (forcing-5 count: {len(d['hist5'])})")
okD = mism == 0 and gmax == 4

# ---------------------------------------------------------------- (E) widet spot checks
log("")
log("(E) WIDET CHECKPOINT ([2,16] x t≤300) spot checks:")
w = json.load(open(os.path.join(OUT, "g4_widet_ckpt.json")))
random.seed(63)
sample = random.sample(w["rows"], 25)
mism = 0
for r in sample:
    A = r["A"]
    worst = 0
    for t in range(1, 301):
        worst = max(worst, minB_sympy(A, t))
    if worst != r["worst"]:
        mism += 1
        log(f"    !!! widet row mismatch: A={A} ckpt={r['worst']} recount={worst}")
log(f"    25 random rows recounted at T=300 (sympy route): {mism} mismatches "
    f"[{'OK' if mism==0 else 'FAIL'}]")
# brute spot-check on the widet hardest rows
hard = [r for r in w["rows"] if r["worst"] == 4][:5]
mismb = 0
for r in hard:
    A = r["A"]
    # brute the claimed hard t
    s_br, _ = minB_brute(A, r["t"], kmax=4)
    if s_br != 4:
        mismb += 1
        log(f"    !!! brute says minB({A},{r['t']})={s_br} != 4")
log(f"    5 hardest widet rows brute-checked at their t: {mismb} mismatches "
    f"[{'OK' if mismb==0 else 'FAIL'}]")
okE = mism == 0 and mismb == 0

# ---------------------------------------------------------------- (F) DP-vs-brute sample
log("")
log("(F) DP-vs-BRUTE equalities (random box sample + hard A's):")
random.seed(708)
mism = 0
tests = 0
samp = random.sample(As_all, 40) + [[6, 10, 14, 15], [2, 3, 4, 5], [2, 3, 5, 7]]
for A in samp:
    for t in random.sample(range(1, 41), 6):
        s1 = minB_from_wf(A, window_factors(max(A), t))
        s2, _ = minB_brute(A, t, kmax=min(len(range(t+1, t+max(A)+1)), 5))
        tests += 1
        if s1 != s2:
            mism += 1
            log(f"    !!! DP/brute mismatch A={A} t={t}: {s1} vs {s2}")
log(f"    {tests} pairs, {mism} mismatches [{ 'OK' if mism==0 else 'FAIL'}]")
okF = mism == 0

log("")
verdict = all([okA, okB, okC, okD, okE, okF])
log(f"BATTERY VERDICT: {'GREEN' if verdict else 'RED'} "
    f"(A={okA} B={okB} C={okC} D={okD} E={okE} F={okF})")
log("E708_G4_MASTER_BATTERY_" + ("GREEN" if verdict else "RED"))

with open(os.path.join(OUT, "g4_verify_out.txt"), "w") as f:
    f.write("\n".join(LOG) + "\n")
print("saved g4_verify_out.txt")
