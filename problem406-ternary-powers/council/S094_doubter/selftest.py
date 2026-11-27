"""Self-test of the S094 doubter library against exhaustive brute force."""
import sys, json
sys.path.insert(0, "/home/z/erdos-weak-problems/problem406-ternary-powers/council/S094_doubter")
from lib import *

ok = True
def check(name, cond):
    global ok
    print(("PASS " if cond else "FAIL ") + name, flush=True)
    ok = ok and cond

# ---- 1. TargetMITM (0-constrained v2*0) vs brute, M=0..14 ----
for M in range(0, 15):
    b, bw = brute_v2star0(M)
    tm = TargetMITM([0], list(range(1, M + 1)))
    v, w, info = tm.solve()
    good = (v == b)
    if w is not None:
        good = good and (v2(sum(3**i for i in w)) == v) and 0 in w and max(w) <= M
    check(f"v2*0({M}): mitm={v} brute={b} wit={w}", good)

# ---- 2. FullMITM vs brute v2*, M=0..14 ----
for M in range(0, 15):
    b, bw = brute_v2star(M)
    fm = FullMITM(list(range(0, M + 1)))
    v, w, info = fm.solve()
    good = (v == b)
    if w is not None:
        good = good and (v2(sum(3**i for i in w)) == v) and (len(w) >= 1)
    check(f"v2*({M}): full={v} brute={b} wit={w}", good)

# ---- 3. shift-invariance identity v2*0 == v2* on M=0..18 ----
for M in range(0, 19):
    b, _ = brute_v2star(M)
    b0, _ = brute_v2star0(M)
    check(f"identity v2*0({M})==v2*({M}): {b0}=={b}", b == b0)

# ---- 4. g(m) constrained-fresh vs brute, m=0..12 ----
for m in range(0, 13):
    bg = brute_g(m) if m >= 1 else (0, [0])
    tm = TargetMITM([0, m], list(range(1, m))) if m >= 2 else (TargetMITM([0, m], []) if m == 1 else None)
    if m == 0:
        v, w = 0, [0]
    elif m == 1:
        v, w, _ = tm.solve()
    else:
        v, w, _ = tm.solve()
    check(f"g({m}): mitm={v} brute={bg[0]} wit={w}", v == bg[0] and (w is None or v2(sum(3**i for i in w)) == v))

# ---- 5. ComboMITM exactly-k vs brute, k=2..6, M=k..12 ----
pows = pow3_mod64_list(40)
for k in range(2, 7):
    for M in range(k, 13):
        bk, bwk = brute_maxk(M, k)
        cm = ComboMITM(k, M, pows)
        v, w, infos = cm.solve_k()
        good = v == bk and (w is None or (len(w) == k and 0 in w and v2(sum(3**i for i in w)) == v))
        check(f"max{k}({M}): mitm={v} brute={bk}", good)

# ---- 6. Method A sweep vs brute v2*, M=0..16, t<=17 ----
flags = methodA_sweep(17, 16, verbose=False)
for M in range(0, 17):
    b, _ = brute_v2star(M)
    vA = max([t for t in range(1, 18) if flags[t][M]] + [0])
    check(f"methodA v2*({M})={vA} brute={b}", vA == b)

# ---- 7. campaign table cross-check on the overlap M<=21 (exhaustive) ----
camp = json.load(open("/home/z/erdos-weak-problems/problem406-ternary-powers/caplaw/v2star_table.json"))
tbl = {int(k): v for k, v in camp["v2star"].items()}
for M in range(0, 22):
    b, _ = brute_v2star(M)
    check(f"campaign v2*({M})=={tbl[M]} vs brute {b}", tbl[M] == b)

print("\nSELFTEST", "GREEN" if ok else "RED", flush=True)
sys.exit(0 if ok else 1)
