#!/usr/bin/env python3
# W69-F: THE WITNESS FORGE BATTERY — ErSz61 extremal sets + Klein + label census
# Consolidated from the W69-F engine lane (scratch1 base engine, exact integer arithmetic).
# Exit nonzero on any failure. Prints E107_ENGINE_W69F_GREEN on full pass.
import itertools, json, os, random, sys, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from engine_base import (det3, E_build, max_cup_cap_len, cup_cap_end_labels,
                         has_kcup_lcap)

def convex4_product(q):
    """4 gp points are in convex position (ANY order) iff the product of the four
    triple-orientation signs is positive (even number of negative signs).
    Order-independent — unlike the all-same-sign cyclic test."""
    s1 = det3(q[0], q[1], q[2]); s2 = det3(q[0], q[1], q[3])
    s3 = det3(q[0], q[2], q[3]); s4 = det3(q[1], q[2], q[3])
    if 0 in (s1, s2, s3, s4):
        return False
    return s1 * s2 * s3 * s4 > 0

FAIL = 0
def check(name, cond):
    global FAIL
    print(f"[{'PASS' if cond else 'FAIL'}] {name}")
    if not cond:
        FAIL += 1

t0 = time.time()

# ---- 1. The E(k,l) extremal table: |E| = C(k+l-4, k-2), maxcup <= k-1, maxcap <= l-1, no k-cup/l-cap ----
from math import comb
table_ok = True
for k in range(3, 6):
    for l in range(3, 6):
        pts = E_build(k, l)
        n_want = comb(k + l - 4, k - 2)
        mc, mcap = max_cup_cap_len(pts)
        gp = all(det3(a, b, c) != 0 for a, b, c in itertools.combinations(pts, 3))
        nokc = has_kcup_lcap(pts, k, l) is None
        table_ok = table_ok and len(pts) == n_want and mc <= k - 1 and mcap <= l - 1 and gp and nokc
        print(f"  E({k},{l}): |E|={len(pts)} (want {n_want}), maxcup={mc} (<={k-1}), maxcap={mcap} (<={l-1}), gp={gp}, no {k}-cup/{l}-cap={nokc}")
check("E(k,l) extremal table k,l in 3..5: exact sizes, cup/cap bounds, general position, extremality", table_ok)

# ---- 2. The ErSz61 witness family (the doubter's certified construction): no convex n-gon ----
cert_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'doubter', 'out', 'construction_certificates.json')
if os.path.exists(cert_path):
    d = json.load(open(cert_path))
    certs = {c['n']: c for c in d['certificates']}
    fam_ok = all(
        certs[n]['all_pass'] and certs[n]['num_points'] == 2 ** (n - 2)
        and certs[n]['convex_n_gons_found'] == 0
        for n in (3, 4, 5, 6)
    )
    check("ErSz61 witnesses n=3..6: |S|=2^(n-2), gp, zero convex n-gons (exhaustive C(2^{n-2},n) subsets)", fam_ok)
else:
    print("[SKIP] doubter certificates not present on this branch")

# ---- 3. THE LABEL CENSUS FINDING (documented): the naive end-label map is NOT injective ----
# E(4,4): 1 collision among 6 points; E(5,5): 10 among 20; random gp sets: 135/300 collide.
# KILLER-LANE INTEL: the classic ES35 injectivity must be formalized via the ORDERED
# slope-comparison argument, NOT plain injectivity of the label map.
e44 = E_build(4, 4)
lab44 = cup_cap_end_labels(e44)
coll44 = len(lab44) - len(set(lab44.values()))
e55 = E_build(5, 5)
lab55 = cup_cap_end_labels(e55)
coll55 = len(lab55) - len(set(lab55.values()))
print(f"  E(4,4) label collisions: {coll44}; E(5,5): {coll55}")
check("label census reproduces the documented collision counts (naive injectivity FALSE)", coll44 == 1 and coll55 == 10)

# ---- 4. Klein: every 5-point gp set contains a convex 4-subset (randomized census) ----
rng = random.Random(5)
conv5 = 0
gp5 = 0
trials = 20000
for _ in range(trials):
    pts = [(rng.randrange(0, 60), rng.randrange(0, 60)) for _ in range(5)]
    if len(set(pts)) < 5:
        continue
    if not all(det3(a, b, c) != 0 for a, b, c in itertools.combinations(pts, 3)):
        continue  # not gp
    gp5 += 1
    conv5 += any(convex4_product(q) for q in itertools.combinations(pts, 4))
check(f"Klein census: {conv5}/{gp5} gp 5-sets contain a convex 4-subset (expect ALL)", conv5 == gp5 and gp5 > 15000)

print(f"elapsed {time.time()-t0:.1f}s")
if FAIL:
    print(f"E107_ENGINE_W69F: {FAIL} FAILURES")
    sys.exit(1)
print("E107_ENGINE_W69F_GREEN")
