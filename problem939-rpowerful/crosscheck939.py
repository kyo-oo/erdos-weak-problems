#!/usr/bin/env python3
# crosscheck939.py — W63-B1: SECOND-METHOD RE-DERIVATION of the box zero-claims.
#
# The verification law: every computational claim re-derived by a second method.
# The box lanes (EO same-bucket / OO complementary-bucket) are one traversal;
# these are the INDEPENDENT traversals of the same finite sets:
#   M3  pure-Python brute force, NO buckets, NO numpy: every pair (a,b) in
#       L x L, a < b, a+b <= LIMIT, sum in Lset (covers all parities incl.
#       the EE pairs the lanes rightly exclude). At 1e13.
#   M4  the (e,c)-traversal of the EO stratum: for EVERY even 4-powerful e,
#       EVERY odd c in the O-list above e, o = c - e tested against the
#       O-list (no mod-16 bucket machinery — the congruence is automatic
#       since 16 | e). And the (c,a)-traversal of the OO stratum: for EVERY
#       even 4-powerful c, every odd a < c - a with b = c - a tested against
#       the O-list. At 1e13, 1e15, 1e16.
# Both must reproduce the lane receipts' hit sets EXACTLY (elementwise),
# re-deriving: ZERO coprime triples (all hits gcd > 1).
import os, sys, time, gzip, json
import numpy as np
import math

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import hunt939d as H

REPO = H.REPO
OUTP = os.path.join(REPO, 'crosscheck939_output.txt')

def load_lane_hits(tag):
    """The first-method receipts: (EO hits, OO hits, CON pairs)."""
    eo = []
    with gzip.open(os.path.join(REPO, f'ck939_box{tag}_eo.json.gz')) as fh:
        eo = [tuple(x) for x in json.load(fh)['hits']]
    with gzip.open(os.path.join(REPO, f'ck939_box{tag}_oo.json.gz')) as fh:
        oo = [tuple(x) for x in json.load(fh)['hits']]
    con = json.load(open(os.path.join(REPO, f'ck939_box{tag}_con.json')))['pairs']
    return eo, oo, con

def m3_brute(LIMIT):
    """M3: pure-Python brute force over all pairs (a,b), a<b, a+b<=LIMIT.
    Returns ALL sum-hits (any parity)."""
    L = H.gen4(LIMIT); Lset = set(L)
    hits = []
    for i, a in enumerate(L):
        if 2 * a > LIMIT: break
        for b in L[i + 1:]:
            if a + b > LIMIT: break
            if (a + b) in Lset:
                hits.append((a, b, a + b))
    return hits

def m4_ec(LIMIT):
    """M4: (e,c)-traversal (EO stratum) + (c,a)-traversal (OO stratum).
    Returns (eo_hits, oo_hits, con_pairs) in the lane receipts' triple form."""
    L = H.gen4(LIMIT); Lset = set(L)
    E = [x for x in L if not (x & 1)]
    O = [x for x in L if (x & 1)]
    O_np = np.array(O, dtype=np.uint64); nO = len(O)
    eo = []; oo = []
    # (e, c): e in E, c in O above e, o = c - e in O  [every EO triple once]
    for e in E:
        lo = int(np.searchsorted(O_np, np.uint64(e), side='right'))
        if lo >= nO: continue
        cands = O_np[lo:]
        diffs = cands - np.uint64(e)
        pos = np.searchsorted(O_np, diffs)
        np.clip(pos, 0, nO - 1, out=pos)
        hit = O_np[pos] == diffs
        for k in np.nonzero(hit)[0]:
            eo.append((e, int(diffs[k]), int(cands[k])))
    # (c, a): c in E, a in O with a < c - a, b = c - a in O  [every OO triple once]
    for c in E:
        half = c >> 1
        hi = int(np.searchsorted(O_np, np.uint64(half), side='left'))
        if hi <= 0: continue
        a_c = O_np[:hi]
        b_c = np.uint64(c) - a_c
        pos = np.searchsorted(O_np, b_c)
        np.clip(pos, 0, nO - 1, out=pos)
        hit = O_np[pos] == b_c
        for k in np.nonzero(hit)[0]:
            oo.append((int(a_c[k]), int(b_c[k]), c))
    con = sum(1 for x in L if x + 1 <= LIMIT and (x + 1) in Lset)
    return eo, oo, con

def check(exp):
    LIMIT = 10 ** exp
    t0 = time.time()
    eo_r, oo_r, con_r = load_lane_hits(str(exp))
    eo4, oo4, con4 = m4_ec(LIMIT)
    ok_eo = sorted(eo4) == sorted(eo_r)
    ok_oo = sorted(oo4) == sorted(oo_r)
    ok_con = (con4 == con_r)
    allcop = all(math.gcd(a, b) > 1 for a, b, c in eo4 + oo4)
    ncop4 = sum(1 for a, b, c in eo4 + oo4 if math.gcd(a, b) == 1)
    print(f'  [B{exp}] M4 (e,c)/(c,a) traversals: EO {len(eo4)} hits (receipt {len(eo_r)}) '
          f'-> exact match {ok_eo}; OO {len(oo4)} hits (receipt {len(oo_r)}) -> exact '
          f'match {ok_oo}; CON {con4} vs {con_r} -> {ok_con}; '
          f'coprime hits {ncop4}; {time.time()-t0:.1f}s', flush=True)
    return ok_eo and ok_oo and ok_con and ncop4 == 0

def check_m3(exp):
    LIMIT = 10 ** exp
    t0 = time.time()
    eo_r, oo_r, con_r = load_lane_hits(str(exp))
    ref = eo_r + oo_r + [(1, x, x + 1) for x in range(0)]  # CON pairs = 0
    b3 = m3_brute(LIMIT)
    b3_mix = [t for t in b3 if not (t[0] & 1 == 0 and t[1] & 1 == 0)]
    ok = sorted(b3_mix) == sorted(ref)
    ncop = sum(1 for t in b3 if math.gcd(t[0], t[1]) == 1)
    ee = sum(1 for t in b3 if (t[0] & 1 == 0 and t[1] & 1 == 0))
    print(f'  [B{exp}] M3 pure-Python brute: {len(b3)} sum-hits total ({ee} EE — '
          f'excluded by coprimality; {len(b3_mix)} mixed/odd vs receipt {len(ref)}) '
          f'-> exact match {ok}; coprime hits among ALL pairs: {ncop}; '
          f'{time.time()-t0:.1f}s', flush=True)
    return ok and ncop == 0

def main():
    print('=== crosscheck939 — SECOND-METHOD BOX RE-DERIVATIONS (W63-B1) ===', flush=True)
    ok = True
    for exp in [int(x) for x in sys.argv[1:]] or []:
        ok &= check(exp)
        if os.environ.get('M3') == '1' and exp <= 13:
            ok &= check_m3(exp)
    print(f'=== crosscheck939 VERDICT: {"ALL GREEN" if ok else "MISMATCH"} ===', flush=True)

if __name__ == '__main__':
    main()
