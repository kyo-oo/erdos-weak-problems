# P939 STRIKE B — the local obstruction profile + exact uniform-heuristic expectation,
# on the CORRECTED census (hunt939c engine), r=4 @ 10^15 and r=3 @ 10^12 (calibration).
#
# For every coprime pair (a,b), a,b r-powerful, a+b <= LIMIT, c = a+b:
#   E_unif += d(c)      d = decade-averaged empirical density of r-powerfuls near c
#   local p-adic necessary conditions on c (p = 2,3,5,7):
#       v_p(c) in {0} u [r, inf)   <=>   c % p^r == 0  or  c % p != 0
#   survivors counted; E_loc = E_unif restricted to survivors;
#   conditional expectation E_cond = E_loc / f_rand  (f_rand = P(random int passes)).
# Calibration: r=3 observed = 1 (certified witness 271^3 + 2^3 3^5 73^3 = 919^3).
import time, math, bisect
import numpy as np
from sympy import primerange, factorint

POOL = 2200

def census(r, LIMIT):
    primes = list(primerange(2, int(LIMIT ** (1.0 / r)) + 2))
    vals, psets = [], []
    def gen(idx, val, ps):
        if val > 1:
            vals.append(val); psets.append(tuple(ps))
        for i in range(idx, len(primes)):
            p = primes[i]
            v = val * p ** r
            if v > LIMIT:
                break
            ps.append(i)
            while v <= LIMIT:
                gen(i + 1, v, ps)
                v *= p
            ps.pop()
    gen(0, 1, [])
    order = sorted(range(len(vals)), key=lambda i: vals[i])
    return [vals[i] for i in order], [psets[i] for i in order]

def profile(r, LIMIT, label):
    t0 = time.time()
    vals, psets = census(r, LIMIT)
    N = len(vals); V = np.array(vals, dtype=np.int64)
    K = int(round(math.log10(LIMIT)))
    Ndec = [bisect.bisect_right(vals, 10 ** k) for k in range(0, K + 1)]
    dens = np.zeros(K)
    for k in range(K):
        dens[k] = (Ndec[k + 1] - Ndec[k]) / (10 ** (k + 1) - 10 ** k)
    print(f"\n=== [{label}] r={r}, LIMIT=10^{K}: census N={N} (gen {time.time()-t0:.1f}s) ===")
    print("decade counts N(10^k):", " ".join(f"{k}:{Ndec[k]}" for k in range(1, K + 1)))
    maxp = max(max(s) for s in psets if s) + 1
    div = [[] for _ in range(maxp)]
    for j, ps in enumerate(psets):
        for pid in ps:
            div[pid].append(j)
    dl = [np.array(d, dtype=np.int64) for d in div]

    # census residue coverage (the local supports)
    for m in (16, 81, 625, 2401):
        hist = np.bincount(V % m, minlength=m)
        hit = int((hist > 0).sum())
        phi = m - m // next(q for q in primerange(2, m + 1) if m % q == 0)
        print(f"  census residues mod {m}: {hit} classes hit "
              f"(units+0 possible = {phi + 1}); nonzero-class support ok={hit >= phi}")
    h16 = np.bincount(V % 16, minlength=16)
    print("  census mod-16 histogram:", dict(enumerate(h16.tolist())))

    # the pair loop
    tot = 0; cop = 0; hits = []
    E_unif = 0.0; E_dec = np.zeros(K)
    fc = {'2': 0, '3': 0, '5': 0, '7': 0}
    surv = 0; E_loc = 0.0
    oddodd = 0; oddodd16 = 0
    pool = np.array([], dtype=np.int64)
    for i in range(N):
        a = vals[i]
        if 2 * a > LIMIT:
            break
        cutoff = int(np.searchsorted(V, LIMIT - a, side='right'))
        if cutoff <= i + 1:
            continue
        mask = np.ones(cutoff, dtype=bool); mask[: i + 1] = False
        for pid in psets[i]:
            d = dl[pid]; d = d[d < cutoff]; mask[d] = False
        tot += cutoff - (i + 1)
        idx = np.flatnonzero(mask)
        if len(idx) == 0:
            continue
        cop += len(idx)
        c = a + V[idx]
        dec = np.minimum(np.floor(np.log10(c.astype(np.float64))), K - 1).astype(np.int64)
        dc = dens[dec]
        E_unif += float(dc.sum())
        E_dec += np.bincount(dec, weights=dc, minlength=K)
        if r == 4:
            f2 = (c % 16 == 0) | (c % 2 == 1)
            f3 = (c % 3 != 0) | (c % 81 == 0)
            f5 = (c % 5 != 0) | (c % 625 == 0)
            f7 = (c % 7 != 0) | (c % 2401 == 0)
        else:
            f2 = (c % 8 == 0) | (c % 2 == 1)
            f3 = (c % 3 != 0) | (c % 27 == 0)
            f5 = (c % 5 != 0) | (c % 125 == 0)
            f7 = (c % 7 != 0) | (c % 343 == 0)
        fc['2'] += int(f2.sum()); fc['3'] += int(f3.sum())
        fc['5'] += int(f5.sum()); fc['7'] += int(f7.sum())
        sv = f2 & f3 & f5 & f7
        nsv = int(sv.sum())
        if nsv:
            E_loc += float(dc[sv].sum())
            csv = c[sv]
            if pool.size < POOL:
                pool = np.concatenate([pool, csv])
            elif csv.min() < pool.max():
                pool = np.concatenate([pool, csv])
            if pool.size > 4 * POOL:
                pool = np.partition(pool, POOL)[:POOL]
        surv += nsv
        if a % 2 == 1:
            ev = (c % 2 == 0)
            oddodd += int(ev.sum()); oddodd16 += int(((c % 16) == 0).sum())
        pos = V.searchsorted(c); pos[pos >= N] = 0; ok = V[pos] == c
        if ok.any():
            for j, s in zip(idx[ok], c[ok]):
                hits.append((a, int(vals[j]), int(s)))
    # f_rand
    fr = 1.0
    for p in (2, 3, 5, 7):
        bad = (1 - 1/p) * sum(1 / p ** t for t in range(1, r))
        fr *= (1 - bad)
    E_cond = E_loc / fr
    print(f"  pairs(sum<=LIMIT)={tot:,}  coprime={cop:,}  HITS={len(hits)}  {hits[:3]}")
    print(f"  E_unif (exact, decade densities)          = {E_unif:.4f}")
    top = np.argsort(E_dec)[::-1][:5]
    print("  E_unif by decade (top5):",
          " ".join(f"k={k}:{E_dec[k]:.4f}" for k in top))
    print(f"  filter pass counts: 2:{fc['2']:,} 3:{fc['3']:,} 5:{fc['5']:,} 7:{fc['7']:,}")
    print(f"  ALL-4-filter survivors: {surv:,}  (fraction {surv/max(cop,1):.4f}; "
          f"random-int fraction f_rand = {fr:.4f})")
    print(f"  E_loc (survivors only) = {E_loc:.4f}   E_cond = E_loc/f_rand = {E_cond:.4f}"
          f"   [observed hits = {len(hits)}]")
    print(f"  (odd,odd) coprime pairs: {oddodd:,}; of these 16|(a+b): {oddodd16:,} "
          f"(empirical {oddodd16/max(oddodd,1):.4f} vs 1/8={0.125:.4f})")
    # smallest survivors anatomy
    pool = np.partition(pool, min(POOL - 1, pool.size - 1))[:POOL]
    pool = np.sort(pool)
    print(f"  smallest survivor sums c=a+b (of {surv:,}):")
    shown = 0
    for cval in pool.tolist():
        f = factorint(cval)
        bad = [p for p, e in f.items() if 1 <= e <= r - 1]
        if shown < 8:
            fs = " * ".join(f"{p}^{e}" for p, e in sorted(f.items()))
            print(f"    c={cval}: {fs}  bad-primes(v in 1..{r-1})={bad}")
            shown += 1
    print(f"  [{label}] total {time.time()-t0:.1f}s")
    return dict(N=N, cop=cop, hits=hits, E_unif=E_unif, E_loc=E_loc, E_cond=E_cond,
                surv=surv, fr=fr, tot=tot)

# ---- the small-prime sumset solubility table (local lane open/closed) ----
def sumset_profile(r, LIMIT):
    vals, _ = census(r, min(LIMIT, 10 ** 9))
    V = np.array(vals, dtype=np.int64)
    print(f"\n=== SUMSET SOLUBILITY (r={r}): is the local lane open mod m? ===")
    for m in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 16, 81, 625, 2401, 14641]:
        if r == 3 and m in (16, 81, 625, 2401, 14641):
            m = {16: 8, 81: 27, 625: 125, 2401: 343, 14641: 1331}[m]
        S = set((V % m).tolist())
        pl = [q for q in primerange(2, m + 1) if m % q == 0]
        found = None
        for r1 in S:
            for r2 in S:
                if any(r1 % q == 0 and r2 % q == 0 for q in pl):
                    continue
                if (r1 + r2) % m in S:
                    found = (r1, r2, (r1 + r2) % m); break
            if found: break
        print(f"  m={m:6d}: |S|={len(S):5d}  local triple exists: "
              f"{'YES ' + str(found) if found else 'NO  (OBSTRUCTION!)'}")

res4 = profile(4, 10 ** 15, "r4@1e15")
res3 = profile(3, 10 ** 12, "r3@1e12")
sumset_profile(4, 10 ** 15)
print("\nCALIBRATION VERDICT:")
print(f"  r=3: E_unif={res3['E_unif']:.4f}  E_cond={res3['E_cond']:.4f}  observed={len(res3['hits'])}")
print(f"  r=4: E_unif={res4['E_unif']:.4f}  E_cond={res4['E_cond']:.4f}  observed={len(res4['hits'])}")
print(f"  r=4 Poisson P(0 hits | E_cond): {math.exp(-res4['E_cond']):.4f}")
print(f"  r=3 Poisson P(>=1 hit | E_cond): {1 - math.exp(-res3['E_cond']):.4f}")
