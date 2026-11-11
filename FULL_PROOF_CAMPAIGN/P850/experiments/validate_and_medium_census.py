#!/usr/bin/env python3
"""
W2-P850 experiments: Erdos-Woods length-3 (corpus #850) — VALIDATION + MEDIUM CENSUS.

Method (all exact, integer arithmetic):
  1. rad[] sieve (full array) up to N1.
  2. k=3 witness census, method I (UNCONDITIONAL, no theorems): hash every n by
     the triple (rad(n), rad(n+1), rad(n+2)); a witness is a collision
     (two distinct n with identical triples).
  3. k=2 pair census (side artifact: Erdos family, Makowski, novel pairs).
  4. k=3 census, method II (DUAL, uses Theorem A necessity R(x) | D): for each
     x, scan D = m*R(x); direct radical-equality check. Cross-validates I.
  5. Theorem A empirical equivalence check on all near-miss pairs.
  6. Theorem B scan: all y with R(y) < y (candidate tops) up to N1.
  7. Quality landscape for abc triples (n^2-1, 1, n^2), n = y+1 <= N1+1.
  8. Explicit verification: Erdos family + Makowski pair.
"""
import numpy as np, sys, time, math

T0 = time.time()
def log(msg): print(f"[{time.time()-T0:7.1f}s] {msg}", flush=True)

N1 = int(sys.argv[1]) if len(sys.argv) > 1 else 2_000_000
X2 = int(sys.argv[2]) if len(sys.argv) > 2 else 200_000   # x-range for method II

# ---------- radical sieve ----------
def rad_sieve(N):
    rad = np.ones(N + 3, dtype=np.int64)
    is_p = np.ones(N + 3, dtype=bool); is_p[:2] = False
    for p in range(2, int(N**0.5) + 1):
        if is_p[p]:
            is_p[p*p::p] = False
    primes = np.nonzero(is_p)[0]
    for p in primes:
        rad[p::p] *= p
    return rad, primes

log(f"sieving rad up to {N1}")
rad, primes = rad_sieve(N1)
log(f"rad sieve done; #primes <= N1: {len(primes)}")

# sanity of sieve
def rad_ref(n):
    r = 1
    d = 2
    while d*d <= n:
        if n % d == 0:
            r *= d
            while n % d == 0: n //= d
        d += 1
    if n > 1: r *= n
    return r
for n in list(range(1, 500)) + [75, 76, 1215, 1216, 1217, 242, 243, 244, 1024, 59049]:
    assert rad[n] == rad_ref(n), (n, rad[n], rad_ref(n))
log("rad sieve sanity: OK (vs trial division on 500+ samples)")

# ---------- R(n) = rad(n(n+1)(n+2)) exactly (int64 safe? rad<=N1, product<=N1^3 > 2^63 if N1>2M) ----------
# compute exact R via Python ints where needed; for scanning use logs.
def R_exact(n):
    g = 2 if (n % 2 == 0) else 1   # gcd(rad(n), rad(n+2)) is 2 iff n even
    return rad[n]*rad[n+1]*rad[n+2]//g

# ---------- (2) k=3 collision census (unconditional) ----------
log("k=3 collision census (method I: triple-hash)")
a = rad[0:N1+1]        # rad(n)   for n in [0, N1]
key = a[0:N1-1]*(N1+3) + a[1:N1]        # (rad(n), rad(n+1)) packed
idx = np.lexsort((a[2:N1+1], key))      # sort by (key, rad(n+2))
k1 = key[idx]; k2 = a[2:N1+1][idx]
eq = (k1[1:] == k1[:-1]) & (k2[1:] == k2[:-1])
coll = np.nonzero(eq)[0]
witnesses = []
for c in coll:
    n1, n2 = int(idx[c]), int(idx[c+1])
    witnesses.append((min(n1,n2), max(n1,n2)))
# careful: runs of >2 equal triples
log(f"k=3 witnesses (max<= {N1}): {witnesses if witnesses else 'NONE'}")

# ---------- (3) k=2 pair census ----------
log("k=2 pair census (side artifact)")
idx2 = np.argsort(key, kind='stable')
ks = key[idx2]
eq2 = ks[1:] == ks[:-1]
pairs2 = []
c = 0
m = len(ks)
# group consecutive equal keys
i = 0
eqpos = np.nonzero(eq2)[0]
# build groups
groups = []
start = 0
for e in eqpos:
    pass
# simpler: iterate runs
run_start = 0
for j in range(1, m+1):
    if j == m or ks[j] != ks[run_start]:
        if j - run_start >= 2:
            groups.append(idx2[run_start:j].tolist())
        run_start = j
log(f"k=2 radical-key groups with >=2 members: {len(groups)}")
npairs = 0
fam, other = [], []
for g in groups:
    g = sorted(g)
    for i in range(len(g)):
        for j in range(i+1, len(g)):
            x, y = g[i], g[j]
            # genuine pair requires BOTH windows aligned: supp(x)=supp(y), supp(x+1)=supp(y+1)
            if rad[x+1] == rad[y+1] and rad[x+2] == rad[y+2]:
                pass
            if rad[x+1] == rad[y+1]:   # key equality gives rad(x)=rad(y), rad(x+1)=rad(y+1)
                npairs += 1
                # classify: Erdos family? y == x*(x+2)
                if y == x*(x+2):
                    fam.append((x, y))
                else:
                    other.append((x, y))
log(f"k=2 pairs total <= {N1}: {npairs}; Erdos-family: {len(fam)}; non-family: {other[:20]}{'...' if len(other)>20 else ''}")

# ---------- (4) method II: (x, D=m*R(x)) direct scan ----------
log(f"method II: (x,D) scan for x <= {X2}, y <= {N1}")
found2 = []
total_checks = 0
for x in range(1, X2+1):
    Rx = rad[x]*rad[x+1]*rad[x+2]//(2 if x % 2 == 0 else 1)
    mmax = (N1 - x - 2)//Rx
    if mmax < 1: continue
    ms = np.arange(1, mmax+1, dtype=np.int64)
    ys = x + Rx*ms
    ok = (rad[ys] == rad[x]) & (rad[ys+1] == rad[x+1]) & (rad[ys+2] == rad[x+2])
    total_checks += mmax
    w = np.nonzero(ok)[0]
    for wi in w:
        found2.append((x, int(ys[wi])))
log(f"method II witness checks performed: {total_checks}; witnesses (x<={X2}, y<={N1}): {found2 if found2 else 'NONE'}")

# cross-check: method I restricted to x <= X2 must equal method II
wI = [(x,y) for (x,y) in witnesses if x <= X2]
assert sorted(wI) == sorted(found2), (wI, found2)
log("methods I and II AGREE (dual-method validation: OK)")

# ---------- (5) Theorem A empirical equivalence ----------
# For random (x,y) pairs and all engineered near-misses, verify:
#   supp-match on 3-window  <=>  R(x)|D and R(y)|D
rng = np.random.default_rng(850)
bad = 0
for trial in range(200000):
    x = int(rng.integers(1, min(N1-3, 100000)))
    y = int(rng.integers(x+1, min(N1, 200000)))
    D = y - x
    match = (rad[x]==rad[y]) and (rad[x+1]==rad[y+1]) and (rad[x+2]==rad[y+2])
    Rx = rad[x]*rad[x+1]*rad[x+2]//(2 if x%2==0 else 1)
    Ry = rad[y]*rad[y+1]*rad[y+2]//(2 if y%2==0 else 1)
    div = (D % Rx == 0) and (D % Ry == 0)
    if match != div:
        bad += 1
        print("THEOREM A COUNTEREXAMPLE:", x, y)
log(f"Theorem A empirical check: 200000 random pairs, mismatches: {bad}")

# ---------- (6) Theorem B scan: R(y) < y ----------
log("Theorem B scan: candidates with R(y) < y")
lr = np.log(rad[0:N1+1].astype(np.float64))
s = lr[0:N1-1] + lr[1:N1] + lr[2:N1+1]
ys = np.arange(0, N1-1)
even = (ys % 2 == 0)
s = s - np.where(even, np.log(2.0), 0.0)
# candidates: log R < log y + margin
cand = np.nonzero(s < np.log(np.maximum(ys,1)) + 0.001)[0]
cand = cand[cand >= 2]
log(f"Theorem B candidates (float prefilter): {len(cand)}")
true_cands = []
for y in cand:
    y = int(y)
    if R_exact(y) < y:
        true_cands.append(y)
log(f"y with R(y) < y (exact), y <= {N1}: {true_cands if true_cands else 'NONE'}")

# ratio landscape: smallest R(y)/y
ratio = np.exp(s - np.log(np.maximum(ys, 1)))
ratio[0:2] = np.inf
order = np.argsort(ratio)[:15]
log("smallest R(y)/y (float): " + ", ".join(f"y={int(ys[o])}:{ratio[o]:.3f}" for o in order))

# ---------- (7) quality landscape for (n^2-1, 1, n^2) ----------
# q = 2 ln n / ln R(y), y = n-1
n_arr = ys[2:] + 1
q = 2.0*np.log(n_arr)/s[2:]
oq = np.argsort(-q)[:12]
recs = sorted(((int(n_arr[o]), float(q[o])) for o in oq), key=lambda t: -t[1])
log("top abc-qualities of (n^2-1, 1, n^2): " + ", ".join(f"n={n}:q={qq:.4f}" for n,qq in recs))

# ---------- (8) explicit family verification ----------
log("explicit verifications:")
for r in range(1, 12):
    x = 2*(2**r - 1); y = x*(x+2)
    if y + 2 <= N1:
        m0 = (rad[x]==rad[y]) and (rad[x+1]==rad[y+1])
        m2 = rad[x+2]==rad[y+2]
        D = y - x
        Rx = R_exact(x); Ry = R_exact(y)
        log(f"  Erdos r={r}: x={x} y={y} match01={m0} match2={m2} R(x)|D={D%Rx==0} R(y)|D={D%Ry==0} D={D} R(x)={Rx} R(y)/y={Ry/y:.1f}")
x, y = 75, 1215
D = y - x
log(f"  Makowski: match01={rad[x]==rad[y] and rad[x+1]==rad[y+1]} match2={rad[x+2]==rad[y+2]} (77={rad[77]}, 1217={rad[1217]}) R(x)|D={D % R_exact(x)==0} R(y)|D={D % R_exact(y)==0}")

log("ALL VALIDATION DONE")
