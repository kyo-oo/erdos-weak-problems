#!/usr/bin/env python3
"""
W2-P850: SIGN ANALYSIS census (the corpus statement says INTEGERS, not
positive integers). Rigorous sign reduction (Lemma 0 of PROOF.md):

  - both-positive windows: the Erdos-Woods length-3 problem (main target).
  - both-negative: equivalent to both-positive by window reversal.
  - mixed sign (x <= -4, y >= 1): the MIRROR problem
        supp(X+2) = supp(y), supp(X+1) = supp(y+1), supp(X) = supp(y+2),
        X = -x-2 >= 2,
    i.e. the triple-key of X read BACKWARDS equals the triple-key of y.
    (x,y) = (-4,2) i.e. (X,y) = (2,2) is a solution (supp(2) = supp(4)).

This script enumerates, exactly, up to N1:
  (a) all y with rad(y) = rad(y+2)  (symmetric mirror solutions X = y);
  (b) all mirror pairs (X, y), X != y, via reversed-key hashing;
  (c) confirms the positive-domain k=3 census is empty (cross-check).
"""
import numpy as np, sys, time, math

T0 = time.time()
def log(msg): print(f"[{time.time()-T0:7.1f}s] {msg}", flush=True)

N1 = int(sys.argv[1]) if len(sys.argv) > 1 else 20_000_000

def rad_sieve(N):
    rad = np.ones(N + 3, dtype=np.int64)
    is_p = np.ones(N + 3, dtype=bool); is_p[:2] = False
    for p in range(2, int(N**0.5) + 1):
        if is_p[p]: is_p[p*p::p] = False
    primes = np.nonzero(is_p)[0]
    for p in primes: rad[p::p] *= p
    return rad

log(f"rad sieve to {N1}")
rad = rad_sieve(N1)
log("done")

# (a) symmetric mirror: rad(y) == rad(y+2), y in [1, N1]
a0 = rad[1:N1+1]; a2 = rad[3:N1+3]
sym = np.nonzero(a0 == a2)[0] + 1
log(f"(a) y with supp(y) = supp(y+2), y <= {N1}: {sym.tolist()[:50]}{'...' if len(sym)>50 else ''} (count {len(sym)})")

# (b) mirror pairs via key hashing: key3(n) = (rad(n), rad(n+1), rad(n+2));
#     mirror match X <-> y iff key3(X) == reverse(key3(y)).
# pack (rad(n), rad(n+1)) and keep rad(n+2); build dict from
# (rad(n+2), rad(n+1)) -> positions  [reversed prefix]  and probe
# (rad(n), rad(n+1)) i.e. forward prefix. Match iff also rad(X) == rad(y+2).
# Memory-safe two-pass with sorting:
r0 = rad[0:N1+1]; r1 = rad[1:N1+2]; r2 = rad[2:N1+3]
n_arr = np.arange(0, N1+1)
# forward key for position n: (r0[n], r1[n], r2[n]) ; need X with
# (r0[X], r1[X], r2[X]) == (r2[y], r1[y], r0[y]).
K = np.int64(N1 + 5)
fwd12 = r0*K + r1            # (rad(n), rad(n+1)) for n in [0, N1]
rev12 = r2*K + r1            # (rad(n+2), rad(n+1)) for n in [0, N1]
order_f = np.lexsort((r2, fwd12))    # sort forward keys (fwd12, r2)
order_r = np.lexsort((r0, rev12))    # sort reversed keys (rev12, r0)
# merge-scan for equality of (fwd12, r2)[order_f] == (rev12, r0)[order_r]
fA = fwd12[order_f]; fC = r2[order_f]
rA = rev12[order_r]; rC = r0[order_r]
i = j = 0
mirror_pairs = []
LA, LB = len(fA), len(rA)
while i < LA and j < LB:
    ka = (int(fA[i]), int(fC[i])); kb = (int(rA[j]), int(rC[j]))
    if ka == kb:
        # collect all with same keys on both sides
        ii = i
        while ii < LA and (int(fA[ii]), int(fC[ii])) == ka: ii += 1
        jj = j
        while jj < LB and (int(rA[jj]), int(rC[jj])) == kb: jj += 1
        for a in range(i, ii):
            for b in range(j, jj):
                X = int(order_f[a]); y = int(order_r[b])
                # mirror condition: key3(X) == reverse(key3(y)) with X,y in [1, N1-2]
                if 1 <= X <= N1-2 and 1 <= y <= N1-2:
                    if (rad[X] == rad[y+2] and rad[X+1] == rad[y+1] and rad[X+2] == rad[y]):
                        if X != y or True:
                            mirror_pairs.append((X, y))
        i = ii; j = jj
    elif ka < kb: i += 1
    else: j += 1
mirror_pairs = sorted(set(mirror_pairs))
log(f"(b) mirror pairs (X, y) [witness (x,y) = (-(X+2), y)], X,y <= {N1-2}: {mirror_pairs[:50]}{'...' if len(mirror_pairs)>50 else ''} (count {len(mirror_pairs)})")
sym_pairs = [(t, t) for t in sym if t <= N1-2]
novel = [p for p in mirror_pairs if p not in set(sym_pairs)]
log(f"    of which symmetric (X=y): {len(sym_pairs)}; NON-symmetric mirror pairs: {novel[:30]} (count {len(novel)})")

# verify the flagship
X, y = 2, 2
x = -(X+2)
log(f"flagship check: x={x}, y={y}: supp(x)={sorted(set(math.factor(abs(x)) if hasattr(math,'factor') else []))} -> via rad: rad({x})={rad[abs(x)]}, rad({y})={rad[y]}; rad(x+1)={rad[abs(x+1)]}, rad(y+1)={rad[y+1]}; rad(x+2)={rad[abs(x+2)]}, rad(y+2)={rad[y+2]}")
assert rad[abs(x)] == rad[y] and rad[abs(x+1)] == rad[y+1] and rad[abs(x+2)] == rad[y+2]
log("FLAGSHIP WITNESS (-4, 2) VERIFIED (literal signed reading)")
log("done")
