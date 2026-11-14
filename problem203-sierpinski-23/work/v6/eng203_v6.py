"""eng203_v6.py — THE CORE+FIBER ENGINE for Erdos #203 (W66-P203-K).

Torus L = CORE * P (CORE = L/P, P = largest prime factor, exponent 1).
CRT layout: cell (k,l) <-> ((a,b) = (k mod CORE, l mod CORE),
                            (j1,j2) = (k mod P, l mod P)).

Family: core-primes (h | CORE) carve the SAME coset in every fiber;
p-primes (h = P*m, m | CORE) carve (m-coset in core) x (P-line in fibers).
Covered(a,b,j) = core_count(a,b) >= 1 OR (some p-prime q with j on line_q
and (a,b) in its m-coset).

State: core_count (CORE^2 int8) + W per core prime + (w0,w11) per p-prime.
Modes: greedy -> sweep cycles. Exact residual via per-fiber carve.
Kill: residual == 0 -> covering dump.

Usage: eng203_v6.py <palette.json> <L> <mode>
"""
import json, math, os, sys, time, random
import numpy as np

PALF = sys.argv[1]
L = int(sys.argv[2])
MODE = sys.argv[3] if len(sys.argv) > 3 else "greedy"
W_DIR = os.path.dirname(os.path.abspath(__file__))

n = L; fac = {}
d = 2
while d * d <= n:
    while n % d == 0:
        fac[d] = fac.get(d, 0) + 1; n //= d
    d += 1 if d == 2 else 2
if n > 1:
    fac[n] = fac.get(n, 0) + 1
P = max(fac)
CORE = L // P
assert fac[P] == 1 and CORE * P == L
PF = P  # fibers: (Z_P)^2

pal = json.load(open(PALF))
pal = [(int(r[0]), int(r[1]), int(r[2]), int(r[3])) for r in pal]
fam_all = [r for r in pal if L % r[1] == 0]
fam_all.sort(key=lambda r: -1.0 / r[1])
core_fam = [r for r in fam_all if CORE % r[1] == 0]
pfam = [r for r in fam_all if r[1] % P == 0 and CORE % (r[1] // P) == 0]
print(f"L={L}: CORE={CORE}, fiber {P}: family {len(fam_all)} = "
      f"{len(core_fam)} core (b={sum(1.0/r[1] for r in core_fam):.4f}) + "
      f"{len(pfam)} p (b={sum(1.0/r[1] for r in pfam):.4f})", flush=True)

ks = np.arange(CORE, dtype=np.int64)
fiber_j = [(j1, j2) for j1 in range(PF) for j2 in range(PF)]

def coset_row_indices(h, U, V, Wv):
    """rows of {(a,b) in CORE^2: U a + V b = Wv mod h}: (a, l0, stride)."""
    g = int(np.gcd(V, h)); hg = h // g
    rhs = (Wv - U * ks) % h
    ok = (rhs % g == 0) if g > 1 else np.ones(CORE, dtype=bool)
    if hg > 1:
        Vg = (V // g) % hg
        inv = pow(int(Vg), -1, int(hg))
    else:
        inv = 0
    for a in np.nonzero(ok)[0]:
        l0 = ((int(rhs[a]) // g) * inv) % hg if hg > 1 else 0
        yield int(a), l0, hg

def carve_bool(Z, h, U, V, Wv):
    for a, l0, hg in coset_row_indices(h, U, V, Wv):
        Z[a, l0::hg] = False

core_count = np.zeros((CORE, CORE), dtype=np.int8)
cchoice = {}   # q -> W
pchoice = {}   # q -> (w0, w11)
PFAM_BY_Q = {r[0]: r for r in pfam}

def apply_core(i, Wv, delta):
    q, h, U, V = core_fam[i]
    for a, l0, hg in coset_row_indices(h, U, V, Wv):
        core_count[a, l0::hg] += delta

def fiber_carved(j1, j2):
    """Z_j: bool core bitmap of uncovered cells in fiber (j1,j2)."""
    Zj = (core_count == 0)
    for (q, h, U, V) in pfam:
        if q in pchoice and (U * j1 + V * j2) % P == pchoice[q][1]:
            carve_bool(Zj, h // P, U, V, pchoice[q][0])
    return Zj

def exact_residual():
    Z = (core_count == 0)
    total = 0
    for (j1, j2) in fiber_j:
        if not any(q in pchoice for q in PFAM_BY_Q):
            total += int(Z.sum()); continue
        Zj = Z.copy()
        for (q, h, U, V) in pfam:
            if q in pchoice and (U * j1 + V * j2) % P == pchoice[q][1]:
                carve_bool(Zj, h // P, U, V, pchoice[q][0])
        total += int(Zj.sum())
    return total

def dump_state(path, rem):
    json.dump({"L": L, "residual": rem,
               "core": [[q, h, U, V, cchoice.get(q, -1)] for (q, h, U, V) in core_fam],
               "p": [[q, h, U, V] + list(pchoice.get(q, (-1, -1))) for (q, h, U, V) in pfam]},
              open(path, "w"))

def kill_check():
    rem = exact_residual()
    if rem == 0:
        dump_state(W_DIR + f"/covering_closed_v6_L{L}.json", 0)
        print("*** COVERING CLOSED ***", flush=True)
        return True
    return False

# ================= greedy =================
t0 = time.time()
if MODE in ("greedy", "full"):
    # phase 1: core greedy
    for i in range(len(core_fam)):
        q, h, U, V = core_fam[i]
        vals = (U * (ks % h)[:, None] + V * (ks % h)[None, :]) % h
        counts = np.bincount(vals.ravel()[(core_count == 0).ravel()], minlength=h)
        Wv = int(np.argmax(counts))
        if counts[Wv] > 0:
            apply_core(i, Wv, +1)
            cchoice[q] = Wv
    print(f"core greedy: residual {(core_count==0).sum()/(CORE*CORE)*100:.3f}% "
          f"({time.time()-t0:.0f}s)", flush=True)

    # phase 2: p-prime greedy (incremental per-fiber bincounts)
    bcs = {}   # fiber index -> bincount vector over w0 (per m of pending prime)
    def fiber_bc(j1, j2, m, U, V):
        Zj = fiber_carved(j1, j2)
        vm = (U * (ks % m)[:, None] + V * (ks % m)[None, :]) % m
        return np.bincount(vm.ravel()[Zj.ravel()], minlength=m).astype(np.int64)

    for (q, h, U, V) in pfam:
        m = h // P
        bestgain, bestc = 0, None
        for w11 in range(P):
            agg = np.zeros(m, dtype=np.int64)
            for j1 in range(P):
                for j2 in range(P):
                    if (U * j1 + V * j2) % P == w11:
                        agg += fiber_bc(j1, j2, m, U, V)
            w0 = int(np.argmax(agg))
            if agg[w0] > bestgain:
                bestgain = int(agg[w0]); bestc = (w0, w11)
        if bestc is not None:
            pchoice[q] = bestc
        else:
            pchoice[q] = (0, 0)
        if len(pchoice) % 20 == 0:
            print(f"  p-greedy {len(pchoice)}/{len(pfam)}: q={q} gain={bestgain} "
                  f"({time.time()-t0:.0f}s)", flush=True)

    rem = exact_residual()
    print(f"greedy complete: residual {rem} / {L*L} = {rem/(L*L)*100:.4f}% "
          f"({time.time()-t0:.0f}s)", flush=True)
    dump_state(CK := W_DIR + f"/state_v6_L{L}.json", rem)
    if rem == 0:
        kill_check()
        sys.exit(0)

# ================= sweeps =================
if MODE in ("sweep", "full"):
    # core sweep: coordinate-optimal switches on core_count (fiber-blind:
    # gains weighted by fiber-uncovered count via the pi map approximation is
    # deferred; v1 sweep = plain core-level (valid when p-layer thin))
    def core_gain_dist(i):
        q, h, U, V = core_fam[i]
        vals = (U * (ks % h)[:, None] + V * (ks % h)[None, :]) % h
        return np.bincount(vals.ravel()[(core_count == 0).ravel()], minlength=h).astype(np.int64)

    def core_loss(i):
        q, h, U, V = core_fam[i]
        Wold = cchoice.get(q)
        if Wold is None:
            return 0
        d = 0
        for a, l0, hg in coset_row_indices(h, U, V, Wold):
            d += int((core_count[a, l0::hg] == 1).sum())
        return d

    for sweep_round in range(8):
        switches = 0
        for i in range(len(core_fam)):
            q, h, U, V = core_fam[i]
            if q not in cchoice:
                continue
            G = core_gain_dist(i)
            w_best = int(np.argmax(G))
            if G[w_best] == 0:
                continue
            loss = core_loss(i)
            if G[w_best] > loss:
                apply_core(i, cchoice[q], -1)
                apply_core(i, w_best, +1)
                cchoice[q] = w_best
                switches += 1
        print(f"core sweep {sweep_round}: {switches} switches "
              f"({time.time()-t0:.0f}s)", flush=True)
        if switches == 0:
            break

    # p-prime sweep: exact per-fiber gain/loss
    def p_gain(q, w0, w11):
        h, U, V = PFAM_BY_Q[q][1], PFAM_BY_Q[q][2], PFAM_BY_Q[q][3]
        m = h // P
        g = 0
        for j1 in range(P):
            for j2 in range(P):
                if (U * j1 + V * j2) % P == w11:
                    Zj = fiber_carved(j1, j2)
                    vm = (U * (ks % m)[:, None] + V * (ks % m)[None, :]) % m
                    g += int(np.count_nonzero((vm == w0) & Zj))
        return g

    def p_loss(q):
        h, U, V = PFAM_BY_Q[q][1], PFAM_BY_Q[q][2], PFAM_BY_Q[q][3]
        w0, w11 = pchoice[q]
        m = h // P
        d = 0
        for j1 in range(P):
            for j2 in range(P):
                if (U * j1 + V * j2) % P == w11:
                    Zj = (core_count == 0)
                    for (q2, h2, U2, V2) in pfam:
                        if q2 != q and q2 in pchoice and (U2 * j1 + V2 * j2) % P == pchoice[q2][1]:
                            carve_bool(Zj, h2 // P, U2, V2, pchoice[q2][0])
                    vm = (U * (ks % m)[:, None] + V * (ks % m)[None, :]) % m
                    d += int(np.count_nonzero((vm == w0) & Zj))
        return d

    for sweep_round in range(6):
        switches = 0
        for (q, h, U, V) in pfam:
            if q not in pchoice:
                continue
            m = h // P
            # best (w0, w11) by gain, vs current loss
            bestgain, bestc = 0, None
            for w11 in range(P):
                for j1 in range(P):
                    for j2 in range(P):
                        if (U * j1 + V * j2) % P == w11:
                            Zj = fiber_carved(j1, j2)
                            vm = (U * (ks % m)[:, None] + V * (ks % m)[None, :]) % m
                            bc = np.bincount(vm.ravel()[Zj.ravel()], minlength=m)
                            w0 = int(np.argmax(bc))
                            if int(bc[w0]) > 0:
                                cand_gain = p_gain(q, w0, w11)
                                if cand_gain > bestgain:
                                    bestgain = cand_gain; bestc = (w0, w11)
            loss = p_loss(q)
            if bestc is not None and bestgain > loss:
                pchoice[q] = bestc
                switches += 1
        print(f"p sweep {sweep_round}: {switches} switches ({time.time()-t0:.0f}s)", flush=True)
        if kill_check():
            sys.exit(0)
        if switches == 0:
            break

    rem = exact_residual()
    dump_state(W_DIR + f"/state_v6_L{L}_swept.json", rem)
    print(f"final residual {rem} ({rem/(L*L)*100:.4f}%)", flush=True)
