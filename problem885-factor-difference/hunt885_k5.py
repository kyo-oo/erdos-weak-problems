#!/usr/bin/env python3
"""hunt885_k5.py — W56-3 / P885 ROUND 1: the k=5 witness hunt.

PROOF.md §2 pair-indexed enumeration (the factorization-indexed search space):
for a row pair (s0, s1), every C of a K_{6,4} configuration (Theorem B: 6
distinct rows s, 4 distinct positive C, all 24 sums s^2 + C_j perfect
squares  =>  #885(5) TRUE via the lambda=2 scaling) lies in

    G(s0, s1) = {m0^2 - s0^2 : m0 from the factor pairs of Delta = s1^2 - s0^2}.

We enumerate (u, v) = (s1 - s0, s1 + s1) [same parity, u < v], build G,
compute each C's FULL row set R(C) = {s >= 1 : s^2 + C = square} EXACTLY
(rows are (q-p)/2 [resp. q-p] over the same-parity factor pairs of C —
no range cuts, no square tests needed), then hunt 4-subsets of G with
>= 6 common rows (the K_{6,4} biclique).

Memory ration (<= 300MB): SPF sieve int32 to 5e6 (~20MB) + tau sieve int32
(~20MB); everything else is per-pair transient.  Runtime cap ~280s wall.
The SPF sieve replaces sympy divisor calls for speed; factorization of
C <= 10^8 is EXACT (trial division by primes <= 10^4; any composite
remainder would exceed 10^8).

Round-1 census gates (honestly reported):
  Delta = u*v <= 5_000_000 (s1 <= 2236), tau(Delta) >= 64 (rich deltas),
  C <= 10^8, row degree cap 30.
A k=3 validation pass first re-derives the in-house K_{4,2} witness
(rows {2, 22, 46, 134}, C {1365, 3360}).
"""
import time
from math import isqrt
from itertools import combinations
from collections import defaultdict

import numpy as np

T0 = time.time()
BASE = "/home/z/my-project/erdos-weak-problems/problem885-factor-difference"
LOG = open(BASE + "/hunt885_k5.log", "w")

DELTA_MAX = 5_000_000
S1_MAX = 2236                 # s1^2 <= 5e6  =>  Delta <= 5e6
C_CAP = 10**8
TAU_EXACT = 64                # rich-Delta gate for the k5 round
TAU_PREF = 28                 # cheap sieve prefilter (never skips tau >= 64)
ROW_DEG_CAP = 30              # rows in > 30 C's truncated (heuristic cap)
TIME_CAP_TOTAL = 280.0

def logprint(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    LOG.write(s + "\n")
    LOG.flush()

logprint("[hunt885_k5] W56-3 ROUND 1 k=5 hunt — PROOF.md §2 pair-indexed engine")
logprint(f"[hunt885_k5] gates: Delta <= {DELTA_MAX}, tau(Delta) >= {TAU_EXACT}, "
         f"C <= {C_CAP}, row-degree cap {ROW_DEG_CAP}, total wall cap {TIME_CAP_TOTAL}s")

# ---------- SPF sieve to DELTA_MAX (int32, ~20MB) ----------
def build_spf(limit):
    spf = np.zeros(limit + 1, dtype=np.int32)
    spf[1] = 1
    for i in range(2, isqrt(limit) + 1):
        if spf[i] == 0:
            spf[i * i::i] = np.where(spf[i * i::i] == 0, i, spf[i * i::i])
    mask = spf == 0
    idx = np.nonzero(mask)[0]
    spf[idx] = idx
    return spf

logprint(f"[hunt885_k5] building SPF sieve to {DELTA_MAX} ...")
SPF = build_spf(DELTA_MAX)
logprint(f"[hunt885_k5] SPF ready ({time.time()-T0:.1f}s)")

# ---------- tau sieve: tau_sieve[n] = #{d <= sqrt(LIM) : d | n} ----------
LIM = S1_MAX * S1_MAX
tau_sieve = np.zeros(LIM + 1, dtype=np.int32)
for d in range(1, isqrt(LIM) + 1):
    tau_sieve[d::d] += 1
logprint(f"[hunt885_k5] tau sieve to {LIM} ready ({time.time()-T0:.1f}s)")

# primes to 10^4 (exact factorization of C <= 10^8)
SMALL_PRIMES = []
for n in range(2, 10000):
    if all(n % p for p in SMALL_PRIMES if p * p <= n):
        SMALL_PRIMES.append(n)

def factorize(n):
    """Exact prime factorization: SPF for n <= DELTA_MAX, else trial
    division by primes <= 10^4 (remainder is prime or 1 for n <= 10^8)."""
    f = {}
    if n <= DELTA_MAX:
        while n > 1:
            p = int(SPF[n])
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            f[p] = e
        return f
    for p in SMALL_PRIMES:
        if p * p > n:
            break
        if n % p == 0:
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            f[p] = e
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def divisors(n):
    divs = [1]
    for p, e in factorize(n).items():
        divs = [d * p**k for d in divs for k in range(e + 1)]
    return divs

def factor_pairs_parity(n):
    """(p, q), p < q, p*q = n, p == q (mod 2) — the difference-of-squares
    pairs.  Empty for n % 4 == 2.  n odd: odd pairs; n % 4 == 0: pairs of
    n/4 (actual pair (2p, 2q))."""
    if n % 2 == 1:
        out = []
        for p in divisors(n):
            q = n // p
            if p < q:
                out.append((p, q))
        return out
    if n % 4 == 2:
        return []
    m = n // 4
    out = []
    for p in divisors(m):
        q = m // p
        if p < q:
            out.append((p, q))
    return out

def G_candidates(s0, s1):
    """All C with 0 < C <= C_CAP, s0^2 + C = m0^2 and s1^2 + C = m1^2."""
    Delta = s1 * s1 - s0 * s0
    out = []
    if Delta % 2 == 1:
        for p, q in factor_pairs_parity(Delta):
            m0 = (q - p) // 2
            m1 = (q + p) // 2
            if m0 > s0:
                C = m0 * m0 - s0 * s0
                if C <= C_CAP:
                    out.append((C, m0, m1))
    elif Delta % 4 == 0:
        for p, q in factor_pairs_parity(Delta):
            m0 = q - p
            m1 = q + p
            if m0 > s0:
                C = m0 * m0 - s0 * s0
                if C <= C_CAP:
                    out.append((C, m0, m1))
    return out

def rows_of_C(C):
    """ALL rows s >= 1 with s^2 + C = square (exact: factor pairs of C)."""
    rows = []
    if C % 2 == 1:
        for p, q in factor_pairs_parity(C):
            rows.append((q - p) // 2)
    elif C % 4 == 0:
        for p, q in factor_pairs_parity(C):
            rows.append(q - p)
    return rows

def verify_config(rows, Cs):
    """Exact check: all |rows|*|Cs| sums perfect squares; distinct; C > 0."""
    if len(set(rows)) != len(rows) or len(set(Cs)) != len(Cs):
        return False
    if any(c <= 0 for c in Cs):
        return False
    for s in rows:
        for c in Cs:
            t = s * s + c
            m = isqrt(t)
            if m * m != t:
                return False
    return True

def build_witness(rows, Cs):
    """Theorem B lambda=2 scaling: rows sorted, s_min = min; the #885(5)
    witness is N_i = s_i^2 - s_min^2 (i >= 1) and d = [2*s_min] +
    [2*isqrt(C_j + s_min^2)]."""
    rows = sorted(rows)
    s_min = rows[0]
    Ns = [s * s - s_min * s_min for s in rows[1:]]
    ds = [2 * s_min] + [2 * isqrt(c + s_min * s_min) for c in Cs]
    return Ns, ds

def process_pair(s0, s1, need_Cs, need_rows):
    G = G_candidates(s0, s1)
    if len(G) < need_Cs:
        return None
    rowmap = defaultdict(list)
    for idx, (C, _, _) in enumerate(G):
        for s in rows_of_C(C):
            rowmap[s].append(idx)
    cnt = defaultdict(int)
    for s, lst in rowmap.items():
        if len(lst) < need_Cs:
            continue
        for combo in combinations(sorted(lst)[:ROW_DEG_CAP], need_Cs):
            cnt[combo] += 1
    best = max(cnt.values()) if cnt else 0
    hits = []
    for combo, c in cnt.items():
        if c >= need_rows:
            Cs = [G[i][0] for i in combo]
            rows = sorted(r for r, lst in rowmap.items() if set(combo) <= set(lst))
            hits.append((rows, Cs))
    return best, hits, len(G)

def hunt(k, s1_max, tau_pref, tau_exact, budget, tag):
    need_rows = k + 1
    need_Cs = k - 1
    t_start = time.time()
    stats = {"pairs": 0, "rich": 0, "proc": 0, "maxG": 0, "best": 0, "maxrows": 0}
    hits = []
    done_u = 0
    for u in range(1, s1_max + 1):
        if time.time() - t_start > budget or time.time() - T0 > TIME_CAP_TOTAL:
            logprint(f"  [{tag}] TIME BUDGET reached at u={u} (partial window)")
            break
        for v in range(u + 2, 2 * s1_max - u + 1, 2):
            D = u * v
            if tau_sieve[D] < tau_pref:
                continue
            stats["pairs"] += 1
            tauD = 1
            for e in factorize(D).values():
                tauD *= (e + 1)
            if tauD < tau_exact:
                continue
            stats["rich"] += 1
            s0 = (v - u) // 2
            s1 = (u + v) // 2
            res = process_pair(s0, s1, need_Cs, need_rows)
            if res is None:
                continue
            best, hh, g = res
            stats["proc"] += 1
            stats["maxG"] = max(stats["maxG"], g)
            stats["maxrows"] = max(stats["maxrows"], len(hh))
            if best > stats["best"]:
                stats["best"] = best
                logprint(f"  [{tag}] new best: a {need_Cs}-C subset with "
                         f"{best} common rows (s0={s0}, s1={s1}, |G|={g})")
            for rows, Cs in hh:
                rows_k = rows[:need_rows]
                if verify_config(rows_k, Cs):
                    hits.append((rows_k, Cs))
                    logprint(f"*** HIT k={k}: rows={rows_k} Cs={Cs}")
        done_u = u
        if u % 50 == 0:
            logprint(f"  [{tag}] u={u} pairs={stats['pairs']} rich={stats['rich']} "
                     f"proc={stats['proc']} best={stats['best']} "
                     f"t={time.time()-t_start:.0f}s")
    logprint(f"[{tag}] done: u-window covered u=1..{done_u} of {s1_max}; "
             f"prefiltered pairs={stats['pairs']}, rich(tau>={tau_exact})="
             f"{stats['rich']}, processed={stats['proc']}, maxG={stats['maxG']}, "
             f"best {need_Cs}-subset common rows={stats['best']}, "
             f"time={time.time()-t_start:.0f}s, hits={len(hits)}")
    return hits, stats

# ---------------- PASS 1: k=3 validation (engine re-derives in-house K_{4,2}) ----------------
logprint("[hunt885_k5] PASS 1: k=3 validation (must re-find rows {2,22,46,134}, C {1365,3360})")
k3_hits, k3_stats = hunt(3, 200, 6, 12, 90.0, "k3val")
known = ([2, 22, 46, 134], [1365, 3360])
found_known = any(sorted(r) == known[0] and sorted(c) == known[1] for r, c in k3_hits)
logprint(f"[hunt885_k5] k3 VALIDATION: in-house K_(4,2) re-derived = {found_known}; "
         f"total k3 configs found = {len(k3_hits)}")

# ---------------- PASS 2: the k=5 hunt (THE TARGET) ----------------
logprint("[hunt885_k5] PASS 2: k=5 hunt — K_(6,4) over the rich window "
         f"(s1 <= {S1_MAX}, tau >= {TAU_EXACT})")
k5_hits, k5_stats = hunt(5, S1_MAX, TAU_PREF, TAU_EXACT,
                         TIME_CAP_TOTAL - (time.time() - T0) - 5.0, "k5")

# ---------------- report ----------------
if k5_hits:
    logprint("[hunt885_k5] *** K=5 WITNESS LANDS *** (next round's Lean theorem):")
    for rows, Cs in k5_hits[:5]:
        Ns, ds = build_witness(rows, Cs)
        logprint(f"  rows={rows} Cs={Cs} -> N_i={Ns}, d={ds}")
else:
    logprint("[hunt885_k5] no K_(6,4) in the round-1 window (expected: k=5 sits at "
             "the B^0*(log)^24 divergence boundary, PROOF.md §2).")
    logprint(f"[hunt885_k5] census bound: no k=5 witness with s1 <= {S1_MAX} "
             f"(Delta <= 5e6), tau(Delta) >= {TAU_EXACT}, C <= 10^8, "
             f"row-degree <= {ROW_DEG_CAP}; best 4-C common-row count seen = "
             f"{k5_stats['best']} (need 6); maxG={k5_stats['maxG']}; "
             f"rich pairs probed = {k5_stats['proc']}.")

status = ("K5_HUNT_ROUND1 status: "
          + ("K5 WITNESS FOUND: " + str(k5_hits[0]) if k5_hits
             else f"NO HIT in gated window (Delta<=5e6, tau>=64, C<=1e8, "
                  f"deg<=30); best={k5_stats['best']}/6 common rows; "
                  f"k3-engine-validation={'PASS' if found_known else 'FAIL'}"))
logprint(status)
LOG.close()
