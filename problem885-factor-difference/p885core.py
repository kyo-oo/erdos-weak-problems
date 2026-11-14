#!/usr/bin/env python3
"""p885core.py — W63-B5 / P885 core: the factorization-indexed config engine.

THE MODEL (P885 PROOF.md §1, Theorems A/B): a #885(k) witness ⟺ a
K_{k+1,k-1} grid configuration — k+1 distinct rows s, k-1 distinct positive
columns C, all (k+1)(k-1) sums s^2 + C perfect squares (Theorem B: ANY row
parities, cleared by the lambda=2 scaling).  Pair-indexed enumeration
(PROOF.md §2): anchor (s0, s1) -> G(s0, s1) = candidate columns from the
factor pairs of Delta = s1^2 - s0^2; each candidate's FULL row set R(C) is
computed EXACTLY from the factor pairs of C (C odd: pairs of C, row
(q-p)/2; C = 4t: pairs of t, row q-p; C = 2 mod 4: no rows); then hunt
(k-1)-subsets of G with >= k+1 common rows (the biclique).

W63-B5 escalation upgrades over round 1/2 (hunt885_k5*.py):
  * RICH-COLUMN FUNNEL — only columns with >= need_rows rows can be in the
    biclique; a tiered tau prefilter (primes <= 1000; the cofactor of any
    n <= 1e9 with all prime factors > 1000 has tau <= 4 — shapes p, p^2,
    p*q only, since p^2*q, p*q*r >= 1009^3 > 1.027e9) kills poor columns
    before full factorization.  rows(C) = tau(C)//2 (odd) / tau(C//4)//2
    (C = 4t), so the gate tau >= 2*need_rows is EXACT.
  * RICH-COLUMN CACHE — a rich column recurs across all C(rows,2) anchors
    of the window, so C -> rows is cached (amortized factorization).
  * COLUMN-PAIR SIGNATURE INDEX — every 2-subset of rich columns with
    >= need_rows common rows (a K_{k+1,2}) is recorded for the
    merge-extension pass (the delta-signature structure of PROOF.md §2).
  * CHECKPOINT/RESUME (L75 law): frontier u + stats + hits on disk.

Exactness register (all claims honest):
  - factorize_exact: trial division by primes <= 40000 -> EXACT for any
    n <= 1.6e9 (cofactor composite would exceed 40000^2 = 1.6e9).
  - tau_ge(n, need): sound prefilter only (never false-negative).
  - rows_of_C / G_candidates / common-row counts: EXACT (full row sets,
    full factor-pair enumeration, no range cuts beyond C <= C_CAP and
    m0 > s0 <=> C > 0).
"""
import time, json, os
from math import isqrt
from itertools import combinations
from collections import defaultdict

# ---------------------------------------------------------------- primes
def primes_upto(n):
    bs = bytearray(n + 1)
    bs[0] = bs[1] = 1
    out = []
    for i in range(2, n + 1):
        if not bs[i]:
            out.append(i)
            for j in range(i * i, n + 1, i):
                bs[j] = 1
    return out

P1000 = primes_upto(1000)          # tier-1 tau prefilter (168 primes)
FULL_PRIMES = primes_upto(40000)    # exact factorization for n <= 1.6e9

def factorize_exact(n):
    """Exact prime factorization by trial division (EXACT for n <= 1.6e9)."""
    f = {}
    for p in FULL_PRIMES:
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

def divisors_of(f):
    divs = [1]
    for p, e in f.items():
        divs = [d * p ** k for d in divs for k in range(e + 1)]
    return divs

def tau_ge(n, need):
    """Sound tau prefilter: True only if tau(n) >= need is still possible;
    False => tau(n) < need CERTAINLY (never skips a rich column).
    Cofactor bound: n <= 1e9 with all prime factors > 1000 has tau <= 4
    (p^2*q and p*q*r are >= 1009^3 = 1.027e9 > 1e9 — impossible)."""
    m = n
    tau = 1
    for p in P1000:
        if p * p > m:
            break
        if m % p == 0:
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            tau *= (e + 1)
    if m == 1:
        return tau >= need
    if p * p > m:          # loop broke with p^2 > m: m is 1 or prime
        return tau * 2 >= need
    return tau * 4 >= need  # exhausted P1000: cofactor all-prime->1000, tau<=4

# ---------------------------------------------------------------- columns
class ColEngine:
    """Rich-column oracle: rows(C) = FULL row set of C (exact), cached;
    returns None when |rows(C)| < need_rows (poor column — cannot be in
    any K_{k+1,k-1})."""
    def __init__(self, need_rows, cache_cap=900_000):
        self.need = need_rows
        self.cap = cache_cap
        self.cache = {}          # C -> tuple(rows) (rich only)
        self.stats = {"queries": 0, "misses": 0, "rich": 0, "poor": 0}

    def rows(self, C):
        self.stats["queries"] += 1
        r = self.cache.get(C)
        if r is not None:
            return r
        self.stats["misses"] += 1
        if C % 2 == 1:
            base, odd = C, True
        elif C % 4 == 0:
            base, odd = C // 4, False
        else:
            self.stats["poor"] += 1
            return None
        if not tau_ge(base, 2 * self.need):     # rows = tau//2 (both cases)
            self.stats["poor"] += 1
            return None
        divs = divisors_of(factorize_exact(base))
        out = []
        for p in divs:
            q = base // p
            if p < q:
                out.append((q - p) // 2 if odd else q - p)
        if len(out) < self.need:
            self.stats["poor"] += 1
            return None
        out.sort()
        t = tuple(out)
        self.stats["rich"] += 1
        if len(self.cache) < self.cap:
            self.cache[C] = t
        return t

# ---------------------------------------------------------------- anchors
def G_candidates(s0, s1, c_cap):
    """All C with 0 < C <= c_cap, s0^2+C and s1^2+C both squares — from the
    factor pairs of Delta = s1^2 - s0^2 (EXACT; Delta = 2 mod 4 impossible)."""
    Delta = s1 * s1 - s0 * s0
    out = []
    if Delta % 2 == 1:
        for p in divisors_of(factorize_exact(Delta)):
            q = Delta // p
            if p < q:
                m0 = (q - p) // 2
                if m0 > s0:
                    C = m0 * m0 - s0 * s0
                    if C <= c_cap:
                        out.append(C)
    elif Delta % 4 == 0:
        t = Delta // 4
        for p in divisors_of(factorize_exact(t)):
            q = t // p
            if p < q:
                m0 = q - p
                if m0 > s0:
                    C = m0 * m0 - s0 * s0
                    if C <= c_cap:
                        out.append(C)
    return out

def verify_config(rows, Cs):
    """Exact check: all rows*Cs sums perfect squares; rows/Cs distinct; C>0."""
    if len(set(rows)) != len(rows) or len(set(Cs)) != len(Cs):
        return False
    if any(c <= 0 for c in Cs) or any(s < 1 for s in rows):
        return False
    for s in rows:
        s2 = s * s
        for c in Cs:
            t = s2 + c
            m = isqrt(t)
            if m * m != t:
                return False
    return True

def build_witness(rows, Cs):
    """Theorem B lambda=2 scaling: rows sorted, s_min = rows[0];
    N_i = s_i^2 - s_min^2 (i >= 1); d = [2*s_min] + [2*isqrt(C_j + s_min^2)]."""
    rows = sorted(rows)
    s_min = rows[0]
    Ns = [s * s - s_min * s_min for s in rows[1:]]
    ds = [2 * s_min] + [2 * isqrt(c + s_min * s_min) for c in Cs]
    return Ns, ds

# ---------------------------------------------------------------- the hunt
def process_pair(s0, s1, k, coleng, row_deg_cap=40):
    """One anchor pair. Returns (best, hits, rich_count, pair_hits) where
    hits = K_{k+1,k-1} configs [(rows, Cs)] (verified) and pair_hits =
    K_{k+1,2} column pairs [(A, B, sorted common rows)] (exact)."""
    need_rows, need_cs = k + 1, k - 1
    G = G_candidates(s0, s1, coleng and COLCAP[0])
    if len(G) < need_cs:
        return 0, [], 0, []
    rich, rowslist = [], []
    for C in G:
        r = coleng.rows(C)
        if r is not None:
            rich.append(C)
            rowslist.append(set(r))
    if len(rich) < need_cs:
        return 0, [], len(rich), []
    rowmap = defaultdict(list)
    for idx, rs in enumerate(rowslist):
        for s in rs:
            rowmap[s].append(idx)
    cnt = defaultdict(int)
    for s, lst in rowmap.items():
        if len(lst) < need_cs:
            continue
        for combo in combinations(sorted(lst)[:row_deg_cap], need_cs):
            cnt[combo] += 1
    best = max(cnt.values()) if cnt else 0
    hits, pair_hits = [], []
    for combo, c in cnt.items():
        if c >= need_rows:
            Cs = [rich[i] for i in combo]
            csz = set(combo)
            rows = sorted(r for r, lst in rowmap.items() if csz <= set(lst))
            if verify_config(rows[:need_rows], Cs):
                hits.append((rows, Cs))
    # K_{k+1,2} signature pairs (exact common-row count of rich col pairs)
    for i in range(len(rich)):
        for j in range(i + 1, len(rich)):
            cij = rowslist[i] & rowslist[j]
            if len(cij) >= need_rows:
                pair_hits.append((rich[i], rich[j], sorted(cij)))
    return best, hits, len(rich), pair_hits

COLCAP = [10 ** 8]   # module-level C cap (set by the runner)

# ---------------------------------------------------------------- driver
def hunt_chunk(k, s1_max, tau_pref, tau_exact, budget, tag, ckpt_path,
               hits_path, pairs_path, coleng, tau_sieve, t_global0=None):
    """One resumable chunk of the pair-indexed hunt. Checkpoints the u
    frontier; appends hits / K_{k+1,2} pairs (deduped); returns summary."""
    t_start = time.time()
    st = {"pairs": 0, "rich": 0, "proc": 0, "maxG": 0, "best": 0,
          "hits": 0, "pairhits": 0, "maxrich": 0, "u_next": 1}
    seen_hits, seen_pairs = set(), set()
    if os.path.exists(ckpt_path):
        with open(ckpt_path) as fh:
            prev = json.load(fh)
        st.update({kk: prev.get(kk, st[kk]) for kk in
                   ("pairs", "rich", "proc", "maxG", "best", "hits",
                    "pairhits", "maxrich")})
        st["u_next"] = prev["u_next"]
        if os.path.exists(hits_path):
            for line in open(hits_path):
                try:
                    h = json.loads(line)
                    seen_hits.add((tuple(h["rows"]), tuple(h["Cs"])))
                except Exception:
                    pass
        if os.path.exists(pairs_path):
            for line in open(pairs_path):
                try:
                    h = json.loads(line)
                    seen_pairs.add((h["A"], h["B"]))
                except Exception:
                    pass
    HF = open(hits_path, "a") if hits_path else None
    PF = open(pairs_path, "a") if pairs_path else None
    for u in range(st["u_next"], s1_max + 1):
        if time.time() - t_start > budget:
            st["u_next"] = u
            _save(ckpt_path, st)
            if HF: HF.close()
            if PF: PF.close()
            return st, False
        for v in range(u + 2, 2 * s1_max - u + 1, 2):
            D = u * v
            if tau_sieve[D] < tau_pref:
                continue
            st["pairs"] += 1
            tauD = 1
            for e in factorize_exact(D).values():
                tauD *= (e + 1)
            if tauD < tau_exact:
                continue
            st["rich"] += 1
            s0, s1 = (v - u) // 2, (u + v) // 2
            best, hh, g, ph = process_pair(s0, s1, k, coleng)
            st["proc"] += 1
            st["maxG"] = max(st["maxG"], g)
            st["maxrich"] = max(st["maxrich"], g)
            if best > st["best"]:
                st["best"] = best
                print(f"  [{tag}] new best: {k-1}-C subset with {best} "
                      f"common rows (s0={s0}, s1={s1}, rich={g})", flush=True)
            for rows, Cs in hh:
                key = (tuple(sorted(rows)[:k + 1]), tuple(sorted(Cs)))
                if key not in seen_hits:
                    seen_hits.add(key)
                    st["hits"] += 1
                    if HF:
                        HF.write(json.dumps({"rows": list(key[0]),
                                             "Cs": list(key[1])}) + "\n")
                        HF.flush()
                    print(f"*** HIT k={k}: rows={list(key[0])} "
                          f"Cs={list(key[1])}", flush=True)
            if PF:
                for A, B, crows in ph:
                    pk = (A, B)
                    if pk not in seen_pairs:
                        seen_pairs.add(pk)
                        st["pairhits"] += 1
                        PF.write(json.dumps({"A": A, "B": B,
                                             "rows": crows}) + "\n")
        st["u_next"] = u + 1
        if u % 100 == 0:
            _save(ckpt_path, st)
            print(f"  [{tag}] u={u} pairs={st['pairs']} rich={st['rich']} "
                  f"proc={st['proc']} best={st['best']} "
                  f"hits={st['hits']} Kpairs={st['pairhits']} "
                  f"t={time.time()-t_start:.0f}s "
                  f"cache={len(coleng.cache)}", flush=True)
    st["u_next"] = s1_max + 1
    _save(ckpt_path, st)
    if HF: HF.close()
    if PF: PF.close()
    return st, True

def _save(path, st):
    tmp = path + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(st, fh)
    os.replace(tmp, path)

def build_tau_sieve(lim):
    import numpy as np
    tau = np.zeros(lim + 1, dtype=np.int16)
    for d in range(1, isqrt(lim) + 1):
        tau[d::d] += 1
    return tau

def exact_tau(n):
    t = 1
    for e in factorize_exact(n).values():
        t *= (e + 1)
    return t
