"""S094 DOUBTER front-line library (Council S094-COUNCIL-B).

Independent third/fourth-method engines for the extremal 2-adic curve
    v2*(M) = max{ v2(sum_{i in S} 3^i) : empty != S subseteq [0,M] }
and its (k,M) frontier, written from scratch for this probe.

Methods implemented here (all independent of the campaign's engines):
  * TargetMITM  : meet-in-the-middle on residues mod 2^64 with forced
                  elements (used for the 0-constrained / primitive-Cantor
                  variant and for the exactly-k frontier).  Binary search
                  over t using the monotonicity
                      match(t) := [exists S with 2^t | sum(S)]  is decreasing in t,
                  plus a t=64 escalation pass that exactly evaluates every
                  pair colliding mod 2^64 (full adversarial range: if no
                  collision mod 2^64 exists, v2 <= 63 is PROVEN for that M).
  * FullMITM    : plain nonempty-subset MITM (empty-empty pair excluded),
                  valid while both half-sums stay < 2^64.
  * methodA_sweep: forward residue DP with Python big-int bitsets
                  (reachable nonempty residues mod 2^t as one giant int,
                  circular shift by 3^i mod 2^t), swept over t so that one
                  pass yields match(t, M) for every M at once.
  * comb_sums   : fixed-cardinality subset-sum residues (numpy), with an
                  inverse decoder for witness recovery.

Shift-invariance law used throughout: v2(sum_{i in S} 3^i) is invariant
under S -> S+1 (factor 3 is odd), hence for EVERY class of subsets the
max is attained with min(S) = 0.  In particular
    v2*_0(M) := max{v2 : S contains 0, S subseteq [0,M]} == v2*(M),
and max_k(M) (over k-subsets) is attained with 0 in S.
"""

import math
import time

import numpy as np

np.seterr(all="ignore")

FULL64 = np.uint64((1 << 64) - 1)
M64 = (1 << 64) - 1
CHUNK = 1 << 22  # streaming chunk (4M entries, 32 MB)


def v2(x: int) -> int:
    return (x & -x).bit_length() - 1


def pow3_mod64_list(n_max):
    return [pow(3, i, 1 << 64) for i in range(n_max + 1)]


def decode_idx(idx: int, elems):
    """subset encoded by bitmask index over elems (bit j <-> elems[j])"""
    return [elems[j] for j in range(len(elems)) if (idx >> j) & 1]


def enum_side_sums(pows):
    """All subset sums (mod 2^64) of the residue list `pows`, as uint64 array.
    Index 0 = empty subset; bit j of index <-> pows[j] included. In-place doubling."""
    n = len(pows)
    r = np.zeros(1 << n, dtype=np.uint64)
    for j in range(n):
        h = 1 << j
        np.add(r[:h], np.uint64(pows[j]), out=r[h:2 * h])
    return r


# ----------------------------------------------------------------------------
# Pair-search core: maximize v2(F + a + b) over a in A, b in B (all pairs
# valid), where F is the exact sum of the forced elements and A, B are the
# residue arrays of the two free half-spaces.
# ----------------------------------------------------------------------------

class PairSearch:
    def __init__(self, forced_elems, A, elemsA, B, elemsB,
                 decode_a=None, decode_b=None):
        self.forced = sorted(forced_elems)
        self.F = sum(3 ** i for i in self.forced)
        if len(A) <= len(B):
            self.sm, self.sm_elems, self.bg, self.bg_elems = A, list(elemsA), B, list(elemsB)
        else:
            self.sm, self.sm_elems, self.bg, self.bg_elems = B, list(elemsB), A, list(elemsA)
        self.work = np.empty_like(self.sm)
        self.c64 = (-self.F) & M64
        self.probe_count = 0
        # decoders: array index -> list of ternary exponents (subset).
        # NOTE: decoders must follow the small/big swap.
        if len(A) <= len(B):
            dec_sm = decode_a or (lambda ia: decode_idx(ia, self.sm_elems))
            dec_bg = decode_b or (lambda ib: decode_idx(ib, self.bg_elems))
        else:
            dec_sm = decode_b or (lambda ia: decode_idx(ia, self.sm_elems))
            dec_bg = decode_a or (lambda ib: decode_idx(ib, self.bg_elems))
        self._dec_a = dec_sm   # decoder for self.sm
        self._dec_b = dec_bg   # decoder for self.bg

    def _probe(self, t, collect=False):
        """match(t): exists pair (a,b) with F+a+b == 0 (mod 2^t).
        If collect: return sorted list of colliding key values (classes)."""
        self.probe_count += 1
        mask = np.uint64((1 << t) - 1) if t < 64 else FULL64
        np.bitwise_and(self.sm, mask, out=self.work)
        self.work.sort()
        B = self.bg
        n = len(B)
        c = np.uint64(self.c64)
        hits = set()
        for s in range(0, n, CHUNK):
            e = min(n, s + CHUNK)
            key = np.subtract(c, B[s:e])
            key &= mask
            pos = np.searchsorted(self.work, key)
            np.minimum(pos, np.intp(len(self.work) - 1), out=pos)
            eq = self.work[pos] == key
            if eq.any():
                if not collect:
                    return True
                hits.update(int(k) for k in key[np.flatnonzero(eq)])
        if collect:
            return sorted(hits)
        return False

    def _eval_pairs(self, keys, maskbits):
        """Given colliding class values, decode all corresponding subsets and
        exactly evaluate v2. Returns list of (v2, sorted witness list)."""
        out = []
        c = self.c64
        for x in keys:
            if maskbits == 64:
                avals = np.flatnonzero(self.sm == np.uint64(x))
                bval = (c - x) & M64
                bvals = np.flatnonzero(self.bg == np.uint64(bval))
            else:
                mask = np.uint64((1 << maskbits) - 1)
                avals = np.flatnonzero((self.sm & mask) == np.uint64(x))
                bval = (c - x) & ((1 << maskbits) - 1)
                bvals = np.flatnonzero((self.bg & mask) == np.uint64(bval))
            for ia in avals[:32]:
                for ib in bvals[:32]:
                    S = list(self.forced) + self._dec_a(int(ia)) + self._dec_b(int(ib))
                    S = sorted(set(S))
                    out.append((v2(sum(3 ** i for i in S)), S))
        return out

    def solve(self, want_witness=True):
        """Returns (best_v2, witness_or_None, info_dict)."""
        t0 = time.perf_counter()
        # ---- escalation: full-collision scan at t=64 --------------------
        keys64 = self._probe(64, collect=True)
        if keys64:
            cands = self._eval_pairs(keys64, 64)
            best = max(cands)
            return best[0], best[1], {
                "mode": "escalated64", "hits64": len(keys64),
                "probes": self.probe_count, "sec": round(time.perf_counter() - t0, 3)}
        # ---- binary search on [1, 63] -----------------------------------
        if not self._probe(1):
            # every F+a+b odd; the max is 0, witness = forced set alone
            return v2(self.F), sorted(self.forced), {
                "mode": "zero", "probes": self.probe_count,
                "sec": round(time.perf_counter() - t0, 3)}
        lo, hi = 1, 63
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if self._probe(mid):
                lo = mid
            else:
                hi = mid - 1
        if not want_witness:
            return lo, None, {"mode": "bisect", "probes": self.probe_count,
                              "sec": round(time.perf_counter() - t0, 3)}
        keys = self._probe(lo, collect=True)
        cands = self._eval_pairs(keys, lo)
        good = [c for c in cands if c[0] == lo]
        # the VALUE lo is proven by the probe; only the witness can fail
        wit = max(good)[1] if good else None
        return lo, wit, {"mode": "bisect" if wit is not None else "bisect-nowit",
                         "probes": self.probe_count,
                         "sec": round(time.perf_counter() - t0, 3)}


class TargetMITM(PairSearch):
    """max v2(F + subset-sum of free_elems), all subsets of free_elems valid
    (including empty).  forced_elems are pinned into every S."""

    def __init__(self, forced_elems, free_elems):
        free = list(free_elems)
        m = len(free)
        h = m // 2
        e1, e2 = free[:h], free[h:]
        A = enum_side_sums([pow(3, i, 1 << 64) for i in e1])
        B = enum_side_sums([pow(3, i, 1 << 64) for i in e2])
        super().__init__(forced_elems, A, e1, B, e2)


class FullMITM:
    """max v2 over NONEMPTY subsets of elems (no forcing, empty pair excluded).
    Requires every half-sum < 2^64 so residue 0 identifies the empty subset
    (valid for elems=[0..M] with M <= 40)."""

    def __init__(self, elems):
        self.elems = list(elems)
        m = len(self.elems)
        h = m // 2
        e1, e2 = self.elems[:h], self.elems[h:]
        assert sum(3 ** i for i in e1) < (1 << 64) and sum(3 ** i for i in e2) < (1 << 64), \
            "FullMITM: half-sum exceeds 2^64; (0,0)-exclusion would be unsound"
        self.A = enum_side_sums([pow(3, i, 1 << 64) for i in e1])
        self.B = enum_side_sums([pow(3, i, 1 << 64) for i in e2])
        self.e1, self.e2 = e1, e2
        self.probe_count = 0

    def _probe(self, t):
        self.probe_count += 1
        mask = np.uint64((1 << t) - 1) if t < 64 else FULL64
        ka = self.A & mask
        kb = np.subtract(np.uint64(0), self.B) & mask  # -b mod 2^t
        inter = np.intersect1d(ka, kb)
        if inter.size == 0:
            return False
        if np.any(inter > 0):
            return True
        # only class 0 collides: legitimate iff some NONEMPTY half-subset
        # is itself 0 mod 2^t
        if np.any((self.A[1:] & mask) == 0) or np.any((self.B[1:] & mask) == 0):
            return True
        return False

    def solve(self, want_witness=True):
        t0 = time.perf_counter()
        # escalation at t = 64: any collision (a + b == 0 mod 2^64) other
        # than the empty-empty pair, or any nonempty half-sum == 0 mod 2^64
        ka = self.A.copy()
        kb = np.subtract(np.uint64(0), self.B)
        inter = np.intersect1d(ka, kb)
        cands = []
        for x in inter:
            x = int(x)
            if x == 0:
                # nonempty a with a == 0 (true value, so residue==0 & idx>0)
                for ia in np.flatnonzero(self.A == 0)[1:]:
                    S = decode_idx(int(ia), self.e1)
                    cands.append((v2(sum(3 ** i for i in S)), sorted(S)))
                for ib in np.flatnonzero(self.B == 0)[1:]:
                    S = decode_idx(int(ib), self.e2)
                    cands.append((v2(sum(3 ** i for i in S)), sorted(S)))
            else:
                for ia in np.flatnonzero(self.A == np.uint64(x)):
                    bval = (-x) & M64
                    for ib in np.flatnonzero(self.B == np.uint64(bval)):
                        S = decode_idx(int(ia), self.e1) + decode_idx(int(ib), self.e2)
                        S = sorted(set(S))
                        cands.append((v2(sum(3 ** i for i in S)), S))
        if cands:
            best = max(cands)
            return best[0], best[1], {"mode": "escalated64", "probes": self.probe_count,
                                      "sec": round(time.perf_counter() - t0, 3)}
        if not self._probe(1):
            return 0, None, {"mode": "zero", "probes": self.probe_count,
                             "sec": round(time.perf_counter() - t0, 3)}
        lo, hi = 1, 63
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if self._probe(mid):
                lo = mid
            else:
                hi = mid - 1
        wit = None
        if want_witness:
            mask = np.uint64((1 << lo) - 1)
            ka = self.A & mask
            kb = np.subtract(np.uint64(0), self.B) & mask
            inter = np.intersect1d(ka, kb)
            for x in inter:
                x = int(x)
                if x > 0:
                    for ia in np.flatnonzero(ka == np.uint64(x))[:4]:
                        bval = ((-x) & ((1 << lo) - 1))
                        for ib in np.flatnonzero(kb == np.uint64(bval))[:4]:
                            S = decode_idx(int(ia), self.e1) + decode_idx(int(ib), self.e2)
                            S = sorted(set(S))
                            if v2(sum(3 ** i for i in S)) == lo:
                                wit = S
                                break
                if wit:
                    break
            if wit is None and 0 in inter:
                ia = np.flatnonzero((self.A[1:] & mask) == 0)
                if ia.size:
                    wit = decode_idx(int(ia[0]) + 1, self.e1)
                else:
                    ib = np.flatnonzero((self.B[1:] & mask) == 0)
                    if ib.size:
                        wit = decode_idx(int(ib[0]) + 1, self.e2)
        return lo, wit, {"mode": "bisect", "probes": self.probe_count,
                         "sec": round(time.perf_counter() - t0, 3)}


# ----------------------------------------------------------------------------
# Method A: forward residue DP with Python big-int bitsets.
# ----------------------------------------------------------------------------

def methodA_sweep(T_A, M_max, verbose=True):
    """One DP pass per t; returns {t: [match(t, M) for M in 0..M_max]}.
    match(t, M) == True  <=>  some nonempty S subseteq [0,M] with 2^t | sum(S).
    The bitmask has 2^t bits (one per residue class mod 2^t); the step is a
    circular shift by p = 3^i mod 2^t of (R | empty-marker), OR-ed into R."""
    flags = {}
    for t in range(1, T_A + 1):
        t0 = time.perf_counter()
        mod = 1 << t
        mask = (1 << mod) - 1
        R = 0
        row = []
        for i in range(M_max + 1):
            p = pow(3, i, mod)
            x = R | 1
            hi = (x << p) & mask        # bits [p, mod) of the shifted set
            lo = x >> (mod - p)         # wrapped bits [0, p)
            R |= hi | lo
            row.append(bool(R & 1))
        flags[t] = row
        if verbose:
            print(f"  [methodA] t={t:2d} done in {time.perf_counter()-t0:8.2f}s "
                  f"(bitset {2**t/8/1e6:.1f} MB)", flush=True)
    return flags


# ----------------------------------------------------------------------------
# fixed-cardinality subset sums (for the (k,M) frontier)
# ----------------------------------------------------------------------------

def comb_sums(pows, start, n, j):
    """uint64 (wrapped) sums of all j-subsets of indices [start, n).
    Ordering: blocks by smallest index; decode with decode_combo."""
    if j == 0:
        return np.zeros(1, dtype=np.uint64)
    if n - start == j:
        s = 0
        for i in range(start, n):
            s += int(pows[i])
        return np.array([s & M64], dtype=np.uint64)
    if j == 1:
        return np.array([int(pows[i]) & M64 for i in range(start, n)], dtype=np.uint64)
    parts = []
    pi = np.uint64(0)
    for i in range(start, n - j + 1):
        sub = comb_sums(pows, i + 1, n, j - 1)
        parts.append(sub + np.uint64(int(pows[i]) & M64))
    return np.concatenate(parts) if len(parts) > 1 else parts[0]


def decode_combo(pos, start, n, j):
    """inverse of comb_sums ordering -> index list of the combo."""
    res = []
    while j > 0:
        for i in range(start, n - j + 1):
            cnt = math.comb(n - i - 1, j - 1)
            if pos < cnt:
                res.append(i)
                start = i + 1
                j -= 1
                break
            pos -= cnt
        else:  # pragma: no cover
            raise RuntimeError("decode_combo failed")
    return res


class ComboMITM(PairSearch):
    """max v2(1 + sum(T)) over T subseteq [1..M], |T| = k-1 (so S = {0} U T
    has exactly k elements and contains 0 — WLOG by shift-invariance)."""

    def __init__(self, k, M, pows):
        assert k >= 2
        self.k, self.M = k, M
        m1 = M // 2
        # j elements from [1, m1], k-1-j from [m1+1, M]
        j = max(0, min(k - 1, m1))  # placeholder; real split chosen per j below
        self.pows = pows
        self.m1 = m1
        self.sides = None

    def build(self, jA):
        jB = self.k - 1 - jA
        m1 = self.m1
        A = comb_sums(self.pows, 1, m1 + 1, jA)
        B = comb_sums(self.pows, m1 + 1, self.M + 1, jB)
        eA = list(range(1, m1 + 1))
        eB = list(range(m1 + 1, self.M + 1))
        decA = (lambda ia: []) if jA == 0 else (lambda ia: decode_combo(ia, 1, m1 + 1, jA))
        decB = (lambda ib: []) if jB == 0 else (lambda ib: decode_combo(ib, m1 + 1, self.M + 1, jB))
        PairSearch.__init__(self, [0], A, eA, B, eB, decode_a=decA, decode_b=decB)

    def solve_k(self, want_witness=True):
        best = (-1, None)
        infos = []
        for jA in range(0, self.k):
            jB = self.k - 1 - jA
            if jA > self.m1 or jB > self.M - self.m1:
                continue
            if math.comb(self.m1, jA) == 0 or math.comb(self.M - self.m1, jB) == 0:
                continue
            self.build(jA)
            v, w, info = self.solve(want_witness=want_witness)
            infos.append({"jA": jA, "v2": v, **{k2: info[k2] for k2 in ("mode", "sec")}})
            if v > best[0]:
                best = (v, w)
        if best[0] == 0:
            # zero path: every k-subset is odd; canonical witness
            best = (0, list(range(self.k)))
        return best[0], best[1], infos


# ----------------------------------------------------------------------------
# small helpers
# ----------------------------------------------------------------------------

def brute_v2star(M):
    """4th-method check: exhaustive Python-int enumeration (M <= 20)."""
    best, bw = 0, None
    p = [3 ** i for i in range(M + 1)]
    for idx in range(1, 1 << (M + 1)):
        s = 0
        j = idx
        while j:
            b = j & -j
            s += p[b.bit_length() - 1]
            j ^= b
        vv = v2(s)
        if vv > best:
            best, bw = vv, [i for i in range(M + 1) if (idx >> i) & 1]
    return best, bw


def brute_v2star0(M):
    """exhaustive check of the 0-constrained curve (M <= 20)."""
    best, bw = 0, None
    p = [3 ** i for i in range(M + 1)]
    for idx in range(0, 1 << M):  # subsets of [1..M]; 0 always included
        s = 1
        j = idx
        while j:
            b = j & -j
            s += p[b.bit_length()]
            j ^= b
        vv = v2(s)
        if vv > best:
            best, bw = vv, [0] + [i + 1 for i in range(M) if (idx >> i) & 1]
    return best, bw


def brute_maxk(M, k):
    """exhaustive exactly-k check (small M, k)."""
    from itertools import combinations
    best, bw = -1, None
    for c in combinations(range(M + 1), k):
        vv = v2(sum(3 ** i for i in c))
        if vv > best:
            best, bw = vv, list(c)
    return best, bw


def brute_g(m):
    """exhaustive: max v2 over S with {0, m} subseteq S subseteq [0, m]."""
    best, bw = -1, None
    mid = list(range(1, m))
    for idx in range(1 << len(mid)):
        s = 1 + 3 ** m
        j = idx
        while j:
            b = j & -j
            s += 3 ** mid[b.bit_length() - 1]
            j ^= b
        vv = v2(s)
        if vv > best:
            best, bw = vv, [0, m] + [mid[i] for i in range(len(mid)) if (idx >> i) & 1]
    return best, sorted(bw) if bw else None
