#!/usr/bin/env python3
"""w66_lib.py — W66 strategist shared library for Erdos #203 (2*3-smooth Sierpinski).

THE FRAME (verified reduction, repo bank): exists m, gcd(m,6)=1, with
2^k 3^l m+1 composite for all k,l >= 0  <=>  a covering of Z^2 by ONE coset
C_p = {(k,l): 2^k 3^l = t_p mod p} per palette prime p (t_p = -m^-1 mod p,
one value per prime; CRT over the primes gives m).

Column-int engine (this file's core): for prime p with dlogs (U,V) mod h
(g^U = 2, g^V = 3, g a generator of H_p = <2,3> of order h), the coset
C_p(W) = {(k,l): U k + V l = W mod h}.  Per column l the covered k-set is
ONE class k = a(W,l) mod o2 (o2 = ord_p(2)), so the whole torus covering is
computed column-by-column with L-bit Python ints (repunit<<a masks).
Masks depend on l only mod o3 = ord_p(3).

Pure python + numpy + sympy only (the venv law); no gmpy2.
"""
import json, math, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
BANK = os.path.join(os.path.dirname(HERE), "pal_dlog_full.json")  # [q,h,U,V,o2,o3]

# ---------------- palette / family ----------------
def load_bank():
    rows = json.load(open(BANK))
    return [(int(r[0]), int(r[1]), int(r[2]), int(r[3]), int(r[4]), int(r[5]))
            for r in rows]

def family(L, bank=None, extra=None):
    """palette primes with h | L (torus-valid), dedup by q."""
    if bank is None:
        bank = load_bank()
    seen = {}
    for r in bank:
        q, h = r[0], r[1]
        if L % h != 0:
            continue
        if q not in seen or 1.0 / h > 1.0 / seen[q][1]:
            seen[q] = r
    if extra:
        for r in extra:
            q, h = r[0], r[1]
            if L % h != 0:
                continue
            if q not in seen or 1.0 / h > 1.0 / seen[q][1]:
                seen[q] = r
    rows = sorted(seen.values(), key=lambda r: -1.0 / r[1])
    return rows

def budget(rows):
    return sum(1.0 / r[1] for r in rows)

# ---------------- column-int machinery ----------------
def repunit(o2, L):
    """bits at 0, o2, 2*o2, ... < o2*T (T = ceil(L/o2)); caller ANDs to L bits."""
    T = (L + o2 - 1) // o2
    return ((1 << (o2 * T)) - 1) // ((1 << o2) - 1)

class PrimeMasks:
    """per prime: per l-residue r (mod o3) the k-class a(W,r) mod o2, for a
    GIVEN W. mask = repunit(o2) << a, truncated to L bits. None if the
    column-class is not in the coset."""
    def __init__(self, q, h, U, V, o2, o3, L, W):
        self.q, self.h, self.U, self.V, self.o2, self.o3, self.L, self.W = \
            q, h, U, V, o2, o3, L, W
        self.full = (1 << L) - 1
        self.rep = repunit(o2, L) & self.full
        g1 = math.gcd(U, h)
        # k-class for c = (W - V*l) mod h, l = r: solve U k = c mod h
        self.g1 = g1
        u_inv = pow(U // g1, -1, o2)
        self.u_inv = u_inv
        self.masks = [self._mask_for_r(r) for r in range(o3)]

    def a_for(self, r):
        W, V, h, g1 = self.W, self.V, self.h, self.g1
        c = (W - V * r) % h
        if c % g1:
            return None
        return ((c // g1) * self.u_inv) % self.o2

    def _mask_for_r(self, r):
        a = self.a_for(r)
        if a is None:
            return None
        return (self.rep << a) & self.full

def column_coverage(rows, assign, L, want_cols=None, chunk=4096):
    """assign: dict q -> W. Returns (uncovered_total, per-column uncovered list
    generator-compatible). Streams columns in chunks, returns total + the
    per-column uncovered counts as a list (L entries, int)."""
    ms = []
    for r in rows:
        q, h, U, V, o2, o3 = r
        W = assign.get(q)
        if W is None:
            continue
        ms.append(PrimeMasks(q, h, U, V, o2, o3, L, W))
    unc = [0] * L
    total = 0
    cols = range(L) if want_cols is None else want_cols
    for l in cols:
        cm = 0
        for m in ms:
            mk = m.masks[l % m.o3]
            if mk:
                cm |= mk
        u = L - bin(cm).count("1")
        unc[l] = u
        total += u
    return total, unc

def uncovered_cells(rows, assign, L, out_npz=None):
    """residual cell index arrays (k_idx, l_idx) via per-column bit extraction.
    Memory-lean: processes columns in blocks, gathers packed bytes, uses numpy."""
    import numpy as np
    ms = []
    for r in rows:
        q, h, U, V, o2, o3 = r
        W = assign.get(q)
        if W is None:
            continue
        ms.append(PrimeMasks(q, h, U, V, o2, o3, L, W))
    full = (1 << L) - 1
    ks_all = []
    ls_all = []
    t0 = None
    CH = 2048
    for a in range(0, L, CH):
        b = min(a + CH, L)
        # build per-column masks, extract bits
        cols = []
        for l in range(a, b):
            cm = 0
            for m in ms:
                mk = m.masks[l % m.o3]
                if mk:
                    cm |= mk
            cols.append(full ^ cm)  # uncovered mask
        # to bytes (L bits) then unpackbits
        buf = b"".join(int.to_bytes(c, (L + 7) // 8, "little") for c in cols)
        arr = np.frombuffer(buf, dtype=np.uint8)
        bits = np.unpackbits(arr, bitorder="little").reshape(b - a, -1)[:, :L]
        kk, ll = np.nonzero(bits)
        ks_all.append((kk + 0).astype(np.int32))  # k = bit position within column
        ls_all.append((ll + a).astype(np.int32))
        del cols, buf, arr, bits, kk, ll
    k_idx = np.concatenate(ks_all)
    l_idx = np.concatenate(ls_all)
    return k_idx, l_idx

def marginal_table(rows, k_idx, l_idx, all_W=True):
    """per prime: counts[W] = #residual cells with phi_p = W.
    Uses separability: v = (U*(k mod o2) + V*(l mod o3)) mod h."""
    import numpy as np
    n = len(k_idx)
    out = {}
    for r in rows:
        q, h, U, V, o2, o3 = r
        V2 = (U * np.arange(o2, dtype=np.int64)) % h
        V3 = (V * np.arange(o3, dtype=np.int64)) % h
        v = V2[k_idx % o2] + V3[l_idx % o3]
        # mod h cheap: values < 2h
        v = np.where(v >= h, v - h, v)
        v = np.where(v >= h, v - h, v)
        counts = np.bincount(v, minlength=h)
        out[q] = counts
    return out

# ---------------- lattice algebra (HNF, intersection, quotient) ----------------
def hnf_rows(v1, v2):
    """row-style triangular basis: rows (a, b), (0, c) with a, c > 0
    spanning the same lattice as v1, v2. Returns (a, b, c).
    Members: x = a*m, y = b*m + c*n."""
    a, b = int(v1[0]), int(v1[1])
    c, d = int(v2[0]), int(v2[1])
    while c != 0:
        q = a // c
        a, b, c, d = c, d, a - q * c, b - q * d
    if a < 0:
        a, b = -a, -b
    if d < 0:
        d = -d
    if d:
        b %= d
        if b < 0:
            b += d
    return (a, b, d)

def lat_from_basis(b1, b2):
    return hnf_rows(list(b1), list(b2))

def lat_index(lat):
    a, b, c = lat
    return a * c if c else None

def lat_contains(lat, x, y):
    a, b, c = lat
    if x % a:
        return False
    m = x // a
    return (y - b * m) % c == 0 if c else (y - b * m) == 0

def lat_intersect(L1, L2):
    """intersection of two lattices in (a,b,c) row-triangular form.
    Membership: x = a*m, y = b*m + c*n."""
    a1, b1, c1 = L1
    a2, b2, c2 = L2
    if c1 == 0 or c2 == 0:
        raise ValueError("degenerate lattice")
    Lc = a1 * a2 // math.gcd(a1, a2)
    g1 = Lc // a1
    g2 = Lc // a2
    gamma = math.gcd(c1, c2)
    Delta = (b2 * g2 - b1 * g1)
    if Delta == 0:
        mu = 1
    else:
        mu = gamma // math.gcd(gamma, abs(Delta))
    # x = Lc*mu*u ; y = alpha*u + lcm*w
    # congruences: y = b1*g1*mu*u (mod c1), y = b2*g2*mu*u (mod c2)
    r1 = (b1 * g1 * mu) % c1
    r2 = (b2 * g2 * mu) % c2
    # CRT solve for coefficient alpha mod lcm(c1,c2): alpha = r1 mod c1,
    # alpha = r2 mod c2; consistent since gamma | (r1 - r2).
    lc = c1 * c2 // gamma
    assert (r1 - r2) % gamma == 0, "inconsistent CRT"
    c1p = c1 // gamma
    c2p = c2 // gamma
    dpp = (r2 - r1) // gamma
    t = (dpp * pow(c1p % c2p, -1, c2p)) % c2p if c2p > 1 else 0
    alpha = (r1 + c1 * t) % lc
    A = Lc * mu
    return (A, alpha % A if A else 0, lc) if False else hnf_rows((Lc * mu, alpha), (0, lc))

def kernel_lattice(u, v, h):
    """basis of {z in Z^2: u z1 + v z2 = 0 mod h} (from the repo engines)."""
    g0 = math.gcd(math.gcd(u, v), h)
    if g0 > 1:
        u //= g0; v //= g0; h //= g0
    g1 = math.gcd(u, v)
    if g1 == 0:
        return ((1, 0), (0, 1))
    old_r, r = u, v
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        qq = old_r // r
        old_r, r = r, old_r - qq * r
        old_s, s = s, old_s - qq * s
        old_t, t = t, old_t - qq * t
    if old_r < 0:
        old_s, old_t = -old_s, -old_t
    s, t = old_s, old_t
    gg = math.gcd(g1, h)
    m1 = h // gg
    a, bp = s, -(v // g1)
    c, dp = t, (u // g1)
    return (a * m1, c * m1), (bp, dp)

def six_minor_s(b1p, b2p, b1q, b2q):
    dets = [abs(b1p[0] * b2p[1] - b1p[1] * b2p[0]),
            abs(b1q[0] * b2q[1] - b1q[1] * b2q[0])]
    for (u, v) in ((b1p, b1q), (b1p, b2q), (b2p, b1q), (b2p, b2q)):
        dets.append(abs(u[0] * v[1] - u[1] * v[0]))
    s = 0
    for d in dets:
        s = math.gcd(s, d)
    return s

if __name__ == "__main__":
    # SELF-TEST at tiny scale: brute-force cross-check of the column engine.
    import random
    rng = random.Random(7)
    L = 60
    bank = load_bank()
    rows = [r for r in bank if L % r[1] == 0][:8]
    print("test family:", [(r[0], r[1]) for r in rows])
    assign = {r[0]: rng.randrange(r[1]) for r in rows}
    total, unc = column_coverage(rows, assign, L)
    # brute force over the torus
    tot2 = 0
    for k in range(L):
        for l in range(L):
            cov = False
            for r in rows:
                q, h, U, V, o2, o3 = r
                if (U * k + V * l) % h == assign[q]:
                    cov = True
                    break
            if not cov:
                tot2 += 1
    print("column-int uncovered:", total, " brute:", tot2)
    assert total == tot2, "MISMATCH"
    # residual cells cross-check
    ki, li = uncovered_cells(rows, assign, L)
    print("residual cells:", len(ki), "== ", total)
    assert len(ki) == total
    # marginal table cross-check for prime rows[0]
    mt = marginal_table([rows[0]], ki, li)
    q0 = rows[0][0]
    cnt_brute = [0] * rows[0][1]
    for i in range(len(ki)):
        v = (rows[0][2] * int(ki[i]) + rows[0][3] * int(li[i])) % rows[0][1]
        cnt_brute[v] += 1
    assert list(mt[q0]) == cnt_brute, "marginal mismatch"
    print("marginal table OK; self-test PASS")
