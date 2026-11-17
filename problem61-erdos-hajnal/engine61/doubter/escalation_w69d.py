#!/usr/bin/env python3
"""
ESCALATION BATTERY W69-D -- Erdos #61 doubter lane, round 3 (Task W69-D).

TARGET (killer lane's family design, branch w67-p61k):
  For F7 = {K1, K2, Kb2, P3, Pb3, K3, Kb3}, every H-free graph G on n vertices
  satisfies max(omega(G), alpha(G)) >= floor(sqrt(n))   (SHARP form),
  with TIGHTNESS witnessed by the disjoint union of 2^j copies of K_{2^j}
  (n = 4^j vertices, omega = alpha = 2^j = floor(sqrt n) exactly).

This battery ESCALATES the CI-green W68 mirror battery (n<=6) with:

  [N7]  FULL labeled exhaustive census at n=7: every one of the 2^21 =
        2,097,152 labeled graphs is classified against all 7 family members
        and sharp-checked.  omega/alpha via TWO engines: DP tables
        (vertex-extension recurrence) and branch-and-bound clique search --
        must agree on ALL 2^21 graphs.  The K3-free class is additionally
        re-counted by a NAIVE TRIPLE SCAN over all 2^21 graphs (engine C).
        The P3-free class is re-generated from set partitions (Bell(7)=877)
        and compared as a SET.  Complement identities (K3<->Kb3, P3<->Pb3
        flags) are verified over the whole space.  The n<=6 cumulative
        counts must replicate the banked W68 battery values.

  [N8]  n=8 census per member (complete per-member enumeration; the full
        2^28 space is not scanned): P3-free = all Bell(8)=4140 partition
        graphs (omega/alpha verified against block structure), Pb3-free via
        complements, K3-free = ALL labeled triangle-free graphs on 8
        vertices enumerated by the (triangle-free F7) x (independent set S)
        extension with per-graph re-verification and EXACT alpha for every
        graph, frontier min max(omega,alpha) and the alpha=3 extremal
        census; Kb3-free by the complement bijection (flag identity
        verified over all 2^21 graphs at n=7).

  [P4]  THE P4/COGRAPH FRONTIER n<=9: labeled cographs by the Seinsche
        recursion (disjoint union / join from K1) for n<=8, unlabeled
        cograph iso-classes by the reduced-cotree multiset recursion for
        n<=9, with the identity labeled(n) = SUM_classes n!/|Aut| required
        to hold exactly at n<=8 (two independent engines).  Every class is
        directly re-verified (induced-P4 orbit scan + B&B omega/alpha vs
        the cotree DP + connectivity/root-type consistency).  Banks the
        empirical Erdos-Hajnal exponent min log2(max(omega,alpha))/log2(n),
        the product law omega*alpha >= n, and the ceil-form observation.

  [TIGHT] Tightness witnesses j=1..5: disjoint union of 2^j copies of
        K_{2^j} on n = 4^j vertices; omega = alpha = 2^j = isqrt(4^j)
        EXACTLY, plus structural P3-free / Pb3-free verification (own code,
        exact integer sqrt; P4-free orbit scan for n<=64).

Pure python stdlib.  Exits nonzero on ANY failure.  English only.
Receipts: TIGHT_WITNESS_GREEN, E61_N7_FULL_CENSUS_GREEN, E61_N8_CENSUS_GREEN,
E61_P4_FRONTIER_GREEN, E61_DOUBTER_W69D_GREEN.
"""
import sys
import json
import time
from math import isqrt, log2, factorial
from itertools import combinations, permutations, product

sys.setrecursionlimit(20000)

T0 = time.time()
FAIL = []


def fail(msg):
    FAIL.append(msg)
    print("FAIL: " + msg)


def stamp():
    return "[t+%6.1fs]" % (time.time() - T0)


# =====================================================================
# Pair indexing (W69-D scheme, built PER level -- no shared global index).
# Pairs (i,j), i<j, of level k are sorted by key (j, -i): all pairs inside
# {0..k-2} come first (recursively in the same scheme), then the pairs of
# vertex k-1 in the order (k-2,k-1), (k-3,k-1), ..., (0,k-1).
# STRUCTURAL FACT: F = F_low | (topbits << m(k-1)) decomposes a level-k mask
# into the induced level-(k-1) mask on {0..k-2} plus the k-1 edge bits of
# vertex k-1; topbits bit j <-> pair (k-2-j, k-1).  Hence the neighborhood
# VERTEX mask of vertex k-1 is the REVERSED top-edge bits; the ENC/DEC
# tables below centralize that correspondence (self-tested against direct
# adjacency extraction).
# =====================================================================

def m(k):
    return k * (k - 1) // 2


PAIRS = {}
PI = {}
FULL = {}
for k in range(0, 11):
    ps = sorted(combinations(range(k), 2), key=lambda p: (p[1], -p[0]))
    PAIRS[k] = ps
    PI[k] = {p: i for i, p in enumerate(ps)}
    FULL[k] = (1 << m(k)) - 1
for k in range(2, 11):
    assert PAIRS[k][:m(k - 1)] == PAIRS[k - 1], k
    assert PAIRS[k][m(k - 1):] == [(i, k - 1) for i in range(k - 2, -1, -1)], k

# ENC[k][S]: S = vertex bitmask over {0..k-2} (bit v = "v adjacent to k-1")
#            -> the top (k-1) EDGE bits.  DEC[k] = inverse.
ENC = {}
DEC = {}
for k in range(2, 11):
    base = m(k - 1)
    enc = [0] * (1 << (k - 1))
    for S in range(1, 1 << (k - 1)):
        b = S & (-S)
        v = b.bit_length() - 1
        enc[S] = enc[S ^ b] | (1 << (base + (k - 2 - v)))
    ENC[k] = enc
    dec = [0] * (1 << (k - 1))
    for S in range(1 << (k - 1)):
        dec[enc[S] >> base] = S
    DEC[k] = dec
    for X in range(1 << (k - 1)):
        assert (ENC[k][DEC[k][X]] >> base) == X
        assert DEC[k][ENC[k][X] >> base] == X


def adj_of(F, n):
    """Adjacency bitmasks (list of n ints) of the level-n edge mask F."""
    adj = [0] * n
    for b, (i, j) in enumerate(PAIRS[n]):
        if (F >> b) & 1:
            adj[i] |= 1 << j
            adj[j] |= 1 << i
    return adj


def mask_from_adj(adj, n):
    F = 0
    for i in range(n):
        for j in range(i + 1, n):
            if (adj[i] >> j) & 1:
                F |= 1 << PI[n][(i, j)]
    return F


def pc(x):
    return x.bit_count()


# =====================================================================
# Exact clique machinery (branch-and-bound) + brute reference.
# =====================================================================

def omega_on(adj, cand):
    """Max clique within candidate vertex bitmask `cand` (adj pre-masked)."""
    best = 0

    def bk(rs, c):
        nonlocal best
        if rs > best:
            best = rs
        if rs + pc(c) <= best:
            return
        while c:
            if rs + pc(c) <= best:
                return
            b = c & (-c)
            v = b.bit_length() - 1
            c ^= b
            bk(rs + 1, c & adj[v])

    bk(0, cand)
    return best


def omega_bb(adj, n):
    return omega_on(adj, (1 << n) - 1)


def alpha_bb(adj, n):
    full = (1 << n) - 1
    comp = [full & ~adj[v] & ~(1 << v) for v in range(n)]
    return omega_bb(comp, n)


def omega_brute(adj, n):
    """Reference clique number by full subset scan (obviously correct)."""
    best = 0
    for S in range(1 << n):
        c = pc(S)
        if c <= best:
            continue
        ok = True
        x = S
        while x:
            b = x & (-x)
            v = b.bit_length() - 1
            x ^= b
            if S & ~adj[v] & ~(1 << v):
                ok = False
                break
        if ok:
            best = c
    return best


def triangle_free_direct(adj, n):
    """Naive: any triple of mutually adjacent vertices? (early exit)."""
    for a in range(n):
        for b in range(a + 1, n):
            if (adj[a] >> b) & 1:
                for c in range(b + 1, n):
                    if (adj[a] >> c) & 1 and (adj[b] >> c) & 1:
                        return False
    return True


def cluster_direct(adj, n):
    """P3-free check: the neighborhood of every vertex is a clique."""
    for v in range(n):
        nb = adj[v]
        x = nb
        while x:
            b = x & (-x)
            u = b.bit_length() - 1
            x ^= b
            if nb & ~adj[u] & ~(1 << u):
                return False
    return True


def components_of(adj, n):
    """List of component vertex-masks."""
    seen = 0
    comps = []
    for v in range(n):
        if not (seen >> v) & 1:
            comp = 0
            front = 1 << v
            while front:
                comp |= front
                nxt = 0
                x = front
                while x:
                    b = x & (-x)
                    u = b.bit_length() - 1
                    x ^= b
                    nxt |= adj[u]
                front = nxt & ~comp
            seen |= comp
            comps.append(comp)
    return comps


# =====================================================================
# Set partitions (blocks as lists) -- Bell census ground truth.
# =====================================================================

def set_partitions(verts):
    verts = list(verts)
    if not verts:
        yield []
        return
    first = verts[0]
    rest = verts[1:]
    for r in range(len(rest) + 1):
        for sub in combinations(rest, r):
            others = [v for v in rest if v not in sub]
            for pi in set_partitions(others):
                yield [[first] + list(sub)] + pi


BELL = {1: 1, 2: 2, 3: 5, 4: 15, 5: 52, 6: 203, 7: 877, 8: 4140}

# Banked CI-green cumulative counts from the W68 mirror battery (n<=6).
BANKED_NLE6 = {'K1': 0, 'K2': 6, 'Kb2': 6, 'P3': 278, 'Pb3': 278,
               'K3': 6228, 'Kb3': 6228, 'P4': 6039}

FAMILY = ['K1', 'K2', 'Kb2', 'P3', 'Pb3', 'K3', 'Kb3']


# =====================================================================
# Induced-P4 local orbit (for cograph verification).
# =====================================================================

def p4_local_orbit():
    """The 12 induced-P4 masks in the local combinations(S,2) 6-bit order."""
    path = [(0, 1), (1, 2), (2, 3)]
    lidx = {p: i for i, p in enumerate(combinations(range(4), 2))}
    res = set()
    for perm in permutations(range(4)):
        msk = 0
        for (a, b) in path:
            u, v = perm[a], perm[b]
            msk |= 1 << lidx[(min(u, v), max(u, v))]
        res.add(msk)
    assert len(res) == 12
    return res


P4_LOCAL = p4_local_orbit()


def p4_free_direct(adj, n):
    """Induced P4 scan over all 4-subsets (local combinations order)."""
    if n < 4:
        return True
    for S in combinations(range(n), 4):
        msk = 0
        for idx, (u, v) in enumerate(combinations(S, 2)):
            if (adj[u] >> v) & 1:
                msk |= 1 << idx
        if msk in P4_LOCAL:
            return False
    return True


# =====================================================================
# SECTION 1 -- core self-tests.
# =====================================================================

def self_test_core():
    print(stamp() + " [CORE] omega B&B vs brute subset scan (all graphs"
          " n<=5 + 2000 deterministic n=6..10)")
    lcg = 123456789
    bad = 0
    for n in range(1, 6):
        for F in range(1 << m(n)):
            adj = adj_of(F, n)
            if omega_bb(adj, n) != omega_brute(adj, n):
                bad += 1
                if bad <= 3:
                    fail("omega B&B != brute n=%d F=%d" % (n, F))
    for _ in range(2000):
        lcg = (lcg * 6364136223846793005 + 1442695040888963407) & ((1 << 61) - 1)
        n = 6 + (lcg % 5)
        F = lcg % (1 << m(n))
        adj = adj_of(F, n)
        if omega_bb(adj, n) != omega_brute(adj, n):
            bad += 1
            if bad <= 3:
                fail("omega B&B != brute n=%d F=%d" % (n, F))
    print("  disagreements: %d" % bad)
    if bad:
        fail("core clique engine broken")

    print(stamp() + " [CORE] ENC/DEC top-bit correspondence vs direct"
          " adjacency (all level-6 masks x 2 patterns + 5000 samples n=7,8)")
    bad = 0
    for F6 in range(1 << m(6)):
        adj = adj_of(F6, 6)
        Nva = (F6 * 2654435761) & 0x3F
        for Nv in {Nva, 63 - Nva}:
            F = F6 | ENC[7][Nv]
            adj7 = adj_of(F, 7)
            if adj7[6] != Nv:
                bad += 1
                if bad <= 3:
                    fail("ENC mismatch F6=%d Nv=%d nb=%d" % (F6, Nv, adj7[6]))
    for _ in range(5000):
        lcg = (lcg * 6364136223846793005 + 1442695040888963407) & ((1 << 61) - 1)
        n = 7 + (lcg % 2)
        F = lcg % (1 << m(n))
        adj = adj_of(F, n)
        if DEC[n][F >> m(n - 1)] != adj[n - 1]:
            bad += 1
            if bad <= 3:
                fail("DEC mismatch n=%d F=%d" % (n, F))
    print("  disagreements: %d" % bad)
    if bad:
        fail("ENC/DEC correspondence broken")

    print(stamp() + " [CORE] partition graphs: cluster + omega==maxblock +"
          " alpha==#blocks (n<=6, vs B&B)")
    bad = 0
    for n in range(1, 7):
        cnt = 0
        for pi in set_partitions(range(n)):
            adj = [0] * n
            for block in pi:
                for u, v in combinations(block, 2):
                    adj[u] |= 1 << v
                    adj[v] |= 1 << u
            cnt += 1
            if not cluster_direct(adj, n):
                bad += 1
                if bad <= 3:
                    fail("partition graph not cluster n=%d" % n)
            if omega_bb(adj, n) != max(len(b) for b in pi):
                bad += 1
            if alpha_bb(adj, n) != len(pi):
                bad += 1
        if cnt != BELL[n]:
            fail("partition count != Bell(%d): %d" % (n, cnt))
    print("  violations: %d; Bell(1..6) = %s OK"
          % (bad, [BELL[i] for i in range(1, 7)]))
    if bad:
        fail("core structural engine broken")


# =====================================================================
# SECTION 2 -- level tables n<=6, member counts by DIRECT structural flags
# (third engine; must replicate the banked W68 battery numbers).
# =====================================================================

def build_level_tables():
    print(stamp() + " [N<=6] direct structural census per member, n=1..6"
          " (replicates banked W68 numbers)")
    counts = {h: {n: 0 for n in range(1, 7)} for h in
              ['K1', 'K2', 'Kb2', 'P3', 'Pb3', 'K3', 'Kb3', 'P4']}
    tf_sets = {1: {0}}
    p3_sets = {1: {0}}
    p4_sets = {1: {0}}
    for n in range(1, 7):
        full = FULL[n]
        tfn = set()
        p3n = set()
        p4n = set()
        k2 = kb2 = kb3 = pb3 = 0
        for F in range(1 << m(n)):
            adj = adj_of(F, n)
            if F == 0:
                k2 += 1
            if F == full:
                kb2 += 1
            if triangle_free_direct(adj, n):
                tfn.add(F)
            if cluster_direct(adj, n):
                p3n.add(F)
            if p4_free_direct(adj, n):
                p4n.add(F)
        # complement-side members: Kb3-free(G) iff K3-free(comp(G)),
        # Pb3-free(G) iff P3-free(comp(G)); comp mask = F ^ full.
        for F in range(1 << m(n)):
            adj = adj_of(F, n)
            comp = [((1 << n) - 1) & ~adj[v] & ~(1 << v) for v in range(n)]
            tfc = triangle_free_direct(comp, n)
            p3c = cluster_direct(comp, n)
            if tfc:
                kb3 += 1
                if (F ^ full) not in tfn:
                    fail("Kb3 complement-identity broken n=%d F=%d" % (n, F))
            if p3c:
                pb3 += 1
                if (F ^ full) not in p3n:
                    fail("Pb3 complement-identity broken n=%d F=%d" % (n, F))
            if not tfc and (F ^ full) in tfn:
                fail("Kb3 complement-identity broken (reverse) n=%d F=%d" % (n, F))
        counts['K2'][n] = k2
        counts['Kb2'][n] = kb2
        counts['K3'][n] = len(tfn)
        counts['Kb3'][n] = kb3
        counts['P3'][n] = len(p3n)
        counts['Pb3'][n] = pb3
        counts['P4'][n] = len(p4n)
        tf_sets[n] = tfn
        p3_sets[n] = p3n
        p4_sets[n] = p4n
        print("  n=%d: K2=%d Kb2=%d P3=%d Pb3=%d K3=%d Kb3=%d P4=%d"
              % (n, k2, kb2, len(p3n), pb3, len(tfn), kb3, len(p4n)))
    for h, banked in BANKED_NLE6.items():
        tot = sum(counts[h][n] for n in range(1, 7))
        if tot != banked:
            fail("n<=6 cumulative %s = %d != banked %d" % (h, tot, banked))
    print("  n<=6 cumulative vs banked W68 battery: K1=0 K2=6 Kb2=6 P3=278"
          " Pb3=278 K3=6228 Kb3=6228 P4=6039 -- REPLICATED")
    return counts, tf_sets, p3_sets, p4_sets


# =====================================================================
# SECTION 3 -- n=7 FULL labeled exhaustive census (2^21 graphs).
# =====================================================================

def census_n7(tf6_set):
    print(stamp() + " [N7] level-6 tables (TF/P3F/COMPS/OM via B&B)")
    TF6 = bytearray(1 << 15)
    P3F6 = bytearray(1 << 15)
    OM6 = bytearray(1 << 15)
    COMP6 = {}
    for F in range(1 << 15):
        adj = adj_of(F, 6)
        tf = triangle_free_direct(adj, 6)
        p3 = cluster_direct(adj, 6)
        TF6[F] = 1 if tf else 0
        P3F6[F] = 1 if p3 else 0
        OM6[F] = omega_bb(adj, 6)
        if p3:
            COMP6[F] = tuple(components_of(adj, 6))
    for F in tf6_set:
        if not TF6[F]:
            fail("tf6 set disagrees with direct triple scan at F=%d" % F)
    if sum(TF6) != len(tf6_set):
        fail("TF6 count %d != tf6 set size %d" % (sum(TF6), len(tf6_set)))
    print("  TF6=%d P3F6=%d (Bell(6)=203)" % (sum(TF6), sum(P3F6)))
    if sum(P3F6) != 203:
        fail("P3F6 count != Bell(6)")

    print(stamp() + " [N7] OM7 engine A: vertex-extension DP over all 2^21")
    OM7 = bytearray(1 << 21)
    for F6 in range(1 << 15):
        adj = adj_of(F6, 6)
        f = [0] * 64
        for N in range(1, 64):
            b = N & (-N)
            v = b.bit_length() - 1
            a = f[N ^ b]
            c = 1 + f[N & adj[v]]
            f[N] = a if a >= c else c
        base = OM6[F6]
        enc = ENC[7]
        for Nv in range(64):
            w = base
            g = 1 + f[Nv]
            if g > w:
                w = g
            OM7[ENC[7][Nv] | F6] = w
    for F6 in range(0, 1 << 15, 97):
        if OM7[F6] != OM6[F6]:
            fail("OM7 Nv=0 slice != OM6 at F6=%d" % F6)

    print(stamp() + " [N7] engine B: full B&B omega+alpha on ALL 2^21 graphs"
          " (must equal engine A tables)")
    FULL7 = FULL[7]
    bad = 0
    for F in range(1 << 21):
        adj = adj_of(F, 7)
        w = omega_bb(adj, 7)
        a = alpha_bb(adj, 7)
        if OM7[F] != w or OM7[F ^ FULL7] != a:
            bad += 1
            if bad <= 5:
                fail("OM7 DP != B&B at F=%d (dp w=%d a=%d, bb w=%d a=%d)"
                     % (F, OM7[F], OM7[F ^ FULL7], w, a))
    print("  graphs checked: %d; disagreements: %d" % (1 << 21, bad))
    if bad:
        fail("n=7 omega/alpha dual-engine disagreement")

    print(stamp() + " [N7] master scan: classify every graph against all 7"
          " members + sharp form + frontier")
    ISQRT7 = isqrt(7)
    mc = {h: 0 for h in FAMILY}
    mmin = {h: None for h in FAMILY}
    marg = {h: None for h in FAMILY}
    viol = {h: 0 for h in FAMILY}
    K3F = bytearray(1 << 21)
    P3F = bytearray(1 << 21)
    pb3_direct = bytearray(1 << 21)
    kb3_direct = bytearray(1 << 21)
    enc7 = ENC[7]
    for F6 in range(1 << 15):
        F6c = F6 ^ FULL[6]
        tf = TF6[F6]
        tfc = TF6[F6c]
        p3f = P3F6[F6]
        p3fc = P3F6[F6c]
        adj = adj_of(F6, 6)
        adjc = adj_of(F6c, 6)
        comps = COMP6.get(F6, ())
        compsc = COMP6.get(F6c, ())
        for Nv in range(64):
            F = enc7[Nv] | F6
            w = OM7[F]
            a = OM7[F ^ FULL7]
            mm = w if w > a else a
            if F == 0:
                mc['K2'] += 1
                mmin['K2'], marg['K2'] = mm, F
                if mm < ISQRT7:
                    viol['K2'] += 1
            if F == FULL7:
                mc['Kb2'] += 1
                mmin['Kb2'], marg['Kb2'] = mm, F
                if mm < ISQRT7:
                    viol['Kb2'] += 1
            if tf:
                x = Nv
                ok = True
                while x:
                    b = x & (-x)
                    v = b.bit_length() - 1
                    if adj[v] & Nv:
                        ok = False
                        break
                    x ^= b
                if ok:
                    mc['K3'] += 1
                    K3F[F] = 1
                    if mmin['K3'] is None or mm < mmin['K3']:
                        mmin['K3'], marg['K3'] = mm, F
                    if mm < ISQRT7:
                        viol['K3'] += 1
            Nvc = Nv ^ 63
            if tfc:
                x = Nvc
                ok = True
                while x:
                    b = x & (-x)
                    v = b.bit_length() - 1
                    if adjc[v] & Nvc:
                        ok = False
                        break
                    x ^= b
                if ok:
                    mc['Kb3'] += 1
                    kb3_direct[F] = 1
                    if mmin['Kb3'] is None or mm < mmin['Kb3']:
                        mmin['Kb3'], marg['Kb3'] = mm, F
                    if mm < ISQRT7:
                        viol['Kb3'] += 1
            if p3f and (Nv == 0 or Nv in comps):
                mc['P3'] += 1
                P3F[F] = 1
                if mmin['P3'] is None or mm < mmin['P3']:
                    mmin['P3'], marg['P3'] = mm, F
                if mm < ISQRT7:
                    viol['P3'] += 1
            if p3fc and (Nvc == 0 or Nvc in compsc):
                mc['Pb3'] += 1
                pb3_direct[F] = 1
                if mmin['Pb3'] is None or mm < mmin['Pb3']:
                    mmin['Pb3'], marg['Pb3'] = mm, F
                if mm < ISQRT7:
                    viol['Pb3'] += 1
    for h in FAMILY:
        if viol[h]:
            fail("n=7 SHARP violation for %s-free: %d graphs" % (h, viol[h]))
    print("  counts: K1=0 K2=%d Kb2=%d P3=%d Pb3=%d K3=%d Kb3=%d"
          % (mc['K2'], mc['Kb2'], mc['P3'], mc['Pb3'], mc['K3'], mc['Kb3']))
    print("  frontier min max(w,a): %s"
          % {h: mmin[h] for h in FAMILY if mmin[h] is not None})
    if mc['P3'] != BELL[7]:
        fail("n=7 P3-free count %d != Bell(7)=877" % mc['P3'])
    if mc['Pb3'] != BELL[7]:
        fail("n=7 Pb3-free count != 877")
    if mc['K3'] != mc['Kb3']:
        fail("n=7 K3/Kb3 counts differ")

    print(stamp() + " [N7] complement identities over the WHOLE 2^21 space")
    bad = 0
    for F in range(1 << 21):
        if K3F[F ^ FULL7] != kb3_direct[F]:
            bad += 1
            if bad <= 3:
                fail("Kb3 identity broken at F=%d" % F)
        if P3F[F ^ FULL7] != pb3_direct[F]:
            bad += 1
            if bad <= 3:
                fail("Pb3 identity broken at F=%d" % F)
    print("  identity violations: %d" % bad)
    if bad:
        fail("complement identities broken")

    print(stamp() + " [N7] engine C: naive triple scan over ALL 2^21 graphs"
          " (independent K3-free recount)")
    cnt = 0
    dec7 = DEC[7]
    for F6 in range(1 << 15):
        adj6 = adj_of(F6, 6)
        for T in range(64):
            Nv = dec7[T]
            adj7 = [adj6[v] | (64 if (Nv >> v) & 1 else 0) for v in range(6)]
            adj7.append(Nv)
            if triangle_free_direct(adj7, 7):
                cnt += 1
                F = (T << 15) | F6
                if not K3F[F]:
                    fail("triple scan found K3-free graph missed by DP: F=%d" % F)
    if cnt != mc['K3']:
        fail("K3-free n=7: triple scan %d != master %d" % (cnt, mc['K3']))
    print("  triangle-free n=7 by naive triple scan: %d (== master)" % cnt)

    print(stamp() + " [N7] P3-free: partition engine (877) vs master flag set")
    p3_part = set()
    bad = 0
    for pi in set_partitions(range(7)):
        adj = [0] * 7
        for block in pi:
            for u, v in combinations(block, 2):
                adj[u] |= 1 << v
                adj[v] |= 1 << u
        F = mask_from_adj(adj, 7)
        p3_part.add(F)
        w = omega_bb(adj, 7)
        a = alpha_bb(adj, 7)
        if w != max(len(b) for b in pi) or a != len(pi):
            bad += 1
            if bad <= 3:
                fail("cluster omega/alpha != block structure at F=%d" % F)
        if OM7[F] != w or OM7[F ^ FULL7] != a:
            bad += 1
            if bad <= 3:
                fail("cluster omega/alpha disagrees with OM7 at F=%d" % F)
    master_p3 = {F for F in range(1 << 21) if P3F[F]}
    if p3_part != master_p3:
        fail("P3-free n=7: partition set != master flag set (%d vs %d)"
             % (len(p3_part), len(master_p3)))
    if bad:
        fail("P3 partition engine checks failed")
    print("  partition engine: %d graphs, set-equal to master, omega=="
          "maxblock, alpha==#blocks -- OK" % len(p3_part))
    print("E61_N7_FULL_CENSUS_GREEN")
    return OM7, mc, mmin, marg


# =====================================================================
# SECTION 4 -- cograph machinery (labeled Seinsche + unlabeled cotrees).
# =====================================================================

def seinsche_labeled(n):
    """All labeled cographs (P4-free graphs) on {0..n-1} as level-n masks,
    by the Seinsche recursion (disjoint union / join from K1)."""
    memo = {}

    def cog(vs):
        key = frozenset(vs)
        if key in memo:
            return memo[key]
        vs = sorted(key)
        if len(vs) == 1:
            res = {0}
            memo[key] = res
            return res
        res = set()
        pi_index = PI[n]
        for pi in set_partitions(vs):
            if len(pi) < 2:
                continue
            cross = 0
            for i in range(len(pi)):
                for j in range(i + 1, len(pi)):
                    for u in pi[i]:
                        for v in pi[j]:
                            cross |= 1 << pi_index[(min(u, v), max(u, v))]
            opts = [cog(b) for b in pi]
            for combo in product(*opts):
                mu = 0
                for msk in combo:
                    mu |= msk
                res.add(mu)
                res.add(mu | cross)
        memo[key] = res
        return res

    return cog(range(n))


# ---- reduced cotree (unlabeled cograph classes) ----
# tree: ('L',) | ('U', children) | ('J', children); children sorted by key,
# internal nodes have >= 2 children, U children are leaves or J nodes,
# J children are leaves or U nodes (reduced/alternating cotree).
# DISC(n)     = U over multisets of >= 2 connected classes (total size n).
# CONN(n>=2)  = J over multisets of >= 2 classes from {K1} U DISC.
# Uniqueness of the reduced cotree => each unlabeled cograph exactly once.

def tree_key(t):
    if t[0] == 'L':
        return 'L'
    return t[0] + '(' + ','.join(tree_key(c) for c in t[1]) + ')'


def make_node(op, children):
    return (op, sorted(children, key=tree_key))


def node_data(t):
    """(n, omega, alpha, aut) of the cograph class given by tree t."""
    if t[0] == 'L':
        return 1, 1, 1, 1
    ns = [node_data(c) for c in t[1]]
    n = sum(d[0] for d in ns)
    if t[0] == 'U':
        w = max(d[1] for d in ns)
        a = sum(d[2] for d in ns)
    else:
        w = sum(d[1] for d in ns)
        a = max(d[2] for d in ns)
    aut = 1
    ch = t[1]
    i = 0
    while i < len(ch):
        mult = 1
        cur = node_data(ch[i])[3]
        j = i
        while j + 1 < len(ch) and tree_key(ch[j + 1]) == tree_key(ch[i]):
            j += 1
            mult += 1
            cur *= node_data(ch[j])[3]
        for r in range(2, mult + 1):
            aut *= r
        aut *= cur
        i = j + 1
    return n, w, a, aut


def tree_to_adj(t):
    edges = set()
    cnt = [0]

    def rec(t):
        if t[0] == 'L':
            v = cnt[0]
            cnt[0] += 1
            return [v]
        verts = [rec(c) for c in t[1]]
        if t[0] == 'J':
            for i in range(len(verts)):
                for j in range(i + 1, len(verts)):
                    for u in verts[i]:
                        for w in verts[j]:
                            edges.add((min(u, w), max(u, w)))
        return [v for vs in verts for v in vs]

    rec(t)
    n = cnt[0]
    adj = [0] * n
    for (u, v) in edges:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    return n, adj


def multiset_combos(items, lo, rem, acc, out):
    """All multisets (item-index lists, non-decreasing) from items
    (list of (size, key, tree)) with total size exactly rem."""
    if rem == 0:
        if acc:
            out.append(list(acc))
        return
    for i in range(lo, len(items)):
        sz = items[i][0]
        if sz > rem:
            continue
        acc.append(items[i])
        multiset_combos(items, i, rem - sz, acc, out)
        acc.pop()


def cograph_classes(nmax):
    """Unlabeled cograph classes for n=1..nmax: dict n -> {key: tree}."""
    leaf = ('L',)
    G = {1: {tree_key(leaf): leaf}}
    DISC = {}
    CONN = {1: {tree_key(leaf): leaf}}
    for n in range(2, nmax + 1):
        conn_items = []
        for s in range(1, n):
            for key, t in CONN[s].items():
                conn_items.append((node_data(t)[0], key, t))
        conn_items.sort(key=lambda it: it[1])
        disc_new = {}
        combos = []
        multiset_combos(conn_items, 0, n, [], combos)
        for combo in combos:
            assert len(combo) >= 2
            t = make_node('U', [c[2] for c in combo])
            disc_new[tree_key(t)] = t
        base_items = [(1, 'L', leaf)]
        for s in range(2, n):
            for key, t in DISC[s].items():
                base_items.append((node_data(t)[0], key, t))
        base_items.sort(key=lambda it: it[1])
        conn_new = {}
        combos = []
        multiset_combos(base_items, 0, n, [], combos)
        for combo in combos:
            assert len(combo) >= 2
            t = make_node('J', [c[2] for c in combo])
            conn_new[tree_key(t)] = t
        DISC[n] = disc_new
        CONN[n] = conn_new
        gn = dict(disc_new)
        for k, t in conn_new.items():
            if k in gn:
                raise AssertionError("DISC/CONN key collision " + k)
            gn[k] = t
        G[n] = gn
    return G


def census_p4(OM7):
    print(stamp() + " [P4] labeled Seinsche cographs n=1..8")
    lab = {}
    for n in range(1, 9):
        lab[n] = seinsche_labeled(n)
        print("  n=%d labeled cographs: %d" % (n, len(lab[n])))
    if (len(lab[1]), len(lab[2]), len(lab[3]), len(lab[4])) != (1, 2, 8, 52):
        fail("labeled cograph base counts wrong (expect 1,2,8,52)")
    if sum(len(lab[n]) for n in range(1, 7)) != BANKED_NLE6['P4']:
        fail("labeled cographs n<=6 cumulative != banked 6039")

    print(stamp() + " [P4] unlabeled cotree classes n=1..9 + direct"
          " per-class verification")
    G = cograph_classes(9)
    class_counts = {}
    frontier = {}
    for n in range(1, 10):
        classes = G[n]
        class_counts[n] = len(classes)
        bad = 0
        minmax = None
        argmin_key = None
        prodviol = 0
        floorviol = 0
        ceilviol = 0
        ratios = []
        s = isqrt(n)
        ceilv = s if s * s == n else s + 1
        for key, t in classes.items():
            tn, w, a, aut = node_data(t)
            if tn != n:
                fail("class size mismatch at n=%d key=%s" % (n, key))
            nn, adj = tree_to_adj(t)
            if nn != n:
                fail("representative size mismatch at n=%d key=%s" % (n, key))
            wb = omega_bb(adj, n)
            ab = alpha_bb(adj, n)
            if (wb, ab) != (w, a):
                bad += 1
                if bad <= 3:
                    fail("cotree (w,a)=(%d,%d) != B&B (%d,%d) n=%d key=%s"
                         % (w, a, wb, ab, n, key))
            if not p4_free_direct(adj, n):
                bad += 1
                if bad <= 3:
                    fail("class is NOT P4-free: n=%d key=%s" % (n, key))
            comp = components_of(adj, n)
            if n > 1:
                if (len(comp) == 1) != (t[0] == 'J'):
                    bad += 1
                    if bad <= 3:
                        fail("root type vs connectivity mismatch n=%d key=%s"
                             % (n, key))
                if t[0] == 'U' and len(comp) != len(t[1]):
                    bad += 1
                    if bad <= 3:
                        fail("U-node children != components n=%d key=%s"
                             % (n, key))
            mm = max(w, a)
            if w * a < n:
                prodviol += 1
            if mm < isqrt(n):
                floorviol += 1
            if mm < ceilv:
                ceilviol += 1
            if n >= 2:
                ratios.append(log2(mm) / log2(n))
            if minmax is None or mm < minmax:
                minmax = mm
                argmin_key = key
        frontier[n] = {
            'classes': len(classes),
            'min_max_omega_alpha': minmax,
            'argmin_key': argmin_key,
            'min_ratio': min(ratios) if ratios else None,
            'product_law_violations': prodviol,
            'floor_form_violations': floorviol,
            'ceil_form_violations': ceilviol,
        }
        if bad or prodviol or floorviol:
            fail("cograph class verification failed at n=%d (bad=%d prod=%d"
                 " floor=%d)" % (n, bad, prodviol, floorviol))
        mr = frontier[n]['min_ratio']
        print("  n=%d: classes=%d min max(w,a)=%s min_ratio=%s prod-law"
              " viol=%d floor viol=%d ceil viol=%d"
              % (n, len(classes), minmax,
                 ("%.4f" % mr) if mr is not None else "n/a",
                 prodviol, floorviol, ceilviol))
    print("  unlabeled class counts n=1..9: %s"
          % [class_counts[n] for n in range(1, 10)])
    if [class_counts[n] for n in range(1, 5)] != [1, 2, 4, 10]:
        fail("unlabeled cograph counts n<=4 wrong (expect 1,2,4,10)")

    print(stamp() + " [P4] labeled identity labeled(n) == SUM n!/Aut (n<=8)")
    for n in range(1, 9):
        tot = 0
        for key, t in G[n].items():
            tn, w, a, aut = node_data(t)
            tot += factorial(n) // aut
        if tot != len(lab[n]):
            fail("labeled identity broken at n=%d: cotree %d != Seinsche %d"
                 % (n, tot, len(lab[n])))
    print("  identity holds for n=1..8 (two independent engines agree)")

    print(stamp() + " [P4] n=7/n=8 labeled histograms vs class histograms")
    # n=7 via OM7 table
    hist_lab = {}
    for F in lab[7]:
        wa = (OM7[F], OM7[F ^ FULL[7]])
        hist_lab[wa] = hist_lab.get(wa, 0) + 1
    hist_cls = {}
    for key, t in G[7].items():
        tn, w, a, aut = node_data(t)
        wa = (w, a)
        hist_cls[wa] = hist_cls.get(wa, 0) + factorial(7) // aut
    if hist_lab != hist_cls:
        fail("n=7 labeled (omega,alpha) histogram != class histogram")
    # n=7 labeled sharp form via OM7 (full coverage)
    bad = 0
    for F in lab[7]:
        if max(OM7[F], OM7[F ^ FULL[7]]) < isqrt(7):
            bad += 1
    if bad:
        fail("n=7 cograph sharp violations: %d" % bad)
    # n=8 via B&B on every labeled cograph
    bad = 0
    minmax8 = None
    hist_lab8 = {}
    for F in lab[8]:
        adj = adj_of(F, 8)
        w = omega_bb(adj, 8)
        a = alpha_bb(adj, 8)
        hist_lab8[(w, a)] = hist_lab8.get((w, a), 0) + 1
        mm = max(w, a)
        if minmax8 is None or mm < minmax8:
            minmax8 = mm
        if mm < isqrt(8):
            bad += 1
            if bad <= 3:
                fail("n=8 labeled cograph sharp violation at F=%d" % F)
    if bad:
        fail("n=8 labeled cograph sharp violations: %d" % bad)
    hist_cls8 = {}
    for key, t in G[8].items():
        tn, w, a, aut = node_data(t)
        hist_cls8[(w, a)] = hist_cls8.get((w, a), 0) + factorial(8) // aut
    if hist_lab8 != hist_cls8:
        fail("n=8 labeled (omega,alpha) histogram != class histogram")
    if minmax8 != frontier[8]['min_max_omega_alpha']:
        fail("n=8 frontier: labeled min %s != class min %s"
             % (minmax8, frontier[8]['min_max_omega_alpha']))
    print("  n=7: %d labeled, histogram equal, sharp-OK; n=8: %d labeled,"
          " histogram equal, sharp-OK, min max(w,a)=%d"
          % (len(lab[7]), len(lab[8]), minmax8))

    all_ratios = []
    for n in range(2, 10):
        for key, t in G[n].items():
            tn, w, a, aut = node_data(t)
            all_ratios.append(log2(max(w, a)) / log2(n))
    emp = min(all_ratios)
    print("  EMPIRICAL P4 EXPONENT floor over cographs n=2..9: %.6f"
          " (min of log2(max(w,a))/log2(n))" % emp)
    print("E61_P4_FRONTIER_GREEN")
    return lab, G, class_counts, frontier, emp


# =====================================================================
# SECTION 5 -- n=8 census.
# =====================================================================

def census_n8(tf_sets, mc7):
    out = {}
    print(stamp() + " [N8] trivial members: K1-free=0, K2-free=1 (empty),"
          " Kb2-free=1 (complete)")
    empty_adj = [0] * 8
    full_adj = [((1 << 8) - 1) & ~(1 << v) for v in range(8)]
    if not cluster_direct(empty_adj, 8) or omega_bb(empty_adj, 8) != 1 \
            or alpha_bb(empty_adj, 8) != 8:
        fail("n=8 empty graph checks broken")
    if alpha_bb(full_adj, 8) != 1 or omega_bb(full_adj, 8) != 8:
        fail("n=8 complete graph checks broken")
    # uniqueness of the empty/complete witnesses verified over the whole
    # 2^21 space at n=7 (K2-free count was exactly 1 = the empty mask);
    # the n=8 statement is the same edge-free/uniqueness argument plus the
    # direct checks above.
    out['K1'] = 0
    out['K2'] = 1
    out['Kb2'] = 1
    print("  K1=0 K2=1 Kb2=1 (empty/complete direct-checked; uniqueness"
          " verified over all 2^21 graphs at n=7)")

    print(stamp() + " [N8] P3-free: all Bell(8)=4140 partition graphs")
    p3c = 0
    minmax = None
    arg = None
    bad = 0
    for pi in set_partitions(range(8)):
        adj = [0] * 8
        for block in pi:
            for u, v in combinations(block, 2):
                adj[u] |= 1 << v
                adj[v] |= 1 << u
        p3c += 1
        if not cluster_direct(adj, 8):
            bad += 1
            if bad <= 3:
                fail("n=8 partition graph not cluster")
        w = omega_bb(adj, 8)
        a = alpha_bb(adj, 8)
        if w != max(len(b) for b in pi) or a != len(pi):
            bad += 1
            if bad <= 3:
                fail("n=8 cluster omega/alpha != block structure")
        mm = max(w, a)
        if minmax is None or mm < minmax:
            minmax = mm
            arg = sorted(sorted(b) for b in pi)
        if mm < isqrt(8):
            bad += 1
            if bad <= 3:
                fail("n=8 P3-free sharp violation")
    if p3c != BELL[8]:
        fail("n=8 P3-free count %d != Bell(8)=4140" % p3c)
    if bad:
        fail("n=8 P3-free checks failed (%d)" % bad)
    out['P3'] = p3c
    out['P3_minmax'] = minmax
    out['P3_argmin'] = arg
    print("  P3-free: %d graphs, all sharp-OK, min max(w,a)=%d"
          % (p3c, minmax))
    print("  argmin block structure: %s" % arg)

    n7_comp_total = 0
    for pi in set_partitions(range(7)):
        adj = [0] * 7
        for block in pi:
            for u, v in combinations(block, 2):
                adj[u] |= 1 << v
                adj[v] |= 1 << u
        n7_comp_total += len(components_of(adj, 7))
    if n7_comp_total + BELL[7] != BELL[8]:
        fail("P3 n=8 engine B count %d != 4140" % (n7_comp_total + BELL[7]))
    print("  P3 engine B (sum over n=7 cluster graphs of #comp+1): %d OK"
          % (n7_comp_total + BELL[7]))

    print(stamp() + " [N8] Pb3-free: complements of the 4140 cluster graphs")
    pb3c = 0
    minmaxc = None
    bad = 0
    for pi in set_partitions(range(8)):
        adj = [0] * 8
        for block in pi:
            for u, v in combinations(block, 2):
                adj[u] |= 1 << v
                adj[v] |= 1 << u
        comp = [((1 << 8) - 1) & ~adj[v] & ~(1 << v) for v in range(8)]
        pb3c += 1
        if not cluster_direct(comp, 8):
            bad += 1
            if bad <= 3:
                fail("n=8 complement of cluster graph not cluster")
        w = omega_bb(comp, 8)
        a = alpha_bb(comp, 8)
        mm = max(w, a)
        if minmaxc is None or mm < minmaxc:
            minmaxc = mm
        if mm < isqrt(8):
            bad += 1
            if bad <= 3:
                fail("n=8 Pb3-free sharp violation")
    if pb3c != BELL[8] or bad:
        fail("n=8 Pb3-free checks failed (count=%d bad=%d)" % (pb3c, bad))
    out['Pb3'] = pb3c
    out['Pb3_minmax'] = minmaxc
    print("  Pb3-free: %d graphs (complement engine), min max(w,a)=%d"
          % (pb3c, minmaxc))

    print(stamp() + " [N8] K3-free: enumerate ALL labeled triangle-free"
          " graphs on 8 vertices ((tf F7) x (independent set S))")
    tf7 = set()
    enc7 = ENC[7]
    for F6 in tf_sets[6]:
        adj6 = adj_of(F6, 6)
        stack = [(63, 0)]
        while stack:
            cand, S = stack.pop()
            tf7.add(F6 | enc7[S])
            while cand:
                b = cand & (-cand)
                v = b.bit_length() - 1
                cand ^= b
                stack.append((cand & ~adj6[v] & ~b, S | b))
    print("  triangle-free n=7 (DP extension from tf6): %d" % len(tf7))
    if len(tf7) != mc7['K3']:
        fail("tf7 DP count %d != n=7 master K3 count %d"
             % (len(tf7), mc7['K3']))
    bad = 0
    for F in tf7:
        if not triangle_free_direct(adj_of(F, 7), 7):
            bad += 1
            if bad <= 3:
                fail("tf7 member fails direct triple scan: F=%d" % F)
    if bad:
        fail("tf7 re-verification failed (%d)" % bad)
    print("  all %d tf7 members re-verified by direct triple scan" % len(tf7))

    ALPHA7 = {}
    for F in tf7:
        ALPHA7[F] = alpha_bb(adj_of(F, 7), 7)

    T8 = 0
    sharp_bad = 0
    minmax_k3 = None
    argmin = None
    a3_count = 0
    a3_witnesses = []
    a3_deghist = {}
    stride_bad = 0
    stride_checked = 0
    ISQRT8 = isqrt(8)
    idx = 0
    for F7 in tf7:
        adj7 = adj_of(F7, 7)
        a7 = ALPHA7[F7]
        has_edge = F7 != 0
        stack = [(127, 0)]
        while stack:
            cand, S = stack.pop()
            x = S
            okS = True
            while x:
                b = x & (-x)
                v = b.bit_length() - 1
                if adj7[v] & S:
                    okS = False
                    break
                x ^= b
            if not okS:
                fail("IS re-verification failed at F7=%d S=%d" % (F7, S))
            A = 127 & ~S
            if A:
                adjsub = [adj7[v] & A for v in range(7)]
                compsub = [A & ~adjsub[v] & ~(1 << v) for v in range(7)]
                a_rest = omega_on(compsub, A)
            else:
                a_rest = 0
            alpha8 = a7 if a7 >= 1 + a_rest else 1 + a_rest
            w8 = 2 if (has_edge or S) else 1
            mm = w8 if w8 > alpha8 else alpha8
            T8 += 1
            if mm < ISQRT8:
                sharp_bad += 1
                if sharp_bad <= 3:
                    fail("n=8 K3-free sharp violation F7=%d S=%d mm=%d"
                         % (F7, S, mm))
            if minmax_k3 is None or mm < minmax_k3:
                minmax_k3 = mm
                argmin = (F7, S)
            if alpha8 == 3:
                a3_count += 1
                adj8 = [adj7[v] | (128 if (S >> v) & 1 else 0)
                        for v in range(7)]
                adj8.append(S)
                degs = tuple(sorted(pc(adj8[v]) for v in range(8)))
                a3_deghist[degs] = a3_deghist.get(degs, 0) + 1
                if len(a3_witnesses) < 8:
                    a3_witnesses.append(adj8)
            if idx % 128 == 0 or alpha8 == 3:
                adj8 = [adj7[v] | (128 if (S >> v) & 1 else 0)
                        for v in range(7)]
                adj8.append(S)
                if not triangle_free_direct(adj8, 8):
                    stride_bad += 1
                    if stride_bad <= 3:
                        fail("stride re-check: not triangle-free F7=%d S=%d"
                             % (F7, S))
                wb = omega_bb(adj8, 8)
                ab = alpha_bb(adj8, 8)
                if (wb, ab) != (w8, alpha8):
                    stride_bad += 1
                    if stride_bad <= 3:
                        fail("stride re-check: (w,a) mismatch F7=%d S=%d"
                             " (%d,%d) vs (%d,%d)"
                             % (F7, S, wb, ab, w8, alpha8))
                stride_checked += 1
            while cand:
                b = cand & (-cand)
                v = b.bit_length() - 1
                cand ^= b
                stack.append((cand & ~adj7[v] & ~b, S | b))
            idx += 1
    print("  K3-free n=8 labeled count: %d" % T8)
    print("  sharp violations: %d; full re-checks (stride 1/128 + all"
          " alpha=3): %d (bad %d)" % (sharp_bad, stride_checked, stride_bad))
    print("  frontier min max(w,a) = %s; graphs with alpha=3: %d"
          % (minmax_k3, a3_count))
    print("  alpha=3 degree-sequence histogram: %s"
          % {str(list(k)): v for k, v in sorted(a3_deghist.items())})
    if sharp_bad or stride_bad:
        fail("n=8 K3-free census failed")
    if minmax_k3 != 3:
        print("  NOTE: frontier min max(w,a) = %s (R(3,3)=6 forces alpha>=3"
              " on triangle-free graphs)" % minmax_k3)
    out['K3'] = T8
    out['K3_minmax'] = minmax_k3
    out['K3_alpha3_count'] = a3_count
    out['K3_argmin'] = argmin
    out['K3_witness_adj'] = a3_witnesses[0] if a3_witnesses else None
    out['Kb3'] = T8
    out['Kb3_minmax'] = minmax_k3
    print("  Kb3-free n=8 = %d by the complement bijection (flag identity"
          " verified over all 2^21 n=7 graphs); frontier identical"
          " (max(w,a) complement-invariant)" % T8)
    print("E61_N8_CENSUS_GREEN")
    return out


# =====================================================================
# SECTION 6 -- tightness witnesses j=1..5.
# =====================================================================

def tightness():
    print(stamp() + " [TIGHT] disjoint union of 2^j copies of K_{2^j},"
          " j=1..5: omega=alpha=2^j=isqrt(4^j) EXACTLY")
    rows = []
    bad = 0
    for j in range(1, 6):
        k = 1 << j          # clique size = number of copies = 2^j
        n = k * k           # 4^j
        adj = [0] * n
        for c in range(k):
            base = c * k
            for u in range(k):
                for v in range(u + 1, k):
                    adj[base + u] |= 1 << (base + v)
                    adj[base + v] |= 1 << (base + u)
        w = omega_bb(adj, n)
        a = alpha_bb(adj, n)
        s = isqrt(n)
        p3 = cluster_direct(adj, n)
        pb3 = True
        for u in range(n):
            for v in range(u + 1, n):
                same = (u // k) == (v // k)
                adj_uv = (adj[u] >> v) & 1
                if same != (not adj_uv):
                    pb3 = False
                    break
            if not pb3:
                break
        p4ok = True if n > 64 else p4_free_direct(adj, n)
        row_ok = (n == (1 << (2 * j)) and s == k and w == k and a == k
                  and p3 and pb3 and p4ok and max(w, a) == s)
        if not row_ok:
            bad += 1
            fail("tightness witness j=%d broken: n=%d w=%d a=%d isqrt=%d"
                 " p3=%s pb3=%s p4=%s" % (j, n, w, a, s, p3, pb3, p4ok))
        rows.append({'j': j, 'k': k, 'n': n, 'omega': w, 'alpha': a,
                     'isqrt_n': s, 'P3free': bool(p3), 'Pbar3free': bool(pb3),
                     'tight': bool(row_ok)})
        print("  j=%d: n=%d omega=%d alpha=%d isqrt(n)=%d -- max(w,a) =="
              " isqrt(n) EXACTLY (P3-free=%s Pbar3-free=%s P4-free=%s)"
              % (j, n, w, a, s, p3, pb3,
                 p4ok if n <= 64 else 'structural'))
    if bad:
        fail("tightness witnesses broken")
    print("TIGHT_WITNESS_GREEN")
    return rows


# =====================================================================
# MAIN
# =====================================================================

def main():
    print("ESCALATION BATTERY W69-D -- Erdos #61 doubter lane round 3")
    print("=" * 74)
    self_test_core()
    counts6, tf_sets, p3_sets, p4_sets = build_level_tables()
    OM7, mc7, mmin7, marg7 = census_n7(tf_sets[6])
    lab, G, class_counts, frontier, emp = census_p4(OM7)
    n8 = census_n8(tf_sets, mc7)
    tight_rows = tightness()

    print("=" * 74)
    bank = {
        'n7': {
            'space_size': 1 << 21,
            'counts': {h: mc7[h] for h in FAMILY},
            'frontier_minmax': {h: mmin7[h] for h in FAMILY},
            'isqrt7': isqrt(7),
        },
        'n8': {
            'counts': {h: n8.get(h) for h in FAMILY},
            'frontier_minmax': {
                'P3': n8.get('P3_minmax'), 'Pb3': n8.get('Pb3_minmax'),
                'K3': n8.get('K3_minmax'), 'Kb3': n8.get('Kb3_minmax')},
            'K3_alpha3_count': n8.get('K3_alpha3_count'),
            'isqrt8': isqrt(8),
        },
        'p4': {
            'labeled_counts': {str(n): len(lab[n]) for n in range(1, 9)},
            'unlabeled_classes': {str(n): class_counts[n]
                                  for n in range(1, 10)},
            'frontier': {str(n): frontier[n] for n in range(1, 10)},
            'empirical_exponent': emp,
        },
        'tightness': tight_rows,
    }
    with open('census_w69d.json', 'w') as f:
        json.dump(bank, f, indent=1, default=str)
    print("census_w69d.json banked")

    if FAIL:
        print("ESCALATION VERDICT: RED (%d failures)" % len(FAIL))
        for msg in FAIL[:20]:
            print("  - " + msg)
        sys.exit(1)
    print("ESCALATION VERDICT: GREEN -- zero violations across the n=7 full"
          " census (all 2^21 graphs), the n=8 member censuses, the P4"
          " frontier n<=9, and tightness j=1..5")
    print("E61_DOUBTER_W69D_GREEN")
    sys.exit(0)


if __name__ == '__main__':
    main()
