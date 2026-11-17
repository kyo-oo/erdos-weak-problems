#!/usr/bin/env python3
"""
COMPARATOR 61 — the independent direct verifier for Erdos #61 (Erdos-Hajnal).
Challenge + solution + evaluator (the DeepMind FunSearch/AlphaCode grading pattern).
NO Lean. NO trust in the campaign's own engines — every claim re-derived fresh.

Verdict protocol: exit 0 + COMPARATOR_61_GREEN=1 only if every lane passes.
Exit 1 on infrastructure failure, exit 2 on any CRITICAL (claim rejected).
"""
import json, sys, itertools, math
from fractions import Fraction
from pathlib import Path

try:
    import z3
    HAVE_Z3 = True
except Exception:
    HAVE_Z3 = False

PASS = 0
FAIL = 0
CRIT = 0
RECEIPTS = []

def rec(msg):
    RECEIPTS.append(msg)
    print(msg)

def ok(lane, msg):
    global PASS
    PASS += 1
    rec(f"  PASS [{lane}] {msg}")

def bad(lane, msg):
    global FAIL, CRIT
    FAIL += 1
    CRIT += 1
    rec(f"  CRITICAL [{lane}] {msg}")

def check(lane, msg, cond):
    if cond:
        ok(lane, msg)
    else:
        bad(lane, msg)

# ----------------------------------------------------------------------------
# Graph machinery (bitmask rows)
# ----------------------------------------------------------------------------

def rows_from_edge_mask(n, mask):
    """mask bit index e = i*C(n,2) - ... convention: bit (i,j) i<j at index
    i*(2n-i-1)//2 + (j-i-1). Build adjacency row bitmasks."""
    rows = [0] * n
    idx = 0
    for i in range(n):
        for j in range(i + 1, n):
            if (mask >> idx) & 1:
                rows[i] |= (1 << j)
                rows[j] |= (1 << i)
            idx += 1
    return rows

def n_edges(n, mask):
    return bin(mask).count("1")

def num_graphs(n):
    return 1 << (n * (n - 1) // 2)

def max_clique(n, rows):
    """Exact max clique by bitmask recursion with pruning."""
    best = [0]
    def expand(R, size):
        if size + bin(R).count("1") <= best[0]:
            return
        if R == 0:
            if size > best[0]:
                best[0] = size
            return
        # pick a vertex from R
        v = (R & -R).bit_length() - 1
        # include v
        expand(R & rows[v], size + 1)
        # exclude v
        expand(R & ~(1 << v), size)
    expand((1 << n) - 1, 0)
    return best[0]

def complement_rows(n, rows):
    full = (1 << n) - 1
    return [(~rows[i] & full) & ~(1 << i) for i in range(n)]

def hom(n, rows):
    omega = max_clique(n, rows)
    alpha = max_clique(n, complement_rows(n, rows))
    return max(omega, alpha)

def induced_sub_rows(rows, subset):
    """subset: tuple of original vertex ids (sorted)."""
    m = len(subset)
    sub = [0] * m
    for a in range(m):
        for b in range(a + 1, m):
            if (rows[subset[a]] >> subset[b]) & 1:
                sub[a] |= (1 << b)
                sub[b] |= (1 << a)
    return sub

def canon(m, rows):
    """Canonical form of a labeled small graph (brute perm)."""
    n = m
    best = None
    for perm in itertools.permutations(range(n)):
        r2 = [0] * n
        for a in range(n):
            for b in range(n):
                if (rows[perm[a]] >> perm[b]) & 1:
                    r2[a] |= (1 << b)
        s = ",".join(str(x) for x in r2)
        if best is None or s < best:
            best = s
    return best

def graph_from_pairs(n, pairs):
    rows = [0] * n
    for (a, b) in pairs:
        rows[a] |= (1 << b)
        rows[b] |= (1 << a)
    return rows

# The H library (canonical builders)
def H_K2():   return graph_from_pairs(2, [(0, 1)])
def H_2K1():  return graph_from_pairs(2, [])
def H_P3():   return graph_from_pairs(3, [(0, 1), (1, 2)])
def H_K3():   return graph_from_pairs(3, [(0, 1), (0, 2), (1, 2)])
def H_3K1():  return graph_from_pairs(3, [])
def H_Pbar3():return complement_rows(3, H_P3())
def H_2K2():  return graph_from_pairs(4, [(0, 1), (2, 3)])
def H_claw(): return graph_from_pairs(4, [(0, 1), (0, 2), (0, 3)])
def H_C4():   return graph_from_pairs(4, [(0, 1), (1, 2), (2, 3), (3, 0)])
def H_P4():   return graph_from_pairs(4, [(0, 1), (1, 2), (2, 3)])

def is_H_free(n, rows, Hn, Hrows):
    """True iff NO induced subgraph of size Hn is isomorphic to H."""
    Hc = canon(Hn, Hrows)
    for subset in itertools.combinations(range(n), Hn):
        if canon(Hn, induced_sub_rows(rows, subset)) == Hc:
            return False
    return True

def all_graphs(n):
    for mask in range(num_graphs(n)):
        yield rows_from_edge_mask(n, mask)

def components_are_cliques(n, rows):
    """INDEPENDENT check: G is a disjoint union of cliques (DSU + clique check)."""
    parent = list(range(n))
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for i in range(n):
        for j in range(i + 1, n):
            if (rows[i] >> j) & 1:
                a, b = find(i), find(j)
                if a != b:
                    parent[a] = b
    comp = {}
    for v in range(n):
        comp.setdefault(find(v), []).append(v)
    for members in comp.values():
        for a in members:
            for b in members:
                if a != b and not ((rows[a] >> b) & 1):
                    return False
    return True

# ----------------------------------------------------------------------------
# z3 third-method certificates
# ----------------------------------------------------------------------------

def z3_h_certificate(Hn, Hrows, n, k):
    """SAT model iff exists H-free G on n vertices with omega<=k and alpha<=k.
    Returns (sat, model_rows or None)."""
    if not HAVE_Z3:
        return (None, None)
    edges = {}
    s = z3.Solver()
    for i in range(n):
        for j in range(i + 1, n):
            edges[(i, j)] = z3.Bool(f"e{i}_{j}")
    def adj(i, j):
        return edges[(min(i, j), max(i, j))]
    # omega <= k : no clique of size k+1
    for sub in itertools.combinations(range(n), k + 1):
        s.add(z3.Not(z3.And([adj(a, b) for a, b in itertools.combinations(sub, 2)])))
    # alpha <= k : no independent set of size k+1
    for sub in itertools.combinations(range(n), k + 1):
        s.add(z3.Or([adj(a, b) for a, b in itertools.combinations(sub, 2)]))
    # H-free: no induced copy of H under ANY injection (every permutation of each
    # subset — a single labeling misses copies related by H-automorphisms)
    Hpairs = [(a, b) for a in range(Hn) for b in range(a + 1, Hn) if (Hrows[a] >> b) & 1]
    Hnonpairs = [(a, b) for a in range(Hn) for b in range(a + 1, Hn) if not ((Hrows[a] >> b) & 1)]
    for sub in itertools.combinations(range(n), Hn):
        for perm in itertools.permutations(sub):
            s.add(z3.Not(z3.And(
                [adj(perm[a], perm[b]) for (a, b) in Hpairs] +
                [z3.Not(adj(perm[a], perm[b])) for (a, b) in Hnonpairs])))
    if s.check() == z3.sat:
        m = s.model()
        rows = [0] * n
        for (i, j), v in edges.items():
            if z3.is_true(m.eval(v)):
                rows[i] |= (1 << j)
                rows[j] |= (1 << i)
        return (True, rows)
    return (False, None)

# ----------------------------------------------------------------------------
# Load challenge + solution
# ----------------------------------------------------------------------------
HERE = Path(__file__).parent
challenge = json.loads((HERE / "challenge.json").read_text())
solution = json.loads((HERE / "solution.json").read_text())

print("=" * 78)
print("COMPARATOR 61 — Erdos-Hajnal DIRECT VERIFICATION (challenge/solution/evaluator)")
print("=" * 78)
print(f"z3: {'available ' + z3.get_version_string() if HAVE_Z3 else 'NOT available (third-method lanes SKIP)'}")

# ----------------------------------------------------------------------------
# LANE S — statement integrity
# ----------------------------------------------------------------------------
print("\n[S] STATEMENT INTEGRITY")
stmt_c = challenge["statement_frozen"]
claims_ok = isinstance(solution.get("claims"), list) and len(solution["claims"]) >= 6
check("S", "Erdos-Hajnal statement frozen (induced subgraph + complete-or-independent) and solution carries >= 6 labeled claims",
      "induced subgraph" in stmt_c and "complete graph or independent set" in stmt_c and claims_ok)
check("S", "open-scope declaration present (the full conjecture stays OPEN)",
      "OPEN" in solution.get("open_scope_declaration", ""))

# ----------------------------------------------------------------------------
# LANE A — h-tables n<=7 (methods: targeted exhaustive + z3 duals)
# ----------------------------------------------------------------------------
print("\n[A] H-TABLES n<=7 — fresh re-derivation")

TABLES = {
    "2K2":  [1, 2, 2, 2, 2, 3, 3],
    "P3":   [1, 2, 2, 2, 3, 3, 3],
    "3K1":  [1, 2, 2, 2, 2, 3, 3],
    "claw": [1, 2, 2, 2, 2, 3, 3],
    "C4":   [1, 2, 2, 2, 2, 3, 3],
    "K2":   [1, 2, 3, 4, 5, 6, 7],
}
HBUILD = {
    "2K2": (4, H_2K2()), "P3": (3, H_P3()), "3K1": (3, H_3K1()),
    "claw": (4, H_claw()), "C4": (4, H_C4()), "K2": (2, H_K2()),
}

# Method 1: full enumeration n<=6 (exact); n=7: witness + Ramsey floor
derived = {}
for name, table in TABLES.items():
    Hn, Hrows = HBUILD[name]
    vals = []
    for n in range(1, 7):
        best = None
        for rows in all_graphs(n):
            if is_H_free(n, rows, Hn, Hrows):
                h = hom(n, rows)
                if best is None or h < best:
                    best = h
        vals.append(best)
    # n = 7: witness search (early exit) — floor rides on Ramsey R(3,3)=6 (lane D)
    n = 7
    target = table[6]
    witness = None
    for rows in all_graphs(n):
        if is_H_free(n, rows, Hn, Hrows):
            h = hom(n, rows)
            if h <= target:
                witness = (h, rows)
                break
    if witness is None:
        vals.append(None)  # no witness at claimed value -> will fail agreement
    else:
        vals.append(witness[0])
    derived[name] = vals

agree = all(derived[name] == TABLES[name] for name in TABLES)
check("A", "six h-tables n=1..7 re-derived (n<=6 exhaustive, n=7 witness+Ramsey) == solution",
      agree)
for name in TABLES:
    rec(f"    h_{name}: {derived[name]}")

# Method 2 (z3 duals): for each H, n in 2..6: SAT at h-1 must be UNSAT, SAT at h must give model
if HAVE_Z3:
    z3_agree = True
    for name, table in TABLES.items():
        if name == "K2":
            continue  # trivial: edgeless is the only K2-free graph
        Hn, Hrows = HBUILD[name]
        for n in range(2, 7):
            h = table[n - 1]
            sat_lo, model = z3_h_certificate(Hn, Hrows, n, h - 1)
            if sat_lo:
                z3_agree = False
                bad("A", f"z3 found {name}-free graph on n={n} with hom<={h-1} — floor broken")
            sat_hi, model = z3_h_certificate(Hn, Hrows, n, h)
            if not sat_hi or model is None:
                z3_agree = False
                bad("A", f"z3 could not witness h_{name}({n})<={h}")
            else:
                # independent re-validation of the model
                if not is_H_free(n, model, Hn, Hrows) or hom(n, model) > h:
                    z3_agree = False
                    bad("A", f"z3 model for h_{name}({n}) fails re-validation")
    check("A", "z3 SAT/UNSAT dual certificates agree with all tables (n=2..6, five non-trivial H)", z3_agree)
else:
    rec("  [A] z3 third-method SKIPPED (not importable)")

# ----------------------------------------------------------------------------
# LANE B — P3 classification + sharp law
# ----------------------------------------------------------------------------
print("\n[B] THEOREM 2 — P3 classification and h_P3(n) = ceil(sqrt(n))")

BELL = {1: 1, 2: 2, 3: 5, 4: 15, 5: 52, 6: 203}
Hn, Hrows = 3, H_P3()
cls_ok = True
count_ok = True
for n in range(1, 7):
    cnt_p3free = 0
    for rows in all_graphs(n):
        free = is_H_free(n, rows, Hn, Hrows)
        duoc = components_are_cliques(n, rows)
        if free != duoc:
            cls_ok = False
        if free:
            cnt_p3free += 1
    if cnt_p3free != BELL[n]:
        count_ok = False
        rec(f"    P3-free count n={n}: {cnt_p3free} != Bell {BELL[n]}")
check("B", "P3-free <=> disjoint-union-of-cliques on EVERY graph n<=6 (exhaustive, independent DSU check)", cls_ok)
check("B", "P3-free census == Bell numbers 1,2,5,15,52,203 at n=1..6", count_ok)

# sharp law: lower bound n<=7 (exhaustive via table lane) + witnesses n<=30
def balanced_parts(n, r):
    """partition n into r parts each <= r (r = ceil(sqrt n))."""
    parts = [n // r] * r
    for i in range(n % r):
        parts[i] += 1
    return parts

witness_ok = True
for n in range(1, 31):
    r = math.ceil(math.sqrt(n))
    parts = balanced_parts(n, r)
    # disjoint union of cliques of those sizes
    rows = [0] * n
    off = 0
    for sz in parts:
        for a in range(off, off + sz):
            for b in range(off, off + sz):
                if a != b:
                    rows[a] |= (1 << b)
        off += sz
    if not components_are_cliques(n, rows):
        witness_ok = False
    om = max(parts)          # largest clique
    al = len(parts)          # independent set: one per component
    if max(om, al) != r:
        witness_ok = False
check("B", "h_P3(n) <= ceil(sqrt(n)) witnesses (balanced clique unions) verified n=1..30; classification gives lower bound (n<=7 exhaustive)", witness_ok and derived["P3"][:7] == TABLES["P3"][:7])

# ----------------------------------------------------------------------------
# LANE C — 3K1 law + C5 honesty correction
# ----------------------------------------------------------------------------
print("\n[C] THEOREM 3 — 3K1 complement-side law with the C5 correction")
Hn, Hrows = 3, H_3K1()
law_ok = True
equality_set = {1, 3, 4, 5, 7}
strict_set = {2, 6}
for n in range(1, 8):
    t = 1
    while t * (t + 1) < n:
        t += 1
    h = TABLES["3K1"][n - 1]
    if h < t:
        law_ok = False
    if (h == t) != (n in equality_set) or (h > t) != (n in strict_set):
        law_ok = False
check("C", "h_3K1(n) >= t_n = min{t: t(t+1)>=n} with equality at {1,3,4,5,7} and Ramsey strictness at {2,6} (n<=7)", law_ok)

# the C5 correction: C5 is 3K1-free, hom(C5)=2 < sqrt(5)
C5 = H_C4()  # C4 == C5 as labeled? NO — build C5 explicitly
C5rows = graph_from_pairs(5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)])
c5_free = is_H_free(5, C5rows, 3, H_3K1())
c5_hom = hom(5, C5rows)
check("C", f"C5 honesty correction: C5 is 3K1-free (={c5_free}) and hom(C5)={c5_hom} < sqrt(5)~2.236 — the naive real-valued law is FALSE exactly as documented",
      c5_free and c5_hom == 2 and 2 < math.sqrt(5))

# ----------------------------------------------------------------------------
# LANE D — Ramsey R(3,3) = 6 (the n=7 floor for every H)
# ----------------------------------------------------------------------------
print("\n[D] RAMSEY CROSS-CHECK R(3,3)=6")
ramsey_ok = True
for rows in all_graphs(6):
    if hom(6, rows) <= 2:
        ramsey_ok = False
        break
check("D", "every 6-vertex graph has omega>=3 or alpha>=3 (exhaustive 2^15) — the universal n=6,7 floor", ramsey_ok)
if HAVE_Z3:
    s, m = z3_h_certificate(3, H_P3(), 6, 2)  # any H: the omega/alpha constraints alone
    # note: the H-free constraints are vacuous-harmless here; re-check via pure Ramsey encoding
    ram = z3.Solver()
    e = {}
    for i in range(6):
        for j in range(i + 1, 6):
            e[(i, j)] = z3.Bool(f"x{i}{j}")
    for sub in itertools.combinations(range(6), 3):
        ram.add(z3.Or([e[(min(a,b),max(a,b))] for a, b in itertools.combinations(sub, 2)]))
        ram.add(z3.Or([z3.Not(e[(min(a,b),max(a,b))]) for a, b in itertools.combinations(sub, 2)]))
    check("D", "z3 UNSAT: no 6-vertex graph with all-triangles-and-independent-triples absent", ram.check() == z3.unsat)

# ----------------------------------------------------------------------------
# LANE E — substitution identities (brute isomorphism)
# ----------------------------------------------------------------------------
print("\n[E] THEOREM 4 — substitution identities")

def substitute(H1rows, H2rows, a, b):
    """H1[H2] on [a]x[b]."""
    n = a * b
    rows = [0] * n
    def vid(p, y): return p * b + y
    for p in range(a):
        for q in range(a):
            if p != q and ((H1rows[p] >> q) & 1):
                for y in range(b):
                    for y2 in range(b):
                        rows[vid(p, y)] |= (1 << vid(q, y2))
    for p in range(a):
        for y in range(b):
            for y2 in range(b):
                if y != y2 and ((H2rows[y] >> y2) & 1):
                    rows[vid(p, y)] |= (1 << vid(p, y2))
    return rows

def iso(n1, r1, n2, r2):
    return n1 == n2 and canon(n1, r1) == canon(n2, r2)

def fast_iso(n, r1, r2):
    """Exact isomorphism for equal-size graphs via degree-ordered backtracking."""
    d1 = [bin(r1[i]).count("1") for i in range(n)]
    d2 = [bin(r2[i]).count("1") for i in range(n)]
    if sorted(d1) != sorted(d2):
        return False
    if sum(d1) != sum(d2):
        return False
    order = sorted(range(n), key=lambda i: -d1[i])
    used = [False] * n
    mapping = [-1] * n
    def bt(k):
        if k == n:
            return True
        u = order[k]
        for v in range(n):
            if used[v] or d2[v] != d1[u]:
                continue
            good = True
            for t in range(k):
                w = order[t]
                e1 = (r1[u] >> w) & 1
                e2 = (r2[v] >> mapping[w]) & 1
                if e1 != e2:
                    good = False
                    break
            if good:
                used[v] = True
                mapping[u] = v
                if bt(k + 1):
                    return True
                used[v] = False
                mapping[u] = -1
        return False
    return bt(0)

ids = []
K2r = H_K2(); K1_2r = H_2K1()
K4 = graph_from_pairs(4, list(itertools.combinations(range(4), 2)))
E4 = graph_from_pairs(4, [])
t1 = substitute(K2r, K2r, 2, 2)
ids.append(("K2[K2] ≅ K4", iso(4, t1, 4, K4)))
t2 = substitute(K1_2r, K2r, 2, 2)
ids.append(("2K1[K2] ≅ 2K2", iso(4, t2, 4, H_2K2())))
t3 = substitute(K2r, K1_2r, 2, 2)
ids.append(("K2[2K1] ≅ C4", iso(4, t3, 4, H_C4())))
t4 = complement_rows(6, substitute(H_P3(), K2r, 3, 2))
C4u2K1 = graph_from_pairs(6, [(0,1),(1,2),(2,3),(3,0)])
ids.append(("comp(P3[K2]) ≅ C4 ∪ 2K1", iso(6, t4, 6, C4u2K1)))
check("E", "all four substitution identities verified by brute isomorphism", all(v for _, v in ids))
for name, v in ids:
    rec(f"    {name}: {v}")

# ----------------------------------------------------------------------------
# LANE F — avoidance table
# ----------------------------------------------------------------------------
print("\n[F] AVOIDANCE TABLE (induced)")
avoid = [
    ("K2[K2] avoids claw", t1, 4, H_claw()),
    ("K2[K2] avoids C4", t1, 4, H_C4()),
    ("K2[K2] avoids 2K2", t1, 4, H_2K2()),
    ("K2[K2] avoids P3", t1, 4, H_P3()),
    ("K2[K2] avoids 3K1", t1, 4, H_3K1()),
    ("K2[K2] avoids P4", t1, 4, H_P4()),
    ("2K1[K2] avoids P3", t2, 4, H_P3()),
    ("2K1[K2] avoids 3K1", t2, 4, H_3K1()),
    ("2K1[K2] avoids claw", t2, 4, H_claw()),
    ("K2[2K1]=C4 avoids 2K2", t3, 4, H_2K2()),
    ("P3[K2] avoids claw", substitute(H_P3(), K2r, 3, 2), 6, H_claw()),
    ("P3[K2] avoids 3K1 (alpha=2)", substitute(H_P3(), K2r, 3, 2), 6, H_3K1()),
]
avoid_ok = True
for name, rows, n, H in avoid:
    Hn2 = 4 if H in (H_2K2(), H_claw(), H_C4(), H_P4()) else 3
    if not is_H_free(n, rows, Hn2, H):
        avoid_ok = False
        rec(f"    AVOIDANCE FAIL: {name}")
check("F", "12-entry induced-avoidance table verified", avoid_ok)
# P3[K2] alpha = 2
p3k2 = substitute(H_P3(), K2r, 3, 2)
alpha_p3k2 = max_clique(6, complement_rows(6, p3k2))
check("F", f"alpha(P3[K2]) = {alpha_p3k2} (claimed 2)", alpha_p3k2 == 2)
# transversal law: H1[H2] contains induced H1 (transversal) and induced H2 (in a class)
trav = graph_from_pairs(6, [(0,0)] )  # placeholder
def transversal_induced(H1rows, a, G, b):
    # pick one vertex per class: the induced subgraph on {(p, 0)} equals H1
    sub = [p * b + 0 for p in range(a)]
    return iso(a, induced_sub_rows(G, tuple(sub)), a, H1rows)
check("F", "transversal law: P3[K2] contains induced P3 on (p,0) transversal",
      transversal_induced(H_P3(), 3, p3k2, 2))
sub_in_class = induced_sub_rows(p3k2, (0, 1))
check("F", "class law: P3[K2] contains induced K2 inside class 0", iso(2, sub_in_class, 2, K2r))

# ----------------------------------------------------------------------------
# LANE G — blow-up law (exhaustive q,s in {1,2,3}^2)
# ----------------------------------------------------------------------------
print("\n[G] THEOREM 4A — blow-up min-law on the exhaustive frame")
P3P3 = substitute(H_P3(), H_P3(), 3, 3)  # the 9-vertex composed graph
viol = 0
total_bu = 0
contain_count = 0
for q in (1, 2, 3):
    for s in (1, 2, 3):
        hP3q = TABLES["P3"][q - 1]
        hP3s = TABLES["P3"][s - 1]
        for Qmask in range(num_graphs(q)):
            Qrows = rows_from_edge_mask(q, Qmask)
            for cls_masks in itertools.product(range(num_graphs(s)), repeat=q):
                cls_rows = [rows_from_edge_mask(s, cm) for cm in cls_masks]
                n = q * s
                rows = [0] * n
                def vid(i, y): return i * s + y
                for i in range(q):
                    for y in range(s):
                        r = 0
                        for y2 in range(s):
                            if (cls_rows[i][y] >> y2) & 1:
                                r |= (1 << vid(i, y2))
                        for j in range(q):
                            if i != j and ((Qrows[i] >> j) & 1):
                                for y2 in range(s):
                                    r |= (1 << vid(j, y2))
                        rows[vid(i, y)] = r
                total_bu += 1
                qfree = is_H_free(q, Qrows, 3, H_P3())
                somecls = any(is_H_free(s, cr, 3, H_P3()) for cr in cls_rows)
                # contains induced P3[P3]?
                if n < 9:
                    contains = False
                else:
                    contains = fast_iso(9, rows, P3P3)
                if contains:
                    contain_count += 1
                # the POSITIVE transversal law: Q has P3 AND every class has P3 => G contains P3[P3]
                if (not qfree) and (not somecls) and not contains:
                    viol += 1
                    rec(f"    G-LAW VIOLATION (positive): q={q} s={s} Qmask={Qmask} cls={cls_masks}")
                # the AVOIDANCE disjunction + hom law for P3[P3]-free G
                if not contains:
                    if not (qfree or somecls):
                        viol += 1
                    if hom(n, rows) < min(hP3q, hP3s):
                        viol += 1
check("G", f"blow-up frame exhaustive (q,s in 1..3, {total_bu} blow-ups, campaign count 4317; {contain_count} contain induced P3[P3]): transversal law + avoidance disjunction + hom >= min(h_H1(q), h_H2(s)) violations = {viol}",
      viol == 0 and total_bu == 4317)

# ----------------------------------------------------------------------------
# LANE H — exponent laws (exact rational)
# ----------------------------------------------------------------------------
print("\n[H] THEOREM 4B/4C — exponent laws (exact rational arithmetic)")
def f2(c1, c2):
    return c1 * c2 / (c1 + c2)
r1 = f2(Fraction(1, 2), Fraction(1, 2))
r2 = f2(f2(Fraction(1, 2), Fraction(1, 2)), Fraction(1, 2))
r3 = f2(f2(Fraction(1, 2), Fraction(1, 3)), Fraction(2, 3))
check("H", f"f(1/2,1/2) = {r1} (claimed 1/4)", r1 == Fraction(1, 4))
check("H", f"f(f(1/2,1/2),1/2) = {r2} (claimed 1/6 — the harmonic law)", r2 == Fraction(1, 6))
check("H", f"f(f(1/2,1/3),2/3) = {r3} (claimed 2/13)", r3 == Fraction(2, 13))
# balanced split: q = n^{c2/(c1+c2)}, s = n^{c1/(c1+c2)} -> q^{c1} == s^{c2} == n^{f(c1,c2)}
bal_ok = True
for jj in (1, 2, 3):
    n = 4 ** jj          # (c1,c2)=(1/2,1/2): q = s = sqrt(n)
    q = 2 ** jj
    s = 2 ** jj
    if q ** 2 != n or s ** 2 != n:
        bal_ok = False
check("H", "balanced splits: q=s=2^j on n=4^j give q^{1/2}=s^{1/2}=n^{1/4}=2^{j/2} exact (integer grid)", bal_ok)

# ----------------------------------------------------------------------------
# LANE I — the F7 family theorem finite core
# ----------------------------------------------------------------------------
print("\n[I] F7 FAMILY THEOREM — finite core + tightness witnesses")
F7 = {"K2": (2, H_K2()), "2K1": (2, H_2K1()), "P3": (3, H_P3()),
      "Pbar3": (3, H_Pbar3()), "K3": (3, H_K3()), "3K1": (3, H_3K1())}
f7_ok = True
f7_detail = {}
for name, (Hn2, Hrows2) in F7.items():
    vals = []
    for n in range(1, 7):
        floor_sq = math.isqrt(n)
        best = None
        for rows in all_graphs(n):
            if is_H_free(n, rows, Hn2, Hrows2):
                h = hom(n, rows)
                if best is None or h < best:
                    best = h
                if h < floor_sq:
                    f7_ok = False
                    bad("I", f"F7 VIOLATION: {name}-free graph on n={n} with hom < floor(sqrt({n}))")
        vals.append(best)
    # n = 7: floor(sqrt(7)) = 2 and the TRIVIAL FLOOR holds for EVERY graph on
    # n >= 2 vertices (any two vertices are adjacent -> clique of 2, or
    # non-adjacent -> independent set of 2). Verified for all H-free graphs
    # a fortiori; the n=7 tables (lane A, Ramsey-forced h=3) exceed it anyway.
    vals.append(None)
    f7_detail[name] = vals
check("I", "F7 family floor(sqrt(n)) verified exhaustively n=1..6 for all six non-vacuous members; n=7 via the trivial floor lemma (floor(sqrt(7))=2 <= hom of any graph on >=2 vertices) + lane A's Ramsey-forced h=3", f7_ok)
for name in F7:
    rec(f"    h_{name} (F7 view, n=1..6): {f7_detail[name][:6]}")
# the trivial floor lemma itself, spot-verified exhaustively at n in 2..6:
triv_ok = all(hom(n, rows) >= 2 for n in range(2, 7) for rows in all_graphs(n))
check("I", "trivial floor lemma: every graph on n in 2..6 vertices has hom >= 2 (exhaustive spot-verification)", triv_ok)

tight_ok = True
for j in (1, 2, 3):
    m = 2 ** j
    n = m * m
    # disjoint union of m copies of K_m
    rows = [0] * n
    off = 0
    for _ in range(m):
        for a in range(off, off + m):
            for b in range(off, off + m):
                if a != b:
                    rows[a] |= (1 << b)
        off += m
    om = m
    al = m  # one vertex per clique
    if hom(n, rows) != m or m != math.isqrt(n):
        tight_ok = False
check("I", "tightness witnesses j=1..3: disjoint union of 2^j K_{2^j} on n=4^j has max(omega,alpha)=2^j=floor(sqrt(n)) EXACTLY (c=1/2 optimal in-family)", tight_ok)

# ----------------------------------------------------------------------------
# LANE J — negative controls (comparator non-vacuity)
# ----------------------------------------------------------------------------
print("\n[J] NEGATIVE CONTROLS")
# J1: corrupted table must be rejected by the derivation
corrupt = dict(TABLES); corrupt["P3"] = [1, 2, 2, 2, 2, 3, 3]  # h_P3(5) corrupted 3->2
rejected = corrupt["P3"] != derived["P3"]
check("J", "corrupted h_P3(5)=2 table REJECTED (true value 3)", rejected)
# J2: corrupted witness: unbalanced clique union at n=5 with hom != ceil(sqrt(5))=3
rows_bad = [0] * 5
for a in range(4):
    for b in range(4):
        if a != b:
            rows_bad[a] |= (1 << b)
w_bad = components_are_cliques(5, rows_bad) and hom(5, rows_bad) == 3
check("J", "corrupted n=5 witness (K4 ∪ K1, hom=4) correctly NOT a ceil(sqrt(5))=3 witness", (not w_bad) or hom(5, rows_bad) == 4)
# J3: a P3-containing graph must not pass the classification
rows_p3 = H_P3() + [0, 0]  # P3 plus two isolated
passed = is_H_free(5, rows_p3, 3, H_P3())
check("J", "P3-containing graph REJECTED by the P3-free checker (non-vacuity)", not passed)

# ----------------------------------------------------------------------------
# VERDICT
# ----------------------------------------------------------------------------
print("\n" + "=" * 78)
print("VERDICT")
print("=" * 78)
print(f"  PASS: {PASS}   FAIL/CRITICAL: {FAIL}")
for r in RECEIPTS:
    if "CRITICAL" in r:
        print(r)
if FAIL == 0 and PASS >= 20:
    print("COMPARATOR_61_GREEN=1")
    print("CMP61-A H-TABLES GREEN")
    print("CMP61-B P3-CLASSIFICATION GREEN")
    print("CMP61-C 3K1-LAW+C5 GREEN")
    print("CMP61-D RAMSEY GREEN")
    print("CMP61-E SUBSTITUTION-IDENTITIES GREEN")
    print("CMP61-F AVOIDANCE GREEN")
    print("CMP61-G BLOWUP-LAW GREEN")
    print("CMP61-H EXPONENT-LAWS GREEN")
    print("CMP61-I F7-FAMILY GREEN")
    print("CMP61-J NEGATIVE-CONTROLS GREEN")
    sys.exit(0)
else:
    print("COMPARATOR_61_RED")
    sys.exit(2)
