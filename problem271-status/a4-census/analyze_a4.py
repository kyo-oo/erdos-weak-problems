#!/usr/bin/env python3
"""WAR-271 task 2-d: A(4) structure extraction from the verified census dumps.

Inputs (all produced + verified by stanley_census / verify_dump):
  data/a4_members_3k20.txt  — A(4) = S(0,4) members on [0, 3^20)
  data/a2_members_3k13.txt  — A(2) = S(0,2) members on [0, 3^13)  [comparison]

Outputs: analysis/*.txt raw tables + this stdout report.
Facts derived from FIXED ranges inside [0,3^K) (block counts, LSB digit
frequencies, gaps, counts) are CERTAIN (complete census); facts about
leading-digit prefixes are empirical to the depth-20 horizon (absence of a
node could be refuted by members >= 3^20; presence is certain).
"""
import sys, os, math
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
A4 = [int(x) for x in open(os.path.join(HERE, 'data/a4_members_3k20.txt'))]
A2 = [int(x) for x in open(os.path.join(HERE, 'data/a2_members_3k13.txt'))]
OUT = os.path.join(HERE, 'analysis')
os.makedirs(OUT, exist_ok=True)

def ter(n):
    if n == 0: return "0"
    d = ""
    while n: d = str(n % 3) + d; n //= 3
    return d

def report(fname, lines):
    with open(os.path.join(OUT, fname), 'w') as f:
        f.write('\n'.join(lines) + '\n')
    print(f"  [raw: analysis/{fname}]")

def census(A, K):
    """c[k] = |A ∩ [0,3^k)|, k=0..K"""
    c = []
    for k in range(K + 1):
        p = 3 ** k
        # binary search
        lo, hi = 0, len(A)
        while lo < hi:
            mid = (lo + hi) // 2
            if A[mid] < p: lo = mid + 1
            else: hi = mid
        c.append(lo)
    return c

K4, K2 = 20, 13
c4 = census(A4, K4)
c2 = census(A2, K2)
L3 = math.log(3)

print("=" * 78)
print("(a) EXACT COUNTS  c_k = |A(4) ∩ [0,3^k)|")
print("=" * 78)
rows = []
for k in range(K4 + 1):
    rows.append(f"k={k:2d}  3^k={3**k:>11d}  c_k={c4[k]:>7d}")
for r in rows: print(r)
report('counts_a4.txt', rows)
print(f"\nA(2) comparison: c_k = {c2}  (= 2^k exactly, the Lean census)")
assert c2 == [2**k for k in range(K2 + 1)], "A(2) census must be 2^k"
print("task-stated A(4) census [1,4,9,19,37,79,147] (k=1..7):",
      c4[1:8], "MATCH" if c4[1:8] == [1,4,9,19,37,79,147] else "MISMATCH")

print()
print("=" * 78)
print("(b) GROWTH ANALYSIS")
print("=" * 78)
rows = ["k    c_k      ratio r_k=c_k/c_{k-1}   local exp ln r/ln3   cum exp ln c/(k ln3)   2c_{k-1}-c_k"]
for k in range(2, K4 + 1):
    r = c4[k] / c4[k-1]
    le = math.log(r) / L3
    ce = math.log(c4[k]) / (k * L3)
    rows.append(f"{k:2d} {c4[k]:7d}   {r:8.4f}          {le:8.4f}            {ce:8.4f}          {2*c4[k-1]-c4[k]:8d}")
for r in rows: print(r)
report('growth_a4.txt', rows)

# local exponent stats over tail
tail = list(range(10, K4 + 1))
les = [math.log(c4[k]/c4[k-1]) / L3 for k in tail]
print(f"\nlocal exponents k=10..20: min={min(les):.4f} max={max(les):.4f} mean={sum(les)/len(les):.4f}")
print(f"cumulative exponent alpha_k: k=10: {math.log(c4[10])/(10*L3):.4f}  k=15: {math.log(c4[15])/(15*L3):.4f}  k=20: {math.log(c4[20])/(20*L3):.4f}")
print(f"Type-1 reference (Cantor rate) log_3 2 = {math.log(2)/L3:.4f};  Type-2 reference 1/2 = 0.5000")
print(f"r_k range over k=2..20: {min(c4[k]/c4[k-1] for k in range(2,K4+1)):.4f} .. {max(c4[k]/c4[k-1] for k in range(2,K4+1)):.4f}")

# a_m growth: exponent fits
print("\nm-th member a_m growth (Type 1: a_m ~ m^{log_2 3} = m^1.585; Type 2: ~ m^2 or m^2/log m):")
rows = []
for m in [100, 1000, 5000, 10000, 50000, 100000, 150000, 200000, 250000, 300000, 340000]:
    a = A4[m-1]
    rows.append(f"m={m:7d}  a_m={a:11d}  a_m/m^2={a/m**2:.5f}  a_m/m^1.585={a/m**1.585:.4f}  a_m*log(m)/m^2={a*math.log(m)/m**2:.5f}")
for r in rows: print(r)
report('member_growth_a4.txt', rows)
# doubling exponents
print("\ndoubling exponent p = ln(a_{2m}/a_m)/ln 2  (Type 1 -> 1.585, Type 2 quadratic -> 2.0):")
rows = []
for m in [500, 5000, 25000, 50000, 88000, 173685]:
    if 2*m <= len(A4):
        p = math.log(A4[2*m-1]/A4[m-1]) / math.log(2)
        rows.append(f"m={m:7d}  a_m={A4[m-1]:11d}  a_2m={A4[2*m-1]:11d}  p={p:.4f}")
for r in rows: print(r)
report('doubling_exp_a4.txt', rows)

# LSQ fits of log a_m = P log m + Q loglog m + C over m in [Mlo, Mhi]
import numpy as np
def fit_am(Mlo, Mhi):
    ms = np.array(range(Mlo, Mhi + 1), dtype=float)
    am = np.array(A4[Mlo-1:Mhi], dtype=float)
    X = np.stack([np.ones_like(ms), np.log(ms), np.log(np.log(ms))]).T
    y = np.log(am)
    coef, res, *_ = np.linalg.lstsq(X, y, rcond=None)
    pred = X @ coef
    r2 = 1 - ((y - pred)**2).sum() / ((y - y.mean())**2).sum()
    return coef, r2
for Mlo, Mhi in [(1000, 347370), (50000, 347370), (150000, 347370)]:
    coef, r2 = fit_am(Mlo, Mhi)
    print(f"LSQ log a_m ~ C + P log m + Q log log m  on m∈[{Mlo},{Mhi}]: P={coef[2]:.4f} Q={coef[1]:.4f}... "
          .replace("P={coef[2]:.4f} Q={coef[1]:.4f}", f"P={coef[1]:.4f} Q={coef[2]:.4f}") + f"R2={r2:.6f}")

# N(x) fits: log c_k = C + a*(k ln3) + b*ln(k ln3)
def fit_c(lo, hi):
    ks = np.array(range(lo, hi + 1), dtype=float)
    x = ks * L3
    y = np.log(np.array(c4[lo:hi+1], dtype=float))
    X = np.stack([np.ones_like(x), x, np.log(x)]).T
    coef, *_ = np.linalg.lstsq(X, y, rcond=None)
    pred = X @ coef
    r2 = 1 - ((y-pred)**2).sum()/((y-y.mean())**2).sum()
    return coef, r2
for lo, hi in [(8, 20), (12, 20), (16, 20)]:
    coef, r2 = fit_c(lo, hi)
    print(f"LSQ log c_k ~ C + a ln x + b ln ln x on k∈[{lo},{hi}]: alpha={coef[1]:.4f} beta={coef[2]:.4f} R2={r2:.6f}")
print(f"c_k / 3^(k/2) (Type-2 scale factor): k=13: {c4[13]/3**6.5:.3f}  k=16: {c4[16]/3**8:.3f}  k=19: {c4[19]/3**9.5:.3f}  k=20: {c4[20]/3**10:.3f}")
print(f"c_k / 3^(k log_3 2) = c_k / 2^k:     k=13: {c4[13]/2**13:.3f}  k=16: {c4[16]/2**16:.3f}  k=19: {c4[19]/2**19:.3f}  k=20: {c4[20]/2**20:.3f}")

# exact linear recurrence hunt (order <= 4) — fraction-free solve
print("\nexact integer linear recurrence hunt (orders 1..4): any exact fit?")
def has_recurrence(seq, r):
    # solve for coeffs a_1..a_r with c_k = sum a_i c_{k-i}, exact rationals
    n = len(seq)
    rows_n = n - r
    if rows_n < r + 2: return None
    import fractions as F
    M = [[F.Fraction(seq[k - i]) for i in range(1, r+1)] + [F.Fraction(seq[k])] for k in range(r, n)]
    # gaussian elimination
    ncols = r + 1
    piv = []
    rr = 0
    for col in range(ncols - 1):
        sel = None
        for i in range(rr, len(M)):
            if M[i][col] != 0: sel = i; break
        if sel is None: continue
        M[rr], M[sel] = M[sel], M[rr]
        pv = M[rr][col]
        M[rr] = [v / pv for v in M[rr]]
        for i in range(len(M)):
            if i != rr and M[i][col] != 0:
                f = M[i][col]
                M[i] = [a - f*b for a, b in zip(M[i], M[rr])]
        piv.append(col); rr += 1
        if rr == len(M): break
    # check consistency: any row with zero LHS but nonzero RHS?
    for row in M:
        if all(v == 0 for v in row[:ncols-1]) and row[-1] != 0:
            return False
    # if consistent, an exact recurrence exists (possibly underdetermined)
    return True
seq4 = c4[:]
for r in range(1, 5):
    res = has_recurrence(seq4, r)
    print(f"  order {r}: {'EXACT FIT EXISTS (degenerate/suspicious)' if res else 'no exact fit (inconsistent)'}")

print()
print("=" * 78)
print("(c) TERNARY ADMISSIBLE-PREFIX TREE (leading digits; empirical to depth 20)")
print("=" * 78)
def prefix_tree(A, K):
    """nodes[d] = set of length-d ternary prefixes (MSB-first) of members with >= d digits, d>=1"""
    nodes = [set() for _ in range(K + 1)]
    for n in A:
        if n == 0: continue
        s = ter(n)
        for d in range(1, len(s) + 1):
            nodes[d].add(s[:d])
    return nodes
nodes4 = prefix_tree(A4, K4)
nodes2 = prefix_tree(A2, K2)
rows = []
rows.append("A(4): depth d: #nodes, #nodes/3^d, growth factor vs prev depth")
prev = None
for d in range(1, K4 + 1):
    nn = len(nodes4[d])
    g = f"{nn/prev:.4f}" if prev else "-"
    rows.append(f"  d={d:2d}  nodes={nn:7d}   nodes/3^d={nn/3**d:.5f}   ratio_vs_prev={g}")
    prev = nn
for r in rows: print(r)
report('prefix_tree_counts_a4.txt', rows)
rows = ["A(2) comparison: depth: #nodes"]
for d in range(1, K2 + 1):
    rows.append(f"  d={d:2d}  nodes={len(nodes2[d]):6d}")
for r in rows: print(r)
report('prefix_tree_counts_a2.txt', rows)

# branching: children pattern per node, by depth
print("\nbranching pattern (which child digits exist) by depth — A(4):")
rows = []
for d in range(1, K4):
    pat = Counter()
    for s in nodes4[d]:
        kids = ''.join(sorted(c for c in '012' if s + c in nodes4[d+1] or any(len(t)==d+1 and t.startswith(s+c) and t in nodes4[d+1] for t in [s+c])))
        kids = ''.join(sorted(c for c in '012' if s + c in nodes4[d+1]))
        # leaf-ness: s itself is a full expansion of a member?
        pat[kids] += 1
    rows.append(f"  d={d:2d}: " + ", ".join(f"'{k or '-'}'x{v}" for k, v in sorted(pat.items())))
for r in rows: print(r)
report('prefix_tree_branching_a4.txt', rows)

# leaf vs internal: nodes that are themselves members (full expansions)
memset4 = set(A4)
rows = []
rows.append("depth d: #nodes, #nodes that are full members (leaves of the language), #internal")
for d in range(1, K4 + 1):
    leaves = sum(1 for s in nodes4[d] if int(s, 3) in memset4)
    rows.append(f"  d={d:2d}  nodes={len(nodes4[d]):7d}  leaves={leaves:7d}  internal={len(nodes4[d])-leaves:7d}")
for r in rows: print(r)
report('prefix_tree_leaves_a4.txt', rows)

# subtree signature collapse (self-similarity): bottom-up canonical signatures
print("\nsubtree-signature self-similarity test (number of distinct subtree types at each residual depth):")
def signatures(A, K):
    # build trie over ternary expansions of members (nonzero), mark member-end
    trie = {}          # node id -> {digit: node id}
    isend = set()      # node ids that are complete members
    nxt = 1
    for n in A:
        if n == 0: continue
        s = ter(n)
        cur = 0
        for ch in s:
            if ch not in trie.setdefault(cur, {}):
                trie[cur][ch] = nxt; nxt += 1
            cur = trie[cur][ch]
        isend.add(cur)
    # depth of each node
    depth = {0: 0}
    stack = [0]
    maxd = 0
    while stack:
        u = stack.pop()
        for ch, v in trie.get(u, {}).items():
            depth[v] = depth[u] + 1
            maxd = max(maxd, depth[v])
            stack.append(v)
    # bottom-up signature
    sig = {}
    def getsig(u):
        if u in sig: return sig[u]
        if u not in trie or not trie[u]:
            s = ('L',)  # pure leaf (may or may not be end — handled below)
        else:
            s = ('N' if u in isend else 'I',) + tuple(sorted((c, getsig(v)) for c, v in trie[u].items()))
        sig[u] = s
        return s
    getsig(0)
    # group live nodes by residual depth (maxd - depth)
    from collections import defaultdict as dd
    byres = dd(list)
    for u in trie:
        byres[maxd - depth[u]].append(u)
    out = {}
    for res, us in sorted(byres.items()):
        out[res] = len({sig[u] for u in us})
    return out, maxd
sig4, maxd4 = signatures(A4, K4)
sig2, maxd2 = signatures(A2, K2)
rows = [f"residual depth r (distance to horizon {maxd4}): #distinct subtree types among live nodes"]
for res in sorted(sig4): rows.append(f"  r={res:2d}: {sig4[res]}")
for r in rows: print(r)
report('subtree_types_a4.txt', rows)
print(f"A(2) comparison (horizon {maxd2}): " + ", ".join(f"r={r}:{sig2[r]}" for r in sorted(sig2)))

# digit histograms per member length, MSB and LSB views
print()
print("=" * 78)
print("(d) DIGIT-2 STATISTICS (LSB-position frequencies are CERTAIN: fixed ranges)")
print("=" * 78)
rows = ["members with exactly d ternary digits ([3^(d-1),3^d)): count, mean #2s/member, P(digit=2) per LSB position 0..d-1, %members with no 2"]
bysize = defaultdict(list)
for n in A4:
    if n == 0: continue
    bysize[len(ter(n))].append(n)
for d in sorted(bysize):
    ns = bysize[d]
    pos = [0]*d
    no2 = 0
    tot2 = 0
    for n in ns:
        m = n; cnt2 = 0
        for i in range(d):
            if m % 3 == 2: pos[i] += 1; cnt2 += 1
            m //= 3
        tot2 += cnt2
        if cnt2 == 0: no2 += 1
    freq = " ".join(f"{p/len(ns):.3f}" for p in pos)
    rows.append(f"  d={d:2d} n={len(ns):6d}  mean2s={tot2/len(ns):.3f}  no2%={100*no2/len(ns):5.1f}%  P(2)@pos0..{d-1}: {freq}")
for r in rows: print(r)
report('digit2_stats_a4.txt', rows)
# A(2) comparison
rows = ["A(2): same table (expect: 2 only ever in last position)"]
bysize2 = defaultdict(list)
for n in A2:
    if n == 0: continue
    bysize2[len(ter(n))].append(n)
for d in sorted(bysize2):
    ns = bysize2[d]
    pos = [0]*d
    for n in ns:
        m = n
        for i in range(d):
            if m % 3 == 2: pos[i] += 1
            m //= 3
    freq = " ".join(f"{p/len(ns):.3f}" for p in pos)
    rows.append(f"  d={d:2d} n={len(ns):6d}  P(2)@pos0..{d-1}: {freq}")
for r in rows: print(r)
report('digit2_stats_a2.txt', rows)

# mod-3 residue distribution by scale (certain)
rows = ["A(4) members in [3^(k-1),3^k) by residue mod 3 (count r0 r1 r2):"]
for k in range(1, K4 + 1):
    lo_, hi_ = 3**(k-1), 3**k
    cnt = [0, 0, 0]
    for n in A4:
        if lo_ <= n < hi_: cnt[n % 3] += 1
        elif n >= hi_: break
    rows.append(f"  k={k:2d}: {cnt}")
for r in rows: print(r)
report('mod3_by_scale_a4.txt', rows)

print()
print("=" * 78)
print("(e) BLOCK STRUCTURE (CERTAIN: complete census on [0,3^20))")
print("=" * 78)
# top-level 3-split at each scale
rows = ["A(4): c_k = b0 + b1 + b2 with bi = |A ∩ [i·3^(k-1), (i+1)·3^(k-1))|, and overlap of shifted block with [0,3^(k-1)) set"]
for k in range(1, K4 + 1):
    h = 3**(k-1)
    base = set(n for n in A4 if n < h)
    parts = []
    for i in range(3):
        blk = set(n - i*h for n in A4 if i*h <= n < (i+1)*h)
        parts.append((len(blk), len(blk & base)))
    b0, b1, b2 = parts[0][0], parts[1][0], parts[2][0]
    rows.append(f"  k={k:2d}: c_k={c4[k]:7d} = {b0:7d}+{b1:7d}+{b2:7d}   |B1∩B0|={parts[1][1]:7d}  |B2∩B0|={parts[2][1]:7d}   B1=B0?{parts[1][1]==len(base)==b1}  B2=∅?{b2==0}")
for r in rows: print(r)
report('block_split_a4.txt', rows)
rows = ["A(2): same 3-split (expect b1=b0, b2=0):"]
for k in range(1, K2 + 1):
    h = 3**(k-1)
    base = set(n for n in A2 if n < h)
    b = [sum(1 for n in A2 if i*h <= n < (i+1)*h) for i in range(3)]
    inter1 = len(set(n-h for n in A2 if h <= n < 2*h) & base)
    rows.append(f"  k={k:2d}: c_k={c2[k]:5d} = {b[0]}+{b[1]}+{b[2]}   B1∩B0={inter1}  B1=B0 exactly? {inter1==len(base)==b[1]}")
for r in rows: print(r)
report('block_split_a2.txt', rows)

# empty aligned blocks at each scale (certain)
rows = ["empty aligned blocks [u·3^j,(u+1)·3^j) inside [0,3^20), per j (count + first few u in ternary):"]
for j in range(1, 13):
    size = 3**j
    counts = defaultdict(int)
    for n in A4: counts[n // size] += 1
    empties = sorted(u for u, v in counts.items() if v == 0 and (u+1)*size <= 3**K4)
    # also blocks beyond last member are empty but partially outside data? no: data covers all [0,3^20)
    ubound = 3**(K4 - j)
    empties = [u for u in range(ubound) if counts.get(u, 0) == 0]
    ex = ", ".join(ter(u) for u in empties[:8])
    rows.append(f"  j={j:2d} (size 3^{j}): empty blocks = {len(empties):6d} / {ubound:7d}   first u (ternary): {ex}")
for r in rows: print(r)
report('empty_blocks_a4.txt', rows)
rows = ["A(2): empty aligned blocks inside [0,3^13), per j:"]
for j in range(1, 10):
    size = 3**j
    counts = defaultdict(int)
    for n in A2: counts[n // size] += 1
    ubound = 3**(K2 - j)
    empties = [u for u in range(ubound) if counts.get(u, 0) == 0]
    ex = ", ".join(ter(u) for u in empties[:10])
    rows.append(f"  j={j:2d}: empty = {len(empties):5d} / {ubound:5d}   first u: {ex}")
for r in rows: print(r)
report('empty_blocks_a2.txt', rows)

print()
print("=" * 78)
print("(f) SORTED GAPS")
print("=" * 78)
import numpy as np
a = np.array(A4, dtype=np.int64)
g = np.diff(a)
rows = []
rows.append(f"A(4): {len(g)} gaps on [0,3^20); min={g.min()} max={g.max()}")
rows.append(f"distinct gap values: {len(np.unique(g))}")
uv = np.unique(g)
rows.append(f"gap histogram (value: count) head: " + ", ".join(f"{v}:{c}" for v, c in zip(uv, [int((g==v).sum()) for v in uv[:20]])))
big = np.argsort(g)[-15:][::-1]
rows.append("15 largest gaps (index i means between a_i and a_(i+1)): " + "; ".join(f"i={i}: g={g[i]} at a={a[i]}" for i in big))
rows.append(f"max gap per scale: " + ", ".join(f"3^{k}:{g[:c4[k]-1].max() if c4[k]>1 else 0}" for k in range(2, K4+1)))
for r in rows: print(r)
report('gaps_a4.txt', rows)
a2 = np.array(A2, dtype=np.int64); g2 = np.diff(a2)
rows = [f"A(2): distinct gaps: {sorted(np.unique(g2).tolist())}"]
rows.append(f"A(2) max gap: {g2.max()}")
for r in rows: print(r)
report('gaps_a2.txt', rows)

# gap vs index fit
rows = ["gap percentile scaling: for m in ranges, median gap / median index ^gamma fit:"]
idx = np.arange(1, len(g) + 1)
sel = idx > 30000
lg_i, lg_g = np.log(idx[sel]), np.log(g[sel] + 1)
p = np.polyfit(lg_i, lg_g, 1)
rows.append(f"  log g ~ gamma log i over i>30000: gamma = {p[0]:.4f}")
for r in rows: print(r)
report('gap_scaling_a4.txt', rows)

# overlap with A(2) (stat)
ov = len(memset4 & set(A2))
print(f"\n|A(4) ∩ A(2) ∩ [0,3^13)| = {ov}  (of {c2[13]} A(2)-members; A(4) is NOT a superset/translate of A(2))")
print("DONE")
