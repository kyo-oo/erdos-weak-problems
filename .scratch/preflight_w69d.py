#!/usr/bin/env python3
"""Pre-flight benchmarks for the W69-D escalation battery. Scratch, not committed."""
import time
from itertools import combinations, product

t00 = time.time()

def m(k): return k * (k - 1) // 2
# W69 indexing: pair (i,j), i<j, sorted by key (j, -i): pairs of vertex k-1
# are the LAST k-1 bits, in order (k-2,k-1), (k-3,k-1), ..., (0,k-1).
PAIRS = {k: sorted(combinations(range(k), 2), key=lambda p: (p[1], -p[0])) for k in range(9)}
FULL = {k: (1 << m(k)) - 1 for k in range(9)}
for k in range(2, 9):
    assert PAIRS[k][-(k - 1):] == [(i, k - 1) for i in range(k - 2, -1, -1)], k
    assert len(PAIRS[k]) == m(k)

def adj_of(F, n):
    adj = [0] * n
    for b, (i, j) in enumerate(PAIRS[n]):
        if (F >> b) & 1:
            adj[i] |= 1 << j
            adj[j] |= 1 << i
    return adj

def pc(x): return x.bit_count()

def omega_bb(adj, n):
    best = 0
    def bk(rs, cand):
        nonlocal best
        if rs > best: best = rs
        if rs + pc(cand) <= best: return
        while cand:
            if rs + pc(cand) <= best: return
            b = cand & (-cand)
            v = b.bit_length() - 1
            cand ^= b
            bk(rs + 1, cand & adj[v])
    bk(0, (1 << n) - 1)
    return best

# ---------------- triangle-free DP counts n=1..8 ----------------
def encode_top(S, n):
    """vertex set S (bits over {0..n-2}) -> edge-mask bits for pairs (v, n-1)."""
    r = 0
    x = S
    while x:
        b = x & (-x)
        v = b.bit_length() - 1
        r |= 1 << (m(n - 1) + (n - 2 - v))
        x ^= b
    return r

def tf_extend(tf_prev, n):
    tf_new = set()
    for F6 in tf_prev:
        adj = adj_of(F6, n - 1)
        stack = [((1 << (n - 1)) - 1, 0)]
        while stack:
            cand, S = stack.pop()
            tf_new.add(F6 | encode_top(S, n))
            while cand:
                b = cand & (-cand)
                v = b.bit_length() - 1
                cand ^= b
                stack.append((cand & ~adj[v] & ~b, S | b))
    return tf_new

tf_prev = {0}
tf_counts = {1: 1}
for n in range(2, 9):
    tf_prev = tf_extend(tf_prev, n)
    tf_counts[n] = len(tf_prev)
    print("n=%d triangle-free labeled: %d" % (n, len(tf_prev)))

print("triangle-free counts:", tf_counts)
print("cumulative n<=6:", sum(tf_counts[k] for k in range(1, 7)))
print("cumulative n<=7:", sum(tf_counts[k] for k in range(1, 8)))

# rebuild level-6 tf set
tf_prev = {0}
for n in range(2, 7):
    tf_prev = tf_extend(tf_prev, n)
tf6_set = tf_prev
print("tf6 rebuilt:", len(tf6_set))

TF6 = bytearray(1 << 15)
for F in tf6_set:
    TF6[F] = 1

t0 = time.time()
OM6 = bytearray(1 << 15)
for F in range(1 << 15):
    OM6[F] = omega_bb(adj_of(F, 6), 6)
print("OM6 via B&B: %.1fs" % (time.time() - t0))

t0 = time.time()
OM7 = bytearray(1 << 21)
for F6 in range(1 << 15):
    adj = adj_of(F6, 6)
    f = [0] * 64
    for N in range(1, 64):
        v = (N & (-N)).bit_length() - 1
        a = f[N ^ (1 << v)]
        b = 1 + f[N & adj[v]]
        f[N] = a if a >= b else b
    base = OM6[F6]
    for Nv in range(64):
        w = base
        g = 1 + f[Nv]
        if g > w: w = g
        OM7[(Nv << 15) | F6] = w
print("OM7 recurrence build: %.1fs" % (time.time() - t0))

t0 = time.time()
cnt = {h: 0 for h in ('K2', 'Kb2', 'K3', 'Kb3')}
FULL7 = FULL[7]
for F6 in range(1 << 15):
    tf = TF6[F6]
    tfc = TF6[F6 ^ FULL[6]]
    adj = adj_of(F6, 6)
    adjc = adj_of(F6 ^ FULL[6], 6)
    for Nv in range(64):
        F = (Nv << 15) | F6
        if F == 0: cnt['K2'] += 1
        if F == FULL7: cnt['Kb2'] += 1
        if tf:
            x = Nv; ok = True
            while x:
                b = x & (-x); v = b.bit_length() - 1
                if adj[v] & Nv: ok = False; break
                x ^= b
            if ok: cnt['K3'] += 1
        Nvc = Nv ^ 63
        if tfc:
            x = Nvc; ok = True
            while x:
                b = x & (-x); v = b.bit_length() - 1
                if adjc[v] & Nvc: ok = False; break
                x ^= b
            if ok: cnt['Kb3'] += 1
print("full-scan K2/Kb2/K3/Kb3 flags: %.1fs" % (time.time() - t0))
print(cnt)
assert cnt['K3'] == tf_counts[7], (cnt['K3'], tf_counts[7])
print("K3 count matches DP: OK")

t0 = time.time()
x = 12345
dis = 0
for i in range(200000):
    x = (x * 1103515245 + 12345) & 0x7FFFFFFF
    F = (x | (x << 10)) & ((1 << 21) - 1)
    adj = adj_of(F, 7)
    w = omega_bb(adj, 7)
    a = omega_bb([~adj[v] & 0x7F & ~(1 << v) for v in range(7)], 7)
    if OM7[F] != w or OM7[F ^ FULL7] != a:
        dis += 1
print("200k B&B spot check: %.1fs, disagreements=%d" % (time.time() - t0, dis))

# ---------------- cograph labeled gen n<=8 ----------------
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

def cographs(vs, memo, n):
    key = frozenset(vs)
    if key in memo: return memo[key]
    vs = sorted(key)
    if len(vs) == 1:
        res = {0}
        memo[key] = res
        return res
    res = set()
    allpairs = {p: b for b, p in enumerate(PAIRS[n])}
    for pi in set_partitions(vs):
        if len(pi) < 2: continue
        cross = 0
        for i in range(len(pi)):
            for j in range(i + 1, len(pi)):
                for u in pi[i]:
                    for v in pi[j]:
                        cross |= 1 << allpairs[(min(u, v), max(u, v))]
        opts = [cographs(b, memo, n) for b in pi]
        for combo in product(*opts):
            mu = 0
            for msk in combo: mu |= msk
            res.add(mu)
            res.add(mu | cross)
    memo[key] = res
    return res

for n in (7, 8):
    t0 = time.time()
    memo = {}
    s = cographs(range(n), memo, n)
    print("labeled cographs n=%d: %d  (%.1fs)" % (n, len(s), time.time() - t0))

print("TOTAL %.1fs" % (time.time() - t00))
