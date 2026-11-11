#!/usr/bin/env python3
"""#273 exact-cover hunt v3: DLX-on-bitmask, lowest-uncovered-bit branching,
capacity pruning (uncovered density <= sum 1/n unused), iterative deepening
on moduli subsets. Distinct moduli, all p-1 (p>=5 prime)."""
import sympy, sys, time

L = int(sys.argv[1]) if len(sys.argv) > 1 else 720720
FULL = (1 << L) - 1

ps = [p for p in sympy.primerange(5, 100000) if L % (p-1) == 0]
moduli = sorted(set(p-1 for p in ps))
dens = sum(1.0/n for n in moduli)
print(f"L={L} moduli={len(moduli)} density={dens:.4f}", flush=True)
print("moduli:", moduli, flush=True)

# base masks: bits at multiples of n  (class 0 mod n); class a = rotation by a
base = {}
for n in moduli:
    b = 0
    for k in range(0, L, n): b |= 1 << k
    base[n] = b

def rot(m, a): return ((m >> a) | (m << (L - a))) & FULL

# precompute rotation cost is fine; class mask for (n,a):
def cmask(n, a): return rot(base[n], a)

nodes = 0
t0 = time.time()
best_left = [L]

def search(unc, unused, chosen, cap):
    """unc: uncovered bitmask; unused: list of moduli; cap: sum 1/n of unused."""
    global nodes, best_left
    nodes += 1
    if nodes % 2000 == 0:
        el = time.time() - t0
        print(f"  nodes={nodes} t={el:.0f}s depth={len(chosen)} best_left={best_left[0]} unc={unc.bit_count()}", flush=True)
    u_cnt = unc.bit_count()
    if u_cnt == 0:
        return chosen
    if u_cnt < best_left[0]:
        best_left[0] = u_cnt
    # capacity prune: remaining uncovered density must be <= capacity
    if u_cnt > cap * L * 1.0000001:
        return None
    if not unused:
        return None
    # lowest uncovered bit
    r = (unc & -unc).bit_length() - 1
    # try moduli in decreasing class-size order (big classes first)
    order = sorted(unused, key=lambda n: -len(range(r%n, L, n)) if False else n)
    # branch: for each unused modulus n, class a = r % n covers r
    # prefer LARGE n first? no — prefer SMALL n (big coverage). sorted ascending n
    for n in order:
        a = r % n
        m = cmask(n, a)
        new_unc = unc & ~m
        res = search(new_unc, [x for x in unused if x != n], chosen + [(a, n)], cap - 1.0/n)
        if res is not None: return res
    return None

# capacity = full sum; iterative: require using moduli so that cap stays >= unc density
res = search(FULL, list(moduli), [], dens)
if res is not None:
    print("FULL COVER FOUND", flush=True)
    # verify
    ok = all(any(x % n == a for a, n in res) for x in range(0, L, L//1000))
    v = True
    for x in range(L):
        if not any(x % n == a for a, n in res): v=False; break
    print("verified:", v, flush=True)
    if v:
        with open(f"WITNESS_273_L{L}.txt", "w") as f:
            f.write(f"#273 WITNESS: distinct covering system, all moduli p-1, p>=5 prime, L={L}\n")
            for a, n in sorted(res, key=lambda t: t[1]): f.write(f"x = {a} mod {n}   (p = {n+1})\n")
        print("WITNESS WRITTEN", flush=True)
        for a, n in sorted(res, key=lambda t: t[1]): print(f"x = {a:>5} mod {n:>5}  (p={n+1})")
else:
    print(f"no cover; best leftover {best_left[0]}/{L}", flush=True)
