#!/usr/bin/env python3
"""#273 hunt v4: fast masks via geometric series; DLX lowest-bit branching
+ capacity pruning + moduli-subset ordering. Distinct moduli, all p-1, p>=5."""
import sympy, sys, time

L = int(sys.argv[1]) if len(sys.argv) > 1 else 720720
FULL = (1 << L) - 1

ps = [p for p in sympy.primerange(5, 200000) if L % (p-1) == 0]
moduli = sorted(set(p-1 for p in ps))
dens = sum(1.0/n for n in moduli)
print(f"L={L} moduli={len(moduli)} density={dens:.4f}", flush=True)
print("moduli:", moduli, flush=True)

# geometric mask: bits at 0, n, 2n, ... < L  ==  sum_{k<m} 2^{kn}, m = ceil(L/n)
def geom_mask(n):
    m = (L + n - 1) // n
    return (((1 << (n*m)) - 1) // ((1 << n) - 1)) & FULL

base = {n: geom_mask(n) for n in moduli}

def rot(m, a): return ((m >> a) | (m << (L - a))) & FULL

t0 = time.time()
nodes = 0
best_left = [L]
import sys as _s
_sys = _s
LIMIT = 3_000_000  # node limit per phase

def search(unc, unused, chosen, cap, depth):
    global nodes
    nodes += 1
    if nodes % 50000 == 0:
        print(f"  nodes={nodes} t={time.time()-t0:.0f}s d={depth} best={best_left[0]} unc={unc.bit_count()}", flush=True)
    u_cnt = unc.bit_count()
    if u_cnt == 0: return chosen
    if u_cnt < best_left[0]: best_left[0] = u_cnt
    if nodes > LIMIT: return None
    if not unused: return None
    if u_cnt > cap * L: return None   # capacity prune
    r = (unc & -unc).bit_length() - 1
    # order: small moduli first (large coverage classes)
    for n in unused:
        a = r % n
        new_unc = unc & ~rot(base[n], a)
        res = search(new_unc, [x for x in unused if x != n], chosen + [(a, n)], cap - 1.0/n, depth+1)
        if res is not None: return res
    return None

res = search(FULL, list(moduli), [], dens, 0)
if res is not None:
    print("FULL COVER FOUND — verifying...", flush=True)
    ok = True
    for x in range(L):
        if not any(x % n == a for a, n in res): ok = False; break
    print("VERIFIED:", ok, flush=True)
    if ok:
        with open(f"WITNESS_273_L{L}.txt", "w") as f:
            f.write(f"#273 WITNESS: distinct covering system, all moduli p-1 (p>=5 prime), L={L}\n")
            f.write(f"# {len(res)} classes; every integer satisfies at least one class\n")
            for a, n in sorted(res, key=lambda t: t[1]): f.write(f"x = {a} mod {n}   (p = {n+1})\n")
        print("=== WITNESS WRITTEN ===", flush=True)
        for a, n in sorted(res, key=lambda t: t[1]): print(f"x = {a:>6} mod {n:>6}  (p={n+1})")
else:
    print(f"phase over: nodes={nodes} best leftover {best_left[0]}/{L} = {best_left[0]/L:.3%}", flush=True)
