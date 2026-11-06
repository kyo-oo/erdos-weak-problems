#!/usr/bin/env python3
"""#273 anneal: fixed distinct moduli (all p-1, p>=5), minimize uncovered
residues of Z_L by annealing the shift vector. Uncovered->0 => WITNESS."""
import sympy, random, time, sys

L = 720720
FULL = (1 << L) - 1
ps = [p for p in sympy.primerange(5, 200000) if L % (p-1) == 0]
all_mods = sorted(set(p-1 for p in ps))

def geom_mask(n):
    m = (L + n - 1) // n
    return (((1 << (n*m)) - 1) // ((1 << n) - 1)) & FULL

# pick a tight subset: smallest moduli until density just over 1.03
subset = []
d = 0.0
for n in all_mods:
    subset.append(n); d += 1.0/n
    if d > 1.10: break
print(f"subset={len(subset)} moduli density={d:.4f}: {subset}", flush=True)

base = {n: geom_mask(n) for n in subset}
def rot(m, a): return ((m >> a) | (m << (L - a))) & FULL

def or_all(shifts):
    acc = 0
    for n, a in zip(subset, shifts): acc |= rot(base[n], a)
    return acc

def uncovered(orb): return L - orb.bit_count()

rng = random.Random(12345)
t0 = time.time()
best_global = 10**9
TIME_LIMIT = 240  # 4 minutes
restart = 0
while time.time() - t0 < TIME_LIMIT:
    restart += 1
    shifts = [rng.randrange(n) for n in subset]
    orb = or_all(shifts)
    u = uncovered(orb)
    T = max(64, L // 500)
    it = 0
    while T > 0 and time.time() - t0 < TIME_LIMIT:
        it += 1
        i = rng.randrange(len(subset))
        old = shifts[i]
        new = rng.randrange(subset[i])
        if new == old: continue
        shifts[i] = new
        orb2 = or_all(shifts)
        u2 = uncovered(orb2)
        if u2 <= u or rng.random() < pow(2.718, -(u2-u)/T):
            u = u2
            if u < best_global:
                best_global = u
                print(f"  [r{restart} it{it} T={T}] uncovered={u} ({u/L:.3%})", flush=True)
            if u == 0:
                print("FULL COVER!", flush=True)
                ok = all(any(x % n == a for n, a in zip(subset, shifts)) for x in range(0, L, 97))
                # exact verify
                ok = True
                for x in range(L):
                    if not any(x % n == a for n, a in zip(subset, shifts)): ok = False; break
                print("VERIFIED:", ok, flush=True)
                if ok:
                    with open("WITNESS_273.txt", "w") as f:
                        f.write(f"#273 WITNESS: distinct covering, all moduli p-1 (p>=5), L={L}\n")
                        for n, a in zip(subset, shifts): f.write(f"x = {a} mod {n}   (p = {n+1})\n")
                    print("=== WITNESS WRITTEN ===")
                    for n, a in zip(subset, shifts): print(f"x = {a:>5} mod {n:>5}  (p={n+1})")
                    sys.exit(0)
        else:
            shifts[i] = old
        T = int(T * 0.9995)
print(f"done: best uncovered {best_global} ({best_global/L:.3%})", flush=True)
