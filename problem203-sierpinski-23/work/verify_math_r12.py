"""C-203 round-12 PRE-FLIGHT MATH VERIFICATION (S058).

The mission demands the honest state be verified before annealing rounds 12+.
All numbers below are computed by THIS script (no fabricated inputs); the full
stdout is teed to verify_r12.log.

Checks:
  1. L=27720 family: size + density budget (claims: 41 members, 1.0563)
  2. L=55440 family: size + density budget (claims: 52 members, 1.1628)
  3. State inventory: state27720live/all vs the old r1 greedy state27720.json
     (the "1.58% remaining" claim of the r1 round) + bestres27720.txt
  4. Exact residuals via the annealer's own count-map method (build_count from
     anneal_27720c.py, verbatim semantics) for: live state, banked state, and
     the old 41-layer greedy state.
  5. Build-time measurement (reaper-law round planning).
"""
import json, time
import numpy as np

L = 27720
W = "/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/work/"
PDIR = "/home/z/my-project/erdos-weak-problems/problem203-sierpinski-23/"

pal = json.load(open(PDIR + "pal_dlog_full.json"))
pal = [(int(r[0]), int(r[1]), int(r[2]), int(r[3])) for r in pal]


def dedup(fam):
    """distinct-prime-base dedup, smallest h per base (engine protocol)."""
    bases = {}
    for (q, h, U, V) in fam:
        p = q
        for d in range(2, int(q ** 0.5) + 1):
            if q % d == 0:
                p = d
                break
        if p not in bases or 1.0 / h > 1.0 / bases[p][1]:
            bases[p] = (q, h, U, V)
    return sorted(bases.values(), key=lambda r: -1.0 / r[1])


print(f"palette entries: {len(pal)}", flush=True)
for Lx in (27720, 55440):
    fam = [r for r in pal if Lx % r[1] == 0]
    fd = dedup(fam)
    print(f"L={Lx}: all-member fam {len(fam)} budget {sum(1.0/r[1] for r in fam):.4f} | "
          f"distinct-base fam {len(fd)} budget {sum(1.0/r[1] for r in fd):.4f}", flush=True)

live = json.load(open(W + "state27720live.json"))
allb = json.load(open(W + "state27720all.json"))
old = json.load(open(W + "state27720.json"))
bestres = int(open(W + "bestres27720.txt").read().strip())
try:
    st55 = json.load(open(W + "state55440.json"))
    r55 = json.load(open(W + "round55440.json"))
except Exception as e:
    st55, r55 = None, None

print(f"state27720live : {len(live)} layers, {sum(1 for l in live if l[4] >= 0)} active, "
      f"active budget {sum(1.0/l[1] for l in live if l[4] >= 0):.4f}", flush=True)
print(f"state27720all : {len(allb)} layers, {sum(1 for l in allb if l[4] >= 0)} active, "
      f"active budget {sum(1.0/l[1] for l in allb if l[4] >= 0):.4f}", flush=True)
print(f"state27720(old): {len(old)} layers, {sum(1 for l in old if l[4] >= 0)} active, "
      f"active budget {sum(1.0/l[1] for l in old if l[4] >= 0):.4f}", flush=True)
if st55 is not None:
    print(f"state55440    : {len(st55)} layers, {sum(1 for l in st55 if l[4] >= 0)} active; round55440={r55}", flush=True)
print(f"live == all   : {live == allb}", flush=True)
qsl = {l[0] for l in live}
qso = {l[0] for l in old}
print(f"in old(r1) not in live: {sorted(qso - qsl)}", flush=True)
print(f"in live not in old(r1): {sorted(qsl - qso)}", flush=True)
print(f"banked bestres27720.txt = {bestres} = {bestres / L / L * 100:.4f}% of L^2 (L^2={L*L})", flush=True)


def build_count(layers):
    """verbatim semantics of anneal_27720c.py build_count"""
    count = np.zeros((L, L), dtype=np.int8)

    def add_coset(h, U, V, Wv, delta):
        g = int(np.gcd(V, h))
        hg = h // g
        ks = np.arange(L, dtype=np.int64)
        rhs = (Wv - U * ks) % h
        ok = (rhs % g == 0) if g > 1 else np.ones(L, dtype=bool)
        Vg = (V // g) % hg if hg > 1 else 0
        inv = pow(int(Vg), -1, int(hg)) if hg > 1 else 0
        idx_k = np.nonzero(ok)[0]
        for k in idx_k:
            l0 = ((int(rhs[k]) // g) * inv) % hg if hg > 1 else 0
            row = count[k]
            ls = np.arange(l0, L, hg)
            row[ls] += delta
    for l in layers:
        if l[4] >= 0:
            q, h, U, V, Wv = l
            add_coset(h, U, V, Wv, 1)
    return count


t = time.time()
c = build_count(live)
rl = int((c == 0).sum())
bl = time.time() - t
print(f"RESIDUAL live  = {rl} ({rl / L / L * 100:.4f}%) [build {bl:.0f}s]", flush=True)
del c
if live == allb:
    ra = rl
    print(f"RESIDUAL all(bank) = same (states identical) = {ra}", flush=True)
else:
    t = time.time()
    c = build_count(allb)
    ra = int((c == 0).sum())
    print(f"RESIDUAL all(bank) = {ra} ({ra / L / L * 100:.4f}%) [build {time.time()-t:.0f}s]", flush=True)
    del c
t = time.time()
c = build_count(old)
ro = int((c == 0).sum())
print(f"RESIDUAL old-r1-greedy-41 = {ro} ({ro / L / L * 100:.4f}%) [build {time.time()-t:.0f}s]", flush=True)
del c

print(f"consistency: bestres {bestres} vs live {rl} -> {'CONSISTENT' if bestres == rl else 'MISMATCH'}; "
      f"vs bank-state {ra} -> {'CONSISTENT' if bestres == ra else 'MISMATCH'}", flush=True)
print(f"old-r1 vs banked best delta: {bestres - ro} cells ({(bestres - ro) / L / L * 100:+.4f}pp in favour of old-r1)", flush=True)
print(f"build time per 35-41 layer state: {bl:.0f}s", flush=True)
print("VERIFY DONE", flush=True)
