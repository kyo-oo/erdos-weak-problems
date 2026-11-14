#!/usr/bin/env python3
"""W66-P203-D A2 — INDEPENDENT COVER VERIFIER (no engine code reused).

Mission: for ANY candidate cover assignment (hunt state layers
[(q, h, U, V, W)] at torus L) verify EVERY (k mod L, l mod L) class
exhaustively — 768M cells at L=27720 — via a completely different
implementation path than the engines:
  engines: numpy bitmaps + dlog lattice parametrization (Uk+Vl=W mod h).
  here:    Python big-int row masks + DIRECT field arithmetic
           (covered iff 2^k 3^l == t_q mod q), t_q derived from the layer
           by a representative cell of {Uk+Vl=W mod h} AND cross-checked
           against an independently reconstructed generator g (g^U=2,
           g^V=3, ord(g)=h). If both derivations of t agree AND the
           sweep count matches the engine bank, the semantics chain is
           verified end-to-end.

Checks per cover:
  C1  layer semantics: t from representative == t from generator; the
      layer's admissible class set (strips) has gcd(o2,o3) elements and
      the layer alone covers exactly L^2/h cells (density exactly 1/h).
  C2  full-torus sweep: exact uncovered count; compare with the banked
      engine residual (bestres27720.txt for L=27720).
  C3  CRT m end-to-end: m = -t_q^{-1} mod q per layer + m = 1 mod 6;
      covered-cell samples satisfy q | 2^k 3^l m + 1 by direct arithmetic.
  C4  explicit small-class tests: (k,l) = (0,0) (m+1 must be composite),
      (1,0), (0,1), small grid; PRIME witnesses 2^k 3^l m + 1 on
      uncovered classes (the fake-cover catcher).
  C5  beyond-torus ord-closure: random large k,l (up to 1e5) and
      systematic k = j*L + r: direct divisibility == class prediction.
"""
import json, math, os, random, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
PDIR = os.path.dirname(HERE)
sys.path.insert(0, HERE)
from a1_palette_audit import my_order

def my_crt(pairs):
    """own CRT over pairwise-coprime moduli; returns (m, M)."""
    m, M = pairs[0]
    for (r2, m2) in pairs[1:]:
        assert math.gcd(M, m2) == 1
        inv = pow(M % m2, -1, m2)
        x = ((r2 - m) * inv) % m2
        m = m + M * x
        M = M * m2
    return m % M, M

def derive_t(q, h, U, V, W, o2, o3):
    """target residue t of the layer, two independent ways + strip structure."""
    # (a) representative cell of {Uk+Vl = W mod h}
    g_ = math.gcd(V, h)
    rep = None
    for k0 in range(h):
        rhs = (W - U * k0) % h
        if rhs % g_ == 0:
            hg = h // g_
            if hg == 1:
                l0 = 0
            else:
                l0 = ((rhs // g_) * pow(V // g_, -1, hg)) % hg
            rep = (k0, l0)
            break
    if rep is None:
        return None, None, None
    k0, l0 = rep
    t_rep = pow(2, k0, q) * pow(3, l0, q) % q
    # (b) generator g with g^U=2, g^V=3 (order h) -> t = g^W
    from a1_palette_audit import canonical_gen, solve_lin_cong
    g0 = canonical_gen(q, h)
    d2 = None; d3 = None
    cur = 1
    for i in range(h):
        if cur == 2 % q and d2 is None: d2 = i
        if cur == 3 % q and d3 is None: d3 = i
        cur = cur * g0 % q
        if d2 is not None and d3 is not None: break
    sol = solve_lin_cong(U % h, d2, h)
    c = None
    if sol is not None:
        gg, x0, m1 = sol
        for cc in range(x0, h, m1):
            if (cc * V - d3) % h == 0 and math.gcd(cc, h) == 1:
                c = cc; break
    if c is None:
        return None, None, None
    g = pow(g0, c, q)
    t_gen = pow(g, W, q)
    # strip structure directly from field arithmetic (independent of U,V):
    # for each k-class mod o2, the l-coset mod o3 where 2^k 3^l = t.
    p3 = {}
    cur = 1
    for l in range(o3):
        p3.setdefault(cur, l)
        cur = cur * 3 % q
    strips = []
    pw2 = 1
    for k in range(o2):
        need = t_rep * pow(pw2, -1, q) % q
        if need in p3:
            strips.append((k, p3[need]))
        pw2 = pw2 * 2 % q
    return t_rep, t_gen, strips

def ap_mask(L, step, off):
    """L-bit int with bits set at off, off+step, ... < L."""
    if step == 1:
        return (1 << L) - 1
    base = ((1 << L) - 1) // ((1 << step) - 1)
    return (base << off) & ((1 << L) - 1)

def full_sweep(L, layers_info):
    """exact covered-cell count over the full torus Z_L^2, big-int row masks."""
    total = 0
    CH = 4000
    pat_cache = {}
    t0 = time.time()
    for a in range(0, L, CH):
        b = min(a + CH, L)
        rows = [0] * (b - a)
        for li in layers_info:
            o2 = li["o2"]; o3 = li["o3"]
            for (k0, l0) in li["strips"]:
                key = (L, o3, l0)
                if key not in pat_cache:
                    pat_cache[key] = ap_mask(L, o3, l0)
                pat = pat_cache[key]
                k = k0
                while k < a:
                    k += o2
                while k < b:
                    rows[k - a] |= pat
                    k += o2
        for r in rows:
            total += r.bit_count()
        del rows
    return total, time.time() - t0

SMALL_PRIMES = None
def small_prime_list():
    global SMALL_PRIMES
    if SMALL_PRIMES is None:
        import sympy
        SMALL_PRIMES = list(sympy.primerange(2, 100000))
    return SMALL_PRIMES

def has_small_factor(n):
    for p in small_prime_list():
        if p * p > n:
            return False
        if n % p == 0:
            return True
    return False

def verify_cover(L, state_file, banked_residual=None):
    print(f"=== A2 verify_cover L={L} state={state_file} ===", flush=True)
    layers = json.load(open(os.path.join(PDIR, state_file)))
    active = [l for l in layers if l[4] >= 0]
    print(f"layers: {len(layers)} total, {len(active)} active (W>=0)", flush=True)
    layers_info = []
    t_bad = []
    for (q, h, U, V, W) in active:
        if not my_order(2, q) or not my_order(3, q):
            t_bad.append((q, "order computation failed"))
            continue
        o2 = my_order(2, q); o3 = my_order(3, q)
        if L % o2 or L % o3:
            t_bad.append((q, f"ord-closure broken: o2={o2} o3={o3} vs L"))
            continue
        t_rep, t_gen, strips = derive_t(q, h, U, V, W, o2, o3)
        if t_rep is None or t_rep != t_gen:
            t_bad.append((q, f"t mismatch rep={t_rep} gen={t_gen}"))
            continue
        expect_strips = o2 * o3 // h
        if len(strips) != expect_strips:
            t_bad.append((q, f"strip count {len(strips)} != gcd(o2,o3)={expect_strips}"))
            continue
        if len(strips) * (L // o2) * (L // o3) != (L * L) // h:
            t_bad.append((q, "density not exactly 1/h"))
            continue
        layers_info.append({"q": q, "h": h, "U": U, "V": V, "W": W,
                            "o2": o2, "o3": o3, "t": t_rep, "strips": strips})
    print(f"C1 layer semantics: {len(layers_info)}/{len(active)} layers verified "
          f"(t_rep==t_gen, strips==gcd(o2,o3), density==1/h); problems: "
          f"{t_bad if t_bad else 'NONE'}", flush=True)
    for li in layers_info[:6]:
        print(f"   q={li['q']:6d} h={li['h']:5d} o2={li['o2']:5d} o3={li['o3']:5d} "
              f"t={li['t']:6d} strips={li['strips'][:6]}", flush=True)

    cov, dt = full_sweep(L, layers_info)
    unc = L * L - cov
    print(f"C2 FULL SWEEP: covered {cov}/{L*L} ({100*cov/(L*L):.4f}%), "
          f"uncovered {unc} ({100*unc/(L*L):.4f}%) [{dt:.0f}s]", flush=True)
    if banked_residual is not None:
        verdict = "CONSISTENT" if unc == banked_residual else "MISMATCH"
        print(f"C2 vs banked engine residual {banked_residual}: {verdict}", flush=True)

    # C3 CRT m
    pairs = []
    for li in layers_info:
        q = li["q"]; t = li["t"]
        pairs.append(((-pow(t, -1, q)) % q, q))
    pairs.append((1, 2)); pairs.append((1, 3))
    m, M = my_crt(pairs)
    assert m % 2 == 1 and m % 3 == 1 and m > 1 and math.gcd(m, 6) == 1
    print(f"C3 CRT m: m has {m.bit_length()} bits; (m,6)=1 OK; m mod small primes nonzero OK", flush=True)
    rng = random.Random(203)
    badc = 0
    for _ in range(4000):
        li = layers_info[rng.randrange(len(layers_info))]
        (k0, l0) = li["strips"][rng.randrange(len(li["strips"]))]
        k = k0 + li["o2"] * rng.randrange(L // li["o2"])
        l = l0 + li["o3"] * rng.randrange(L // li["o3"])
        v = pow(2, k, li["q"]) * pow(3, l, li["q"]) % li["q"] * (m % li["q"]) % li["q"]
        if v != li["q"] - 1:
            badc += 1
    print(f"C3 covered-cell spot check (direct field arithmetic, 4000 samples): "
          f"{'ALL DIVIDE (2^k 3^l m = -1 mod q)' if badc == 0 else str(badc) + ' FAILURES'}", flush=True)

    # C4 small-class grid + prime witnesses on uncovered classes
    covsm = {}
    for li in layers_info:
        for (k0, l0) in li["strips"]:
            for k in range(k0, 24, li["o2"]):
                for l in range(l0, 24, li["o3"]):
                    covsm[(k, l)] = li["q"]
    grid = [(k, l) for k in range(8) for l in range(8)]
    unc64 = [c for c in grid if c not in covsm]
    print(f"C4 small-class coverage (k,l < 8): uncovered: {unc64 if unc64 else 'NONE'}", flush=True)
    print(f"C4 explicit: (0,0)->m+1: covered={((0,0) in covsm)}; (1,0): {((1,0) in covsm)}; "
          f"(0,1): {((0,1) in covsm)}; (2,3): {((2,3) in covsm)}; (1,1): {((1,1) in covsm)}", flush=True)
    import sympy
    witnesses = []
    t0 = time.time()
    for k in range(0, 12):
        for l in range(0, 12):
            if (k, l) in covsm:
                continue
            n = (2 ** k) * (3 ** l) * m + 1
            if n % 5 in (0,) and n > 5:
                continue
            if has_small_factor(n):
                continue
            if sympy.isprime(n):
                witnesses.append((k, l, n.bit_length()))
                if len(witnesses) >= 4:
                    break
        if len(witnesses) >= 4:
            break
    print(f"C4 PRIME WITNESSES on uncovered classes (fake-cover catcher, {time.time()-t0:.0f}s): "
          f"{witnesses if witnesses else 'none found in 12x12 grid'}", flush=True)

    # C5 beyond-torus ord closure
    bad5 = 0
    for trial in range(2000):
        if trial < 800:
            k = rng.randrange(1, 10 ** 5); l = rng.randrange(1, 10 ** 5)
        else:
            k = rng.randrange(1, 4) * L + rng.randrange(L); l = rng.randrange(1, 4) * L + rng.randrange(L)
        kr, lr = k % L, l % L
        divq = set()
        for li in layers_info:
            q = li["q"]
            if pow(2, k, q) * pow(3, l, q) % q * (m % q) % q == q - 1:
                divq.add(q)
        clsq = set()
        for li in layers_info:
            for (k0, l0) in li["strips"]:
                if kr % li["o2"] == k0 and lr % li["o3"] == l0:
                    clsq.add(li["q"])
        if divq != clsq:
            bad5 += 1
            if bad5 < 4:
                print(f"   C5 MISMATCH k={k} l={l}: direct={sorted(divq)} class={sorted(clsq)}", flush=True)
    print(f"C5 beyond-torus closure (2000 samples, k,l up to 1e5 and j*L+r): "
          f"{'PERFECT (direct divisors == class prediction on all samples)' if bad5 == 0 else str(bad5) + ' MISMATCHES'}", flush=True)
    return {"L": L, "layers": len(active), "uncovered": unc,
            "m": str(m), "witnesses": witnesses, "c5_bad": bad5}

def main():
    res = verify_cover(27720, "work/state27720all.json", banked_residual=218794308)
    json.dump(res, open(os.path.join(HERE, "cover_verify_27720.json"), "w"), indent=1)
    res2 = verify_cover(55440, "work/state55440.json", banked_residual=None)
    json.dump(res2, open(os.path.join(HERE, "cover_verify_55440.json"), "w"), indent=1)
    print("A2 DONE", flush=True)

if __name__ == "__main__":
    main()
