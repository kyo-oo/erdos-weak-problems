import math, time, json, sys
from math import gcd

def factor_strip(G, plim=2000000):
    """strip all prime factors < plim from G via sieve; return (list of (p,e), residual)"""
    sieve = bytearray(b'\x01')*(plim+1)
    sieve[0:2] = b'\x00\x00'
    for i in range(2, int(plim**0.5)+1):
        if sieve[i]:
            sieve[i*i::i] = b'\x00'*len(sieve[i*i::i])
    g = G; out = []
    for p in range(2, plim+1):
        if sieve[p] and g % p == 0:
            e = 0
            while g % p == 0: g //= p; e += 1
            out.append((p, e))
    return out, g

def closure_dlogs(q):
    """<2,3> mod q: BFS closure; then find generator g (order h) and dlogs U,V of 2,3.
    Returns (h, U, V) or None if 2 or 3 not invertible / group not cyclic-with-2,3."""
    if gcd(q, 6) != 1 or q < 5: return None
    S = {1}; frontier = [1]
    while frontier:
        x = frontier.pop()
        for y in (x*2 % q, x*3 % q):
            if y not in S: S.add(y); frontier.append(y)
    h = len(S)
    # find generator: an element of order h in S
    for g in S:
        # order of g
        o, x = 0, 1
        while True:
            x = x*g % q; o += 1
            if x == 1: break
        if o == h:
            # dlogs of 2 and 3
            U = V = None
            x, i = 1, 0
            while i < h:
                if x == 2 % q: U = i
                if x == 3 % q: V = i
                if U is not None and V is not None: break
                x = x*g % q; i += 1
            if U is not None and V is not None:
                return (h, U, V)
    return None

def build(L):
    t0 = time.time()
    G = math.gcd((1 << L) - 1, 3**L - 1)
    fac, resid = factor_strip(G)
    print(f"L={L}: gcd bits={G.bit_length()}, stripped primes={len(fac)}, residual bits={resid.bit_length()} ({time.time()-t0:.0f}s)")
    if resid > 1:
        import sympy
        t1 = time.time()
        rf = sympy.factorint(resid)
        print(f"  residual factored in {time.time()-t1:.0f}s: {[(p,e) for p,e in rf.items()]}")
        for p, e in rf.items():
            if p < 2000000: continue
            fac.append((p, e))
    fam = []
    for (p, e) in sorted(fac):
        for ee in range(1, e+1):
            q = p**ee
            r = closure_dlogs(q)
            if r is None:
                print(f"  q={q}: closure_dlogs FAILED"); continue
            h, U, V = r
            fam.append((q, h, U, V))
    # verify: index of lattice + modpow on basis
    def kernel_lattice(u, v, h):
        g0 = gcd(gcd(u, v), h)
        if g0 > 1: u//=g0; v//=g0; h//=g0
        g1 = gcd(u, v)
        if g1 == 0: return ((1,0),(0,1))
        old_r, r = u, v; old_s, s = 1, 0; old_t, t = 0, 1
        while r != 0:
            qq = old_r // r
            old_r, r = r, old_r - qq*r
            old_s, s = s, old_s - qq*s
            old_t, t = t, old_t - qq*t
        if old_r < 0: old_s, old_t = -old_s, -old_t
        s, t = old_s, old_t
        gg = gcd(g1, h); m1 = h // gg
        return (s*m1, t*m1), (-(v//g1), (u//g1))
    ok = True
    for (q, h, U, V) in fam:
        b1, b2 = kernel_lattice(U, V, h)
        det = abs(b1[0]*b2[1] - b1[1]*b2[0])
        def mp(k, l):
            a = pow(2, k, q) if k >= 0 else pow(pow(2, -k, q), -1, q)
            b = pow(3, l, q) if l >= 0 else pow(pow(3, -l, q), -1, q)
            return a*b % q
        if det != h or mp(*b1) != 1 or mp(*b2) != 1:
            ok = False; print(f"  VERIFY FAIL q={q}")
    budget = sum(1.0/h for (q,h,U,V) in fam)
    always = sum(1.0/(h//gcd(V,h)) for (q,h,U,V) in fam if gcd(V,h) == 1)
    print(f"  family size={len(fam)}, budget={budget:.4f}, always-active column budget={always:.4f} (need 1.0)")
    return fam

if __name__ == "__main__":
    for L in [int(x) for x in sys.argv[1:]] or [10080]:
        fam = build(L)
        for (q, h, U, V) in sorted(fam, key=lambda r: r[1]):
            gv = gcd(V, h); gu = gcd(U, h)
            print(f"  q={q:7d} h={h:5d} U={U:5d} V={V:5d} | g_v={gv:3d} m_l={h//gv:5d} g_u={gu:3d} m_k={h//gu:5d}")
        json.dump(fam, open(f"famL{L}.json", "w"))
        print(f"wrote famL{L}.json")
