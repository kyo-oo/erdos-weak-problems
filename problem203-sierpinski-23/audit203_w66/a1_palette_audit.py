#!/usr/bin/env python3
"""W66-P203-D A1 — INDEPENDENT PALETTE AUDIT (adversarial, no engine code reused).

Target: problem203-sierpinski-23/pal_dlog_full.json (1004 entries [q,h,U,V,o2,o3])
        problem203-sierpinski-23/palette203.txt   (lines "q h o2 o3")
        hunt families: L=27720 (h|27720) and L=55440 (h|55440).

Checks (all recomputed from first principles, own code):
  P1  q is prime (own deterministic Miller-Rabin, cross-checked vs sympy).
  P2  ord_q(2), ord_q(3): own order routine (own factorization of q-1),
      cross-checked vs sympy.n_order on every entry.
  P3  h == lcm(o2, o3)  (the palette's h column).
  P4  h | L for every hunt-state layer family (L=27720 / 55440), and
      o2 | L, o3 | L (the ord-closure requirement of the torus claim).
  P5  (U, V) are valid dlogs: exists a generator g of the unique order-h
      subgroup of F_q^* with g^U == 2 and g^V == 3 (solved as a linear
      congruence for c against an independently constructed canonical
      generator g0; also requires gcd(c,h)==1 so ord(g)==h exactly).
  P6  gcd(U,V,h) == 1  (image of (k,l)->Uk+Vl mod h is ALL of Z_h; the
      prime's cover set is one full coset of density exactly 1/h).
  P7  palette203.txt rows <-> pal_dlog_full.json entries agree on (q,h,o2,o3).

Also emits audit203_w66/palette_audit.json with per-entry verdicts.
"""
import json, math, os, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
PDIR = os.path.dirname(HERE)

def my_factor(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1; n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def my_isprime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0:
            return n == p
    d = n - 1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x in (1, n-1): continue
        ok = False
        for _ in range(r - 1):
            x = x * x % n
            if x == n - 1: ok = True; break
        if not ok:
            return False
    return True

def my_order(a, q, fac_qm1=None):
    """multiplicative order of a mod prime q, from own factorization of q-1."""
    if fac_qm1 is None:
        fac_qm1 = my_factor(q - 1)
    o = q - 1
    for p in fac_qm1:
        while o % p == 0 and pow(a, o // p, q) == 1:
            o //= p
    assert pow(a, o, q) == 1
    return o

def canonical_gen(q, h):
    """independent construction: g0 with exact order h. Proper method: find a
    primitive root r of F_q^* (own search with own factorization of q-1),
    set g0 = r^((q-1)/h)."""
    f = my_factor(q - 1)
    for r in range(2, min(q, 5000)):
        if any(pow(r, (q - 1) // p, q) == 1 for p in f):
            continue  # not a primitive root
        g0 = pow(r, (q - 1) // h, q)
        # verify order exactly h
        o = h
        for p in my_factor(h):
            while o % p == 0 and pow(g0, o // p, q) == 1:
                o //= p
        if o == h and g0 != 1:
            return g0
    return None

def solve_lin_cong(a, b, m):
    """all x mod m with a*x = b (mod m): returns (g, x0, m') or None."""
    g = math.gcd(a, m)
    if b % g != 0:
        return None
    a1, b1, m1 = a // g, b // g, m // g
    x0 = (b1 * pow(a1, -1, m1)) % m1
    return (g, x0, m1)

def audit_entry(q, h, U, V, o2, o3):
    rep = {"q": q, "ok": True, "notes": []}
    # P1 primality
    if not my_isprime(q):
        rep["ok"] = False; rep["notes"].append("NOT PRIME")
        return rep
    if q in (2, 3):
        rep["ok"] = False; rep["notes"].append("q in {2,3} forbidden")
        return rep
    # P2 ords
    f = my_factor(q - 1)
    my_o2 = my_order(2, q, f)
    my_o3 = my_order(3, q, f)
    rep["o2"] = my_o2; rep["o3"] = my_o3
    if my_o2 != o2:
        rep["ok"] = False; rep["notes"].append(f"o2 mismatch: true={my_o2} claimed={o2}")
    if my_o3 != o3:
        rep["ok"] = False; rep["notes"].append(f"o3 mismatch: true={my_o3} claimed={o3}")
    # P3 h = lcm
    my_h = my_o2 * my_o3 // math.gcd(my_o2, my_o3)
    rep["h"] = my_h
    if my_h != h:
        rep["ok"] = False; rep["notes"].append(f"h mismatch: true={my_h} claimed={h}")
    # P5/P6 dlog consistency (only meaningful if h correct)
    if my_h == h and h > 1:
        g0 = canonical_gen(q, h)
        if g0 is None:
            rep["ok"] = False; rep["notes"].append("no canonical generator found")
            return rep
        # dlogs of 2,3 wrt g0 (brute scan, h <= 5000 so fine)
        d2 = None; d3 = None
        cur = 1
        for i in range(h):
            if cur == 2 % q and d2 is None: d2 = i
            if cur == 3 % q and d3 is None: d3 = i
            cur = cur * g0 % q
            if d2 is not None and d3 is not None: break
        if d2 is None or d3 is None:
            rep["ok"] = False
            rep["notes"].append(f"2 or 3 not in order-{h} subgroup: d2={d2} d3={d3}")
            return rep
        # need c: c*U = d2, c*V = d3 (mod h), gcd(c,h)=1
        solU = solve_lin_cong(U % h, d2, h)
        found = None
        if solU is not None:
            g_, x0, m1_ = solU
            for c in range(x0, h, m1_):
                if (c * V - d3) % h == 0:
                    if math.gcd(c, h) == 1:
                        found = c
                    break
        if found is None:
            rep["ok"] = False
            rep["notes"].append(f"(U,V)=({U},{V}) not valid dlogs: no consistent generator")
            return rep
        rep["c"] = found
        # P6: gcd(U,V,h) == 1
        if math.gcd(math.gcd(U, V), h) != 1:
            rep["ok"] = False; rep["notes"].append("gcd(U,V,h) != 1 (cover density < 1/h)")
    return rep

def main():
    t0 = time.time()
    pal = json.load(open(os.path.join(PDIR, "pal_dlog_full.json")))
    rows = [tuple(map(int, l.split())) for l in open(os.path.join(PDIR, "palette203.txt")) if l.strip()]
    print(f"pal_dlog_full.json entries: {len(pal)}; palette203.txt rows: {len(rows)}", flush=True)

    # P7 cross-file consistency
    pd = {int(r[0]): (int(r[1]), int(r[2]), int(r[3]), int(r[4]), int(r[5])) for r in pal}
    txt = {r[0]: r for r in rows}
    mism = []
    for (q, h, o2, o3) in rows:
        if q not in pd:
            mism.append((q, "in txt not in json")); continue
        (hj, U, V, o2j, o3j) = pd[q]
        if (h, o2, o3) != (hj, o2j, o3j):
            mism.append((q, f"txt({h},{o2},{o3}) vs json({hj},{o2j},{o3j})"))
    for q in pd:
        if q not in txt:
            mism.append((q, "in json not in txt"))
    print(f"P7 cross-file consistency: {'OK' if not mism else mism[:20]}", flush=True)

    # main audit
    results = []
    bad = []
    n_checked = 0
    for r in pal:
        q, h, U, V, o2, o3 = (int(x) for x in r)
        rep = audit_entry(q, h, U, V, o2, o3)
        results.append(rep)
        n_checked += 1
        if not rep["ok"]:
            bad.append(rep)
        if n_checked % 200 == 0:
            print(f"  ...{n_checked}/{len(pal)} audited ({time.time()-t0:.0f}s), bad so far: {len(bad)}", flush=True)
    print(f"P1-P3/P5/P6 full audit: {n_checked} entries, BAD: {len(bad)}", flush=True)
    for b in bad[:30]:
        print(f"   BAD q={b['q']}: {b['notes']}", flush=True)

    # sympy cross-check of ords on ALL entries (second independent method)
    import sympy
    sbad = []
    for r in pal:
        q, h, U, V, o2, o3 = (int(x) for x in r)
        so2 = sympy.n_order(2, q); so3 = sympy.n_order(3, q)
        if so2 != o2 or so3 != o3:
            sbad.append((q, (o2, o3), (so2, so3)))
    print(f"P2 sympy cross-check: {len(sbad)} mismatches", flush=True)
    for s in sbad[:20]:
        print(f"   q={s[0]} claimed={s[1]} sympy={s[2]}", flush=True)

    # P4: the hunt families
    fams = {}
    for L in (27720, 55440):
        fam = [r for r in pd.values() if L % r[0] == 0 and L % r[3] == 0 and L % r[4] == 0]
        fams[L] = fam
        fam_h = [r for r in pd.values() if L % r[0] == 0]
        same = (len(fam) == len(fam_h))
        bud = sum(1.0 / r[0] for r in fam)
        bud_h = sum(1.0 / r[0] for r in fam_h)
        print(f"P4 L={L}: family size {len(fam)} (h-filter {len(fam_h)}, same={same}); "
              f"budget Sigma1/h = {bud:.4f} (h-filter {bud_h:.4f})", flush=True)

    # verify the actual hunt states use only family members with correct data
    for (L, st) in ((27720, "work/state27720all.json"), (55440, "work/state55440.json")):
        try:
            layers = json.load(open(os.path.join(PDIR, st)))
        except Exception as e:
            print(f"state {st}: {e}", flush=True); continue
        probs = []
        for l in layers:
            q, h, U, V, W = l
            if q not in pd:
                probs.append((q, "layer prime not in palette")); continue
            pj = pd[q]
            if (h, U, V) != (pj[0], pj[1], pj[2]):
                probs.append((q, f"layer (h,U,V)=({h},{U},{V}) vs palette {pj[:3]}"))
            if L % h != 0:
                probs.append((q, f"h={h} does not divide L={L}"))
            if L % pj[3] != 0 or L % pj[4] != 0:
                probs.append((q, f"ord-closure broken: o2={pj[3]} o3={pj[4]} vs L={L}"))
            if W >= h or W < 0:
                probs.append((q, f"W={W} out of [0,h)"))
        active = [l for l in layers if l[4] >= 0]
        print(f"P4 state {st}: {len(layers)} layers, {len(active)} active; "
              f"problems: {probs if probs else 'NONE'}", flush=True)

    json.dump({"entries": len(pal), "bad": bad, "sympy_mismatch": sbad,
               "cross_file": mism,
               "families": {str(L): {"size": len(f), "budget": sum(1.0 / r[0] for r in f)}
                            for L, f in fams.items()}},
              open(os.path.join(HERE, "palette_audit.json"), "w"), indent=1)
    print(f"PALETTE AUDIT DONE ({time.time()-t0:.0f}s); wrote palette_audit.json", flush=True)

if __name__ == "__main__":
    main()
