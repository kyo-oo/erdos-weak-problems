#!/usr/bin/env python3
"""
masterhunt203.py — W63-B3r2: THE BIG-MASTER HUNT (the missed territory of the
chain census).  Campaign law (chain203 + this round's derivation):

A covering of Z^2 by prime cosets factors through ONE master character
chi*(k,l) = A k + B l mod h*  <=>  every used prime q is ALIGNED:
Lambda_q >= ker chi*  <=>  (U_q, V_q) = w*(A, B) mod h_q for a UNIT w,
h_q | h*.  Then the 2D covering problem collapses EXACTLY to the classic
1D covering of Z/h* by one residue class per prime (modulus h_q, class
free), and CRT on the cosets gives m — the FULL kill route.

Alignment is a DIRECTION condition, evaluated prime-power by prime-power:
for each rational prime pi | h_q (gcd(U,V,h_q)=1 => min(v_pi U, v_pi V)=0):
  - type-C (U unit at pi):  slope c_q = V*U^{-1} mod pi^{e_q}, e_q=v_pi(h_q)
  - type-D (V unit, U|pi):  slope d_q = U*V^{-1} mod pi^{e_q}
A master class at pi^{E} (E = max e_q over the family) is (1, c) [c any]
or (d, 1) [d = 0 mod pi]; it matches prime q iff the classes agree mod
pi^{e_q}.  Choosing one class per rational pi (CRT) = choosing the master;
a prime joins the family iff it matches at EVERY pi | h_q.  The big-master
families (h* beyond the census's small-h* scan, which capped at 0.34) are
exactly these choices — this engine finds the MAXIMUM-WEIGHT one by
branch-and-bound over the pi-classes (exact), with the weight
sum_q 1/h_q (the 1D covering budget: >= 1 + slack is the kill bar).

Output: masterhunt203.json + console report.
"""
import json, math, os, sys, time
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "masterhunt203.json")

def log(s): print(s, flush=True)

def factor_small(x):
    fs = set(); d = 2
    while d * d <= x:
        while x % d == 0: fs.add(d); x //= d
        d += 1 if d == 2 else 2
    if x > 1: fs.add(x)
    return fs

def factor_full(x):
    fc = defaultdict(int); d = 2
    while d * d <= x:
        while x % d == 0: fc[d] += 1; x //= d
        d += 1 if d == 2 else 2
    if x > 1: fc[x] += 1
    return fc

def main():
    t0 = time.time()
    rows = json.load(open(os.path.join(HERE, "pal_dlog_full.json")))
    # rows: [p, h, U, V, o2, o3]
    W = [1.0 / r[1] for r in rows]
    total = sum(W)
    log(f"[palette] {len(rows)} primes, total budget {total:.4f}")

    # ---- per-prime pi-class data -------------------------------------
    # piinfo[pi] = dict: E (max exponent), members: list of (idx, type, slope mod pi^e, e)
    piinfo = {}
    for idx, r in enumerate(rows):
        p, h, U, V, o2, o3 = r
        for pi, e in factor_full(h).items():
            info = piinfo.setdefault(pi, {"E": 0, "members": []})
            if e > info["E"]: info["E"] = e
            m = pi ** e
            if U % pi != 0:
                slope = (V % m) * pow(U, -1, m) % m
                info["members"].append((idx, "C", slope, e))
            else:
                # V must be a unit at pi (gcd(U,V,h)=1)
                slope = (U % m) * pow(V, -1, m) % m
                info["members"].append((idx, "D", slope, e))
    # order pi's by descending content weight
    piorder = sorted(piinfo, key=lambda pi: -sum(W[i] for (i, _, _, _) in piinfo[pi]["members"]))
    log("[pi order] " + ", ".join(f"{pi}:{len(piinfo[pi]['members'])}" for pi in piorder[:14]))

    # ---- candidate master classes per pi (match lists) ---------------
    # cand[pi] = list of (frozenset(matched idx), weight) — deduped by signature
    cand = {}
    for pi in piorder:
        info = piinfo[pi]
        E = info["E"]; M = pi ** E
        mem = info["members"]
        cands = {}
        # type-C: c in Z/M  (matching C-members with slope ≡ c mod pi^{e})
        cmem = [(i, s, e) for (i, ty, s, e) in mem if ty == "C"]
        if cmem:
            for c in range(M):
                s_ = frozenset(i for (i, s, e) in cmem if s % (pi ** e) == c % (pi ** e))
                if s_: cands[("C", c)] = s_
        dmem = [(i, s, e) for (i, ty, s, e) in mem if ty == "D"]
        if dmem:
            for d in range(0, M, pi):
                s_ = frozenset(i for (i, s, e) in dmem if s % (pi ** e) == d % (pi ** e))
                if s_: cands[("D", d)] = s_
        # dedup by signature
        sig = {}
        for k, v in cands.items():
            sig.setdefault(v, []).append(k)
        cand[pi] = [(v, ks[0], sum(W[i] for i in v)) for v, ks in sig.items()]
        cand[pi].sort(key=lambda t: -t[2])
    for pi in piorder[:8]:
        log(f"  pi={pi}: {len(cand[pi])} distinct candidate classes (top w "
            f"{cand[pi][0][2]:.4f}, {len(cand[pi][0][0])} primes)")

    # ---- exact branch and bound over pi choices ----------------------
    best = {"weight": 0.0, "choice": {}}
    feasible0 = set(range(len(rows)))

    # greedy incumbent first
    def greedy():
        F = set(feasible0); w = 0.0; choice = {}
        for pi in piorder:
            if not F: break
            if pi not in cand: continue
            # pick candidate maximizing resulting F weight
            bestc = None
            for (v, k, cw) in cand[pi]:
                nv = (F & v) | (F - set(i for (i, _, _, _) in piinfo[pi]["members"]))
                nw = sum(W[i] for i in nv)
                if bestc is None or nw > bestc[0]:
                    bestc = (nw, k, nv)
            if bestc is None: continue
            F = bestc[2]; choice[pi] = bestc[1]
        w = sum(W[i] for i in F)
        return w, choice, F
    gw, gc, gF = greedy()
    best = {"weight": gw, "choice": gc, "family": sorted(gF)}
    log(f"[greedy incumbent] weight {gw:.4f} with {len(gF)} primes")

    # precompute pass-through sets: primes not containing pi
    passmask = {}
    for pi in piorder:
        passmask[pi] = feasible0 - set(i for (i, _, _, _) in piinfo[pi]["members"])

    stack_calls = [0]
    def bb(depth, F, wsofar, choice):
        stack_calls[0] += 1
        if stack_calls[0] % 20000 == 0:
            log(f"  ...bb {stack_calls[0]} calls, depth {depth}, best {best['weight']:.4f} "
                f"({time.time()-t0:.0f}s)")
        fw = sum(W[i] for i in F)
        if wsofar + fw <= best["weight"] + 1e-12:
            return
        if depth == len(piorder) or not F:
            if wsofar + fw > best["weight"] + 1e-12:
                best["weight"] = wsofar + fw
                best["choice"] = dict(choice)
                best["family"] = sorted(F | set())  # all remaining F are forced-in
                log(f"  [new best] {best['weight']:.4f} ({len(best['family'])} primes, "
                    f"depth {depth}, {time.time()-t0:.0f}s)")
            return
        pi = piorder[depth]
        pm = passmask[pi] & F
        tried_any = False
        for (v, k, cw) in cand[pi]:
            NF = (v & F) | pm
            tried_any = True
            choice[pi] = k
            bb(depth + 1, NF, wsofar, choice)
            del choice[pi]
        # also the "empty" class (no pi-member kept): NF = pm
        if True:
            bb(depth + 1, pm, wsofar, choice)
    bb(0, feasible0, 0.0, {})
    log(f"[bb done] {stack_calls[0]} calls; best {best['weight']:.4f}")

    # ---- construct + verify the master -------------------------------
    fam = best["family"]
    hstar = 1
    for i in fam: hstar = hstar * rows[i][1] // math.gcd(hstar, rows[i][1])
    # CRT the master (A,B) from per-pi classes
    A = B = 0
    for pi, k in best["choice"].items():
        E = piinfo[pi]["E"]; M = pi ** E
        ty, s = k
        if ty == "C": a, b = 1, s % M
        else: a, b = s % M, 1
        # CRT into (A,B) mod hstar_pi-part
        t = hstar // M
        inv = t * pow(t, -1, M)  # idempotent: t*inv ≡ 1 mod M and ≡ 0 mod t
        A += a * inv; B += b * inv
    A %= hstar; B %= hstar
    log(f"[master] h* = {hstar} ({hstar.bit_length()} bits), (A,B) = ({A},{B}) "
        f"surjective:{math.gcd(math.gcd(A, B), hstar) == 1}")

    def units_mod(h):
        return [c for c in range(1, h) if math.gcd(c, h) == 1]

    ok = 0; bad = []
    for i in fam:
        p, h, U, V, o2, o3 = rows[i]
        good = any((c * A - U) % h == 0 and (c * B - V) % h == 0 for c in units_mod(h))
        if good: ok += 1
        else: bad.append(rows[i])
    log(f"[verify] aligned members: {ok}/{len(fam)}" + (f"  BAD: {bad[:5]}" if bad else ""))

    out = {"weight": best["weight"], "n_family": len(fam), "hstar": hstar,
           "A": A, "B": B,
           "choice": {str(pi): [ty, s] for pi, (ty, s) in best["choice"].items()},
           "family": [rows[i][0] for i in fam],
           "family_rows": [rows[i] for i in fam],
           "greedy_weight": gw, "palette_total": total}
    json.dump(out, open(OUT, "w"))
    log(f"[done] wrote {OUT} ({time.time()-t0:.0f}s)")

if __name__ == "__main__":
    main()
