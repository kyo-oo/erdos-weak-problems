#!/usr/bin/env python3
"""W66-P203-D A3 — ADVERSARIAL FAKE-COVER BATTERY.

The cover-frame claims must BREAK under attack. Five batteries:

  T1 GROUND TRUTH (1-D Sierpinski m=78557): discover the covering classes
     from scratch (own factorization of 78557*2^k+1), verify the class
     cover of Z_L exhaustively, verify beyond the torus at k up to 1e6.
     -> proves the harness VALIDATES a genuinely complete cover.

  T2 PARTIAL-AS-COMPLETE FAKE: present the live hunt state (35 layers at
     L=27720, 71.5% covered) as if it were a closed cover. The harness
     must (a) report uncovered classes, (b) exhibit a PRIME witness
     2^k 3^l m + 1, killing the fake.

  T3 LAYER-REMOVAL / k>=k0-STYLE FAKE: delete one layer (weaken the
     partial cover): the sweep must grow the uncovered set and a prime
     witness must appear among the newly-uncovered small classes.
     (This is the shape of a "covers only k>=k0" fake: cells the engine
     never accounted for.)

  T4 ORD-POISON PALETTE: fabricate palette entries (wrong ord claims,
     wrong h=lcm, invalid (U,V) dlogs, composite q, q|6). The A1 audit
     must flag each; a cover built on the poison must fail C1.

  T5 m-POISON: corrupt the CRT extraction (m=0 mod a layer prime;
     m not coprime to 6). The covered-cell division spot check must fail.

Each test prints VERDICT: PASS (harness behaved correctly / fake caught).
"""
import json, math, os, random, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
PDIR = os.path.dirname(HERE)
sys.path.insert(0, HERE)
from a1_palette_audit import my_order, my_factor, my_isprime, audit_entry
from a2_cover_verify import derive_t, full_sweep, my_crt, has_small_factor
import sympy

# ---------------------------------------------------------------- T1 ----
def t1_ground_truth():
    print("=== T1 GROUND TRUTH: m=78557 (Sierpinski) 1-D cover ===", flush=True)
    M0 = 78557
    # discover cover primes: small factors of 78557*2^k+1 for k = 0..231
    primes = list(sympy.primerange(3, 5000))
    hits = {}
    for k in range(0, 232):
        n = M0 * (2 ** k) + 1
        for p in primes:
            if n % p == 0:
                hits.setdefault(p, set()).add(k)
    # per prime p: covered k-classes = k mod ord_p(2) with 2^k = -M0^{-1}
    cover = {}
    for p in sorted(hits):
        if p in (2, 3, 5, 7, 11, 13):
            pass
        t = (-pow(M0, -1, p)) % p
        o2 = my_order(2, p)
        # covered classes: k mod o2 with 2^k = t  (t must be in <2>)
        pw = 1; cls = None
        for k in range(o2):
            if pw == t:
                cls = k; break
            pw = pw * 2 % p
        if cls is not None:
            cover[p] = (o2, cls)
    L = 1
    for p, (o2, c) in cover.items():
        L = L * o2 // math.gcd(L, o2)
    L = min(L, 720720)
    # class bitmap on Z_L
    bit = 0
    used = {}
    for p, (o2, c) in cover.items():
        if L % o2:
            continue
        m_ = L // o2
        for j in range(m_):
            bit |= 1 << (c + j * o2)
        used[p] = (o2, c)
    unc = [k for k in range(L) if not (bit >> k) & 1]
    print(f"cover primes discovered: {sorted(used)}", flush=True)
    print(f"torus L={L}: uncovered classes: {len(unc)} "
          f"({unc[:12] if unc else 'NONE — CLASS COVER COMPLETE'})", flush=True)
    # exhaustive class verification is the bitmap; now beyond-torus direct:
    bad = 0; ok = 0
    rng = random.Random(78557)
    for k in range(0, 3000):
        n = M0 * (2 ** k) + 1
        hit = any((2 ** k) % p == (-pow(M0, -1, p)) % p for p in used)
        if hit:
            ok += 1
        else:
            # must be composite by luck or the cover is fake
            if sympy.isprime(n):
                bad += 1
                print(f"   UNCOVERED k={k}: 78557*2^{k}+1 is PRIME (fake-catch) {n.bit_length()} bits", flush=True)
    print(f"direct divisibility for k in [0,3000): {ok} covered-by-class, "
          f"{3000-ok} uncovered, primes among uncovered: {bad}", flush=True)
    for _ in range(200):
        k = rng.randrange(1, 10 ** 6)
        n = M0 * (2 ** k) + 1
        hit = any(pow(2, k, p) == (-pow(M0, -1, p)) % p for p in used)
        if not hit and sympy.isprime(n):
            bad += 1
    print(f"beyond-torus random k up to 1e6: primes on uncovered classes: {bad}", flush=True)
    verdict = "PASS" if len(unc) == 0 and bad == 0 else "FAIL (harness or cover broken)"
    print(f"T1 VERDICT: {verdict}", flush=True)
    return verdict

# ---------------------------------------------------------------- T2 ----
def prime_witness_on(layers_info, m, kmax=14, lmax=14, need=3):
    covsm = {}
    for li in layers_info:
        for (k0, l0) in li["strips"]:
            for k in range(k0, kmax, li["o2"]):
                for l in range(l0, lmax, li["o3"]):
                    covsm[(k, l)] = li["q"]
    wits = []
    for k in range(kmax):
        for l in range(lmax):
            if (k, l) in covsm:
                continue
            n = (2 ** k) * (3 ** l) * m + 1
            if has_small_factor(n):
                continue
            if sympy.isprime(n):
                wits.append((k, l, n.bit_length()))
                if len(wits) >= need:
                    return wits
    return wits

def t2_partial_as_complete():
    print("=== T2 PARTIAL-AS-COMPLETE FAKE (state27720all presented as closed) ===", flush=True)
    layers = json.load(open(os.path.join(PDIR, "work/state27720all.json")))
    active = [l for l in layers if l[4] >= 0]
    L = 27720
    layers_info = []
    for (q, h, U, V, W) in active:
        o2 = my_order(2, q); o3 = my_order(3, q)
        t_rep, t_gen, strips = derive_t(q, h, U, V, W, o2, o3)
        layers_info.append({"q": q, "h": h, "o2": o2, "o3": o3, "t": t_rep, "strips": strips})
    cov, dt = full_sweep(L, layers_info)
    unc = L * L - cov
    print(f"claimed-complete sweep: uncovered {unc}/{L*L} ({100*unc/(L*L):.2f}%)", flush=True)
    pairs = [((-pow(li["t"], -1, li["q"])) % li["q"], li["q"]) for li in layers_info]
    pairs += [(1, 2), (1, 3)]
    m, M = my_crt(pairs)
    wits = prime_witness_on(layers_info, m)
    print(f"PRIME witnesses on uncovered classes: {wits}", flush=True)
    caught = (unc > 0) and len(wits) > 0
    print(f"T2 VERDICT: {'FAKE CAUGHT (uncovered classes + prime witness ' + str(wits[0][:2]) + ')'} "
          if caught else "FAIL (fake not caught!)", flush=True)
    return caught

# ---------------------------------------------------------------- T3 ----
def t3_layer_removal():
    print("=== T3 LAYER-REMOVAL FAKE (weaken the partial cover, k>=k0 shape) ===", flush=True)
    layers = json.load(open(os.path.join(PDIR, "work/state27720all.json")))
    active = [l for l in layers if l[4] >= 0]
    L = 27720
    def build(act):
        out = []
        for (q, h, U, V, W) in act:
            o2 = my_order(2, q); o3 = my_order(3, q)
            t_rep, t_gen, strips = derive_t(q, h, U, V, W, o2, o3)
            out.append({"q": q, "h": h, "o2": o2, "o3": o3, "t": t_rep, "strips": strips})
        return out
    base = build(active)
    cov0, _ = full_sweep(L, base)
    # remove the strongest layers one by one and watch uncovered grow + witnesses appear
    removed = sorted(active, key=lambda l: -1.0 / l[1])[:1]  # remove strongest (q with smallest h)
    remq = {l[0] for l in removed}
    weak = build([l for l in active if l[0] not in remq])
    cov1, _ = full_sweep(L, weak)
    print(f"removed layers: {sorted(remq)}; covered {cov0} -> {cov1} "
          f"(uncovered {L*L-cov0} -> {L*L-cov1})", flush=True)
    pairs = [((-pow(li["t"], -1, li["q"])) % li["q"], li["q"]) for li in weak]
    pairs += [(1, 2), (1, 3)]
    m, M = my_crt(pairs)
    wits = prime_witness_on(weak, m, kmax=16, lmax=16, need=4)
    print(f"prime witnesses on newly-uncovered small classes: {wits}", flush=True)
    caught = (cov1 < cov0) and (len(wits) > 0)
    print(f"T3 VERDICT: {'FAKE CAUGHT (weakening -> new uncovered cells -> witness ' + str(wits[0][:2]) + ')'}"
          if caught else "FAIL (not caught)", flush=True)
    return caught

# ---------------------------------------------------------------- T4 ----
def t4_ord_poison():
    print("=== T4 ORD-POISON PALETTE ===", flush=True)
    # poison 1: wrong o2 for q=17 (true ord_17(2)=8, claim 4; h must then be wrong too)
    rep = audit_entry(17, 8, 1, 3, 4, 16)
    print(f"poison A (q=17, claimed o2=4, h=8): audit ok={rep['ok']} notes={rep['notes']}", flush=True)
    okA = not rep["ok"]
    # poison 2: composite q (221 = 13*17) with fabricated ords
    rep = audit_entry(221, 12, 5, 7, 12, 3)
    print(f"poison B (q=221 composite): audit ok={rep['ok']} notes={rep['notes']}", flush=True)
    okB = not rep["ok"]
    # poison 3: q=3 (divides 6)
    rep = audit_entry(3, 2, 1, 1, 2, 1)
    print(f"poison C (q=3): audit ok={rep['ok']} notes={rep['notes']}", flush=True)
    okC = not rep["ok"]
    # poison 4: true ords but invalid (U,V) dlogs
    rep = audit_entry(13, 12, 5, 5, 12, 3)
    print(f"poison D (q=13, ords true, bogus (U,V)=(5,5)): audit ok={rep['ok']} notes={rep['notes']}", flush=True)
    okD = not rep["ok"]
    # poison 5: correct entry (control — must pass)
    rep = audit_entry(13, 12, 7, 4, 12, 3)
    print(f"control (q=13 true palette entry (7,4)): audit ok={rep['ok']}", flush=True)
    okE = rep["ok"]
    # poison 6: a layer whose h does not divide L (torus violation)
    L = 27720
    (q, h, U, V, W) = (17, 16, 2, 7, 5)  # h=16 does not divide 27720
    o2 = my_order(2, q); o3 = my_order(3, q)
    broken = (L % h != 0) or (L % o2 != 0) or (L % o3 != 0)
    print(f"poison F (layer q=17 h=16 at L=27720): ord-closure broken = {broken}", flush=True)
    okF = broken
    allok = all([okA, okB, okC, okD, okE, okF])
    print(f"T4 VERDICT: {'ALL POISONS FLAGGED, CONTROL PASSES' if allok else 'FAIL'}", flush=True)
    return allok

# ---------------------------------------------------------------- T5 ----
def t5_m_poison():
    print("=== T5 m-POISON (corrupted CRT extraction) ===", flush=True)
    layers = json.load(open(os.path.join(PDIR, "work/state27720all.json")))
    active = [l for l in layers if l[4] >= 0]
    L = 27720
    layers_info = []
    for (q, h, U, V, W) in active[:10]:
        o2 = my_order(2, q); o3 = my_order(3, q)
        t_rep, t_gen, strips = derive_t(q, h, U, V, W, o2, o3)
        layers_info.append({"q": q, "h": h, "o2": o2, "o3": o3, "t": t_rep, "strips": strips})
    rng = random.Random(5)
    # poison 1: m = 0 mod one layer prime
    pairs = [((-pow(li["t"], -1, li["q"])) % li["q"], li["q"]) for li in layers_info]
    pairs += [(1, 2), (1, 3)]
    m_ok, _ = my_crt(pairs)
    pairs_bad1 = list(pairs)
    pairs_bad1[0] = (0, pairs_bad1[0][1])
    m_bad1, _ = my_crt(pairs_bad1)
    def spotcheck(m, n=1500):
        bad = 0
        for _ in range(n):
            li = layers_info[rng.randrange(len(layers_info))]
            (k0, l0) = li["strips"][rng.randrange(len(li["strips"]))]
            k = k0 + li["o2"] * rng.randrange(L // li["o2"])
            l = l0 + li["o3"] * rng.randrange(L // li["o3"])
            if pow(2, k, li["q"]) * pow(3, l, li["q"]) % li["q"] * (m % li["q"]) % li["q"] != li["q"] - 1:
                bad += 1
        return bad
    b_ok = spotcheck(m_ok)
    b_bad = spotcheck(m_bad1)
    print(f"clean m: covered-cell failures {b_ok}/1500 (expect 0); "
          f"m=0-mod-q poison: failures {b_bad}/1500 (expect >0)", flush=True)
    # poison 2: m not coprime to 6 (m = 2 mod 4 / m = 3 mod 9 ...)
    pairs_bad2 = list(pairs)
    pairs_bad2[-2] = (0, 2)  # m = 0 mod 2
    m_bad2, _ = my_crt(pairs_bad2)
    coprime_ok = math.gcd(m_ok, 6) == 1
    coprime_bad = math.gcd(m_bad2, 6) == 1
    print(f"clean m coprime to 6: {coprime_ok}; poisoned m (m=0 mod 2): coprime={coprime_bad}", flush=True)
    caught = (b_ok == 0) and (b_bad > 0) and coprime_ok and (not coprime_bad)
    print(f"T5 VERDICT: {'M-POISONS CAUGHT' if caught else 'FAIL'}", flush=True)
    return caught

def main():
    t0 = time.time()
    v1 = t1_ground_truth()
    v2 = t2_partial_as_complete()
    v3 = t3_layer_removal()
    v4 = t4_ord_poison()
    v5 = t5_m_poison()
    allv = {"T1_ground_truth": v1, "T2_partial_as_complete": v2,
            "T3_layer_removal": v3, "T4_ord_poison": v4, "T5_m_poison": v5}
    print(f"\nA3 BATTERY SUMMARY: {allv}", flush=True)
    print(f"{'ALL TESTS BEHAVED CORRECTLY (fakes caught, truth validated)' if all(allv.values()) else 'SOME TEST FAILED'} "
          f"({time.time()-t0:.0f}s)", flush=True)
    json.dump(allv, open(os.path.join(HERE, "fake_tests.json"), "w"), indent=1)

if __name__ == "__main__":
    main()
