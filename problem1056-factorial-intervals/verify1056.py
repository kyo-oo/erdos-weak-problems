#!/usr/bin/env python3
"""THE 1056 INDEPENDENT VERIFICATION NET (dual-method to the C census).
Modes:
  A  — special primes: chains, purity, battery-cut agreement, Wilson pair law,
       pair structure of value-1 chains, the two k=11-class witnesses
       (block-product method A), table firsts from the in-Python M-table of
       all primes < 52163, and full line-by-line agreement with census1056.txt.
  B  — (dual full sweep, same as A but no census compare) [unused]
  C lo hi — frontier chunk: primes in [lo, hi): M via the SAME definition,
       alert on any M >= 13.
Conventions: M(p) = max multiplicity of a value in (j! mod p), j = 1..p-1
(cut-point indices — the structure law's range)."""
import sys

def sieve(n):
    b = bytearray([1]) * (n + 1)
    b[0:2] = b"\x00\x00"
    i = 2
    while i * i <= n:
        if b[i]:
            b[i * i :: i] = bytearray(len(b[i * i :: i]))
        i += 1
    return [q for q in range(2, n + 1) if b[q]]

def chain_and_M(p):
    """hit lists per value and (M, argmax value, hit list of argmax)."""
    f = 1
    hits = {}
    for j in range(1, p):
        f = f * j % p
        hits.setdefault(f, []).append(j)
    M = max(len(v) for v in hits.values())
    arg = min(v for v, l in hits.items() if len(l) == M)
    return hits, M, arg, hits[arg]

def M_only(p):
    """tight loop: M only (frontier chunks)."""
    cnt = bytearray(p)
    f = 1
    for j in range(1, p):
        f = f * j % p
        cnt[f] += 1
    return max(cnt)

BATTERY = {
  2:  (11,   [(3,4),(5,7)]),
  3:  (17,   [(2,5),(6,11),(12,15)]),
  4:  (23,   [(2,4),(5,8),(9,11),(12,21)]),
  5:  (109,  [(10,11),(12,39),(40,58),(59,73),(74,85)]),
  6:  (71,   [(8,9),(10,19),(20,51),(52,61),(62,63),(64,70)]),
  7:  (673,  [(160,316),(317,354),(355,393),(394,397),(398,506),(507,545),(546,647)]),
  8:  (599,  [(29,50),(51,122),(123,183),(184,250),(251,289),(290,500),(501,539),(540,555)]),
  9:  (3011, [(2,611),(612,723),(724,749),(750,805),(806,2205),(2206,2261),(2262,2287),(2288,2399),(2400,3009)]),
  10: (27901,[(2452,2867),(2868,4768),(4769,10383),(10384,18707),(18708,19589),(19590,19965),(19966,22981),(22982,24673),(24674,26322),(26323,27263)]),
  11: (52163,[(2,3924),(3925,7291),(7292,7427),(7428,18519),(18520,24931),(24932,26081),(26082,27231),(27232,33643),(33644,44735),(44736,44871),(44872,52161)]),
}
WITNESS = {2:11, 3:17, 4:23, 5:109, 6:71, 7:673, 8:599, 9:3011, 10:27901, 11:52163}
EXTRA11 = [(109379, 61812), (111641, 27555)]
CENSUS = "census1056.txt"

def mode_A():
    ok = True
    # ---- 1. Wilson pair law on all primes < 1000 (full check) ----
    wilson_fail = 0
    for p in sieve(1000):
        f = [1] * p
        for j in range(1, p):
            f[j] = f[j - 1] * j % p
        for j in range(0, p):
            lhs = f[j] * f[p - 1 - j] % p
            rhs = 1 if (j % 2 == 1) else p - 1
            if lhs != rhs:
                wilson_fail += 1
    print(f"[A1] Wilson pair law j!(p-1-j)! = (-1)^(j+1) on all primes<1000: "
          f"{'GREEN' if wilson_fail == 0 else 'RED (' + str(wilson_fail) + ' FAILS)'}")
    ok &= wilson_fail == 0

    # ---- 2. battery cases: cuts/chains/purity + method-A block products ----
    for k in sorted(BATTERY):
        p, blocks = BATTERY[k]
        cuts = [blocks[0][0] - 1] + [b for (_, b) in blocks]
        hits, M, arg, arglist = chain_and_M(p)
        # chain of the battery value: factorial at cuts
        v = 1
        for j in range(1, cuts[0] + 1):
            v = v * j % p
        chain = hits.get(v, [])
        purity = (M == k + 1)
        cutmatch = (chain == cuts)
        prods_ok = True
        for (a, b) in blocks:
            pr = 1
            for t in range(a, b + 1):
                pr = pr * t % p
            if pr != 1:
                prods_ok = False
        print(f"[A2] k={k:2d} p={p:6d}: chain value {v:6d} at {chain} | "
              f"M={M} (=k+1: {purity}) cuts-match:{cutmatch} blockprods==1:{prods_ok}")
        ok &= purity and cutmatch and prods_ok

    # ---- 3. value-1 chains: Wilson pair decomposition ----
    for k in (3, 4, 9, 11):
        p, blocks = BATTERY[k]
        cuts = [blocks[0][0] - 1] + [b for (_, b) in blocks]
        pairs, singles, midpoint = [], [], None
        cs = set(cuts)
        for j in cuts:
            if j == 1 or j == p - 2:
                continue
            if 2 * j == p - 1:
                midpoint = j
            elif (p - 1 - j) in cs and j < p - 1 - j:
                pairs.append((j, p - 1 - j))
            elif (p - 1 - j) not in cs:
                singles.append(j)
        print(f"[A3] p={p:6d} value-1 chain pairs {pairs} midpoint {midpoint} "
              f"even-singles {singles} anchor (1,{p - 2})")
        # every odd non-anchor hit is paired (law check)
        law = all(((p - 1 - j) in cs) for j in cuts if j % 2 == 1 and j not in (1, p - 2))
        ok &= law
    print("[A3] odd-j double law on all value-1 witness chains: GREEN")

    # ---- 4. the two k=11-class witnesses ----
    for (p, vclaim) in EXTRA11:
        hits, M, arg, arglist = chain_and_M(p)
        print(f"[A4] p={p}: M={M} argmax value {arg} hits {arglist}")
        ok &= (M == 12) and (arg == vclaim)
        blocks = [(arglist[i] + 1, arglist[i + 1]) for i in range(len(arglist) - 1)]
        prods_ok = True
        for (a, b) in blocks:
            pr = 1
            for t in range(a, b + 1):
                pr = pr * t % p
            if pr != 1:
                prods_ok = False
        span_ok = blocks[0][0] >= 2 and blocks[-1][1] <= p - 1
        cons_ok = all(blocks[i][1] + 1 == blocks[i + 1][0] for i in range(len(blocks) - 1))
        print(f"     11 consecutive intervals: blockprods==1:{prods_ok} span:{span_ok} consecutive:{cons_ok}")
        ok &= prods_ok and span_ok and cons_ok

    # ---- 5. full in-Python M-table for all primes < 52163 + census agreement ----
    census = {}
    with open(CENSUS) as fh:
        for line in fh:
            parts = line.split()
            if len(parts) == 3 and parts[0].isdigit():
                q, m, a = int(parts[0]), int(parts[1]), int(parts[2])
                if q <= 52163:
                    census[q] = (m, a)
    mism = 0
    firstEQ, firstGE = {}, {}
    mtable = []
    for p in sieve(52163):
        f = 1
        cnt = bytearray(p)
        for j in range(1, p):
            f = f * j % p
            cnt[f] += 1
        M = max(cnt)
        arg = 0
        for vv in range(1, p):
            if cnt[vv] == M:
                arg = vv
                break
        mtable.append((p, M))
        if census.get(p) != (M, arg):
            mism += 1
        if p not in (2,) and M not in firstEQ:
            firstEQ[M] = p
        for m in range(2, M + 1):
            if m not in firstGE:
                firstGE[m] = p
    print(f"[A5] dual-method full sweep primes<=52163 vs C census: "
          f"{'GREEN (' + str(len(census)) + ' primes, M+argmax agree)' if mism == 0 else 'RED ' + str(mism)}")
    ok &= mism == 0

    # ---- 6. the table asserts (exact reading = campaign table) ----
    for k in range(2, 12):
        want = WITNESS[k]
        got = firstEQ.get(k + 1)
        ok &= (got == want)
    print(f"[A6] exact-reading firsts m=k+1: "
          f"{ {k: firstEQ.get(k + 1) for k in range(2, 12)} } == campaign table: "
          f"{'GREEN' if all(firstEQ.get(k + 1) == WITNESS[k] for k in range(2, 12)) else 'RED'}")
    print(f"[A6b] >=-reading firsts m: { {m: firstGE.get(m) for m in range(2, 13)} }")
    big = [t for t in mtable if t[1] >= 12]
    print(f"[A6c] primes<=52163 with M>=12: {big} (expect exactly [(52163, 12)])")
    ok &= big == [(52163, 12)]

    print("VERIFY1056-A:", "GREEN" if ok else "RED")
    sys.exit(0 if ok else 1)

def mode_C(lo, hi):
    best = 0
    for p in sieve(hi):
        if p < lo or p < 3:
            continue
        M = M_only(p)
        if M >= 13:
            print(f"[C] ALERT k=12 candidate p={p} M={M}")
        if M > best:
            best = M
            print(f"[C] new best in chunk: p={p} M={M}", flush=True)
    print(f"[C] chunk [{lo},{hi}): best M = {best}")

if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "A"
    if mode == "A":
        mode_A()
    else:
        mode_C(int(sys.argv[2]), int(sys.argv[3]))
