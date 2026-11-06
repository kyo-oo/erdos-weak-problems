#!/usr/bin/env python3
"""K1 EVIDENCE ENGINE — Erdos #317 residue-lemma attack (S27-BETA).

K1   : for every n >= 5, is there a prime p in (n/2, n] with
       r_p(n) := (L_n / p) mod p  NOT in {1, p-1}?      (L_n = lcm(1..n))
K1'  : ... and the LARGEST prime p* <= n works whenever n is not prime.
K1'' : ... and for |P_n| >= 2, one of the two largest primes of P_n works.
       (P_n = primes in (n/2, n]; for |P_n| = 1, i.e. n in {6,10}, K1 itself
        is checked on the single prime.)

ENGINE (exact, no heuristics).  Single upward sweep with an active-prime
ledger.  Update rules (proved in K1_ATTACK.md, Lemma U):
  * n = q^a with a >= 2 (prime power): L_n = q * L_{n-1}, hence
        r_p(n) = q * r_p(n-1) mod p   for every active p
    (the base q <= sqrt(n) < n/2 < p, so q never equals an active prime).
  * n = p prime: L_n = p * L_{n-1}; the prime p ENTERS with
        r_p(p) = L_{n-1} mod p = lcm(1..p-1) mod p    ("self-residue" R_p).
  * all other n: L_n = L_{n-1}; every residue unchanged.
Active primes at n are {p prime : n/2 < p <= n}; p retires when 2p <= n.
Self-residues are read off an incrementally maintained big-int L_n
(~1.45*n bits: 29k bits at n=20000, cheap).  Degeneracy of an active prime
changes ONLY at events, so the per-n cost is O(1) except at prime powers.

Cross-check: for n <= CROSS the direct giant-lcm method must agree on every
active prime's residue (and residues must be nonzero).

Outputs (a)-(i) per the attack brief.  Run:  python3 k1_evidence.py [N]
"""
import math, time, bisect, sys

# ----------------------------------------------------------------------------- primes
def sieve_primes(N):
    s = bytearray([1]) * (N + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, math.isqrt(N) + 1):
        if s[i]:
            s[i * i :: i] = bytearray(len(s[i * i :: i]))
    return [i for i in range(2, N + 1) if s[i]]

# ----------------------------------------------------------------------------- engine
def run(N=20000, CROSS=300, SMALL_TABLE_MAX=60, TOP_TABLES=25):
    t0 = time.time()
    primes = sieve_primes(N)
    primeset = set(primes)

    # prime-power events: n = q^a (a >= 2)  ->  base q  (unique by factorization)
    event = {}
    for q in primes:
        if q * q > N:
            break
        m = q * q
        while m <= N:
            event[m] = q
            m *= q
    pp_sorted = sorted(event)

    ps, rs = [], []            # active primes / their residues r_p(n)
    h = 0                      # head pointer (retired prefix)
    Lbig = 1                   # lcm(1..n), big int
    degen = {}                 # p -> r  for currently degenerate active primes
    up0 = {}                   # p -> self-residue lcm(1..p-1) mod p
    selfdegen = []             # primes with self-residue in {1, p-1}

    w_arr = [0] * (N + 1); k_arr = [0] * (N + 1); d_arr = [0] * (N + 1)
    degen_occ = []             # (n, p, r, pos, k, flags)  flags: 1 largest,2 second,4 smallest,8 self-deg prime
    k1p_fail = []              # K1'  counterexamples
    k1pp_fail = []             # K1'' counterexamples
    n_with_degen = []
    tables = {}                # n -> full [(p, r)] for hard/small n
    compact = {}               # n -> (k, d, sorted degen dict)
    largest_wit = smallest_wit = tot_n = 0
    rank_hist = {}             # rank-from-top of shallowest witness prime
    uncovered = []             # n not covered by largest-prime propagation (Thm P)
    uncovered_rescued_by = []  # for uncovered n: (n, rank, second-largest witness?)
    Ldir = 1                   # cross-check lcm
    psi = 0.0; psi_arr = [0.0] * (N + 1)
    sign_psi = [0] * (N + 1)   # sign census of psi(n) - 2*psi(n//2)  (size wall map)

    for n in range(2, N + 1):
        # 1. retire primes with 2p <= n
        while h < len(ps) and 2 * ps[h] <= n:
            degen.pop(ps[h], None)
            h += 1
        # 2. prime-power event: multiply every active residue by the base
        if n in event:
            e = event[n]
            for i in range(h, len(ps)):
                p = ps[i]; r = (rs[i] * e) % p
                rs[i] = r
                if r == 1 or r == p - 1:
                    degen[p] = r
                else:
                    degen.pop(p, None)
        # 3. entering prime: L_n = L_{n-1} * n, so every OTHER active residue
        #    gets multiplied by n; then p = n itself enters with r = L_{n-1} mod n
        if n in primeset:
            for i in range(h, len(ps)):
                p = ps[i]; r = (rs[i] * n) % p
                rs[i] = r
                if r == 1 or r == p - 1:
                    degen[p] = r
                else:
                    degen.pop(p, None)
            u = Lbig % n                       # = lcm(1..n-1) mod n
            ps.append(n); rs.append(u)
            up0[n] = u
            if u == 1 or u == n - 1:
                selfdegen.append((n, u))
                degen[n] = u                   # entering prime can be degenerate at once
        # 4. stats
        k = len(ps) - h
        d = len(degen)
        if n >= 5:
            tot_n += 1
            k_arr[n] = k; d_arr[n] = d; w_arr[n] = k - d
            lp = ps[-1]; sp = ps[h]
            lw = lp not in degen
            sw = sp not in degen
            largest_wit += lw; smallest_wit += sw
            # rank-from-top of the shallowest witness (top-run of degenerates)
            j = 0
            while j < k and ps[h + k - 1 - j] in degen:
                j += 1
            rank_hist[j] = rank_hist.get(j, 0) + 1
            if d:
                n_with_degen.append(n)
                for p, r in degen.items():
                    pos = bisect.bisect_left(ps, p) - h
                    fl = (1 if p == lp else 0) | (2 if (k >= 2 and p == ps[-2]) else 0) \
                       | (4 if p == sp else 0) | (8 if up0.get(p) in (1, p - 1) else 0)
                    degen_occ.append((n, p, r, pos, k, fl))
                compact[n] = (k, d, sorted(degen.items()))
                if (d_arr[n] >= 3 and len(tables) < TOP_TABLES) or n <= SMALL_TABLE_MAX:
                    tables[n] = [(ps[i], rs[i]) for i in range(h, len(ps))]
            if k >= 2 and lp in degen and ps[-2] in degen:
                k1pp_fail.append((n, ps[-2], degen[ps[-2]], lp, degen[lp]))
            if (n not in primeset) and (lp in degen):
                i0 = bisect.bisect_right(pp_sorted, lp); i1 = bisect.bisect_right(pp_sorted, n)
                k1p_fail.append((n, lp, degen[lp], i1 - i0))
            # coverage by Theorem P (largest prime, no bumps)
            sd = up0.get(lp) in (1, lp - 1)
            i0 = bisect.bisect_right(pp_sorted, lp); i1 = bisect.bisect_right(pp_sorted, n)
            if sd or (i1 - i0) > 0:
                uncovered.append(n)
                uncovered_rescued_by.append((n, j, (k >= 2 and ps[-2] not in degen)))
        # 5. cross-check n <= CROSS against direct giant lcm
        if n <= CROSS:
            if n in primeset:
                assert up0[n] == Ldir % n, ("up0 mismatch", n)
            Ldir = Ldir * n // math.gcd(Ldir, n)
            for i in range(h, len(ps)):
                p = ps[i]; r = rs[i]
                dr = (Ldir // p) % p
                assert 1 <= r <= p - 1 and r == dr, ("residue mismatch", n, p, r, dr)
        # 6. big-int lcm + Chebyshev psi bookkeeping
        g = math.gcd(Lbig, n)
        psi += math.log(n // g)
        psi_arr[n] = psi
        sign_psi[n] = (psi - 2 * psi_arr[n // 2] > 0)
        Lbig = Lbig // g * n
        if n % 4000 == 0:
            print(f"  ... n={n}  ({time.time()-t0:.1f}s)", flush=True)

    # ------------------------------------------------------------------ analysis
    out = []
    A = out.append
    A("=" * 78)
    A(f"K1 EVIDENCE ENGINE — sweep n in [5, {N}]   ({time.time()-t0:.1f}s, "
      f"cross-checked vs giant lcm for n<={CROSS})")
    A("=" * 78)

    # (verdict on K1)
    bad = [n for n in range(5, N + 1) if w_arr[n] == 0]
    A(f"\n[K1 VERDICT] n in [5,{N}]: {'TRUE — every n has a witness prime' if not bad else 'FALSE at ' + str(bad)}")
    A(f"  total (n,p) residue tests = {sum(k_arr[5:N+1])}")

    # (a) witness density
    tot_k = sum(k_arr[5 : N + 1]); tot_d = sum(d_arr[5 : N + 1])
    A(f"\n[(a) DENSITY] total primes-in-window {tot_k}, degenerate {tot_d} "
      f"({100.0*tot_d/max(1,tot_k):.3f}%), witness density {100.0*(tot_k-tot_d)/max(1,tot_k):.3f}%")
    A("  per-1000 bucket: avg #primes in window | avg degenerate | avg witnesses | min witnesses")
    for b in range(5, N + 1, 1000):
        ns = range(b, min(b + 1000, N + 1))
        ks = [k_arr[x] for x in ns]; ds = [d_arr[x] for x in ns]; ws = [w_arr[x] for x in ns]
        A(f"   n in [{b:5d},{min(b+999,N):5d}]: {sum(ks)/len(list(ns)):7.1f} | "
          f"{sum(ds)/len(list(ns)):6.3f} | {sum(ws)/len(list(ns)):7.1f} | {min(ws)}")

    # (b) largest prime
    A(f"\n[(b) LARGEST PRIME] witness rate {largest_wit}/{tot_n} = {100.0*largest_wit/tot_n:.3f}%")
    A(f"  K1' counterexamples (n non-prime, largest prime degenerate): {len(k1p_fail)}")
    for t in k1p_fail[:60]:
        A(f"    n={t[0]}  p*={t[1]}  r={t[2]}  (self-deg prime: {up0.get(t[1]) in (1,t[1]-1)}; "
          f"prime powers in (p*,n]: {t[3]})")

    # (c) smallest prime
    A(f"\n[(c) SMALLEST PRIME IN WINDOW] witness rate {smallest_wit}/{tot_n} = {100.0*smallest_wit/tot_n:.3f}%")

    # (d) hardest n's
    mn = min(w_arr[5 : N + 1])
    hard = [n for n in range(5, N + 1) if w_arr[n] <= mn + 1]
    A(f"\n[(d) HARDEST n] min witness count = {mn}; n with w <= {mn+1}: {len(hard)}")
    for n in hard[:40]:
        if n in compact:
            k, d, dg = compact[n]
            A(f"    n={n}: k={k} witnesses={k-d} degenerate={dg} "
              f"(self-residues: {[(p, up0[p]) for p, _ in dg]})")
    A(f"  n's with >=1 degenerate prime: {len(n_with_degen)}")
    A(f"  rank-from-top of shallowest witness, histogram: {dict(sorted(rank_hist.items()))}")

    # (e) self-degenerate primes
    sd2000 = [(p, u) for (p, u) in selfdegen if p <= 2000]
    A(f"\n[(e) SELF-DEGENERATE PRIMES] lcm(1..p-1) = ±1 (mod p):")
    A(f"  p <= 2000 : {sd2000}")
    A(f"  p <= {N}  : count = {len(selfdegen)}  list = {selfdegen}")

    # (f) residue tables at hard n's
    A(f"\n[(f) FULL RESIDUE TABLES] (n's with >=3 degenerates, plus first sweeps)")
    shown = 0
    for n in sorted(tables, key=lambda x: -d_arr[x]):
        if d_arr[n] < 2 and shown >= 8: break
        k, d, dg = compact.get(n, (k_arr[n], d_arr[n], []))
        A(f"  n={n}  k={k}  degenerate={dg}")
        degset = {p for p, _ in dg}
        row = [(p, r, "*" if p in degset else "") for (p, r) in tables[n]]
        A("    " + " ".join(f"{p}:{r}{m}" for p, r, m in row[:40]) + (" ..." if len(row) > 40 else ""))
        shown += 1
        if shown >= 15: break

    # (g) clustering
    from collections import Counter
    cnt = Counter(d_arr[5 : N + 1])
    A(f"\n[(g) CLUSTERING] histogram of #degenerate primes per n: {dict(sorted(cnt.items()))}")
    mx = max(d_arr[5 : N + 1]); mxdn = [n for n in range(5, N + 1) if d_arr[n] == mx]
    A(f"  max simultaneous degenerates = {mx} at n = {mxdn}")
    for n in mxdn[:10]:
        k, d, dg = compact[n]
        pos = [bisect.bisect_left([p for p, _ in compact[n][2]], 0)]  # unused
        A(f"    n={n}: degenerate primes (p, r, self?) = "
          f"{[(p, r, up0.get(p) in (1, p-1)) for p, r in dg]}  k={k}")
    A(f"  K1'' counterexamples (two largest both degenerate): {len(k1pp_fail)}  {k1pp_fail[:10]}")

    # (h) propagation coverage (Theorem P)
    A(f"\n[(h) THEOREM P COVERAGE] n NOT covered by 'largest prime + no bumps' rule: {len(uncovered)}")
    if uncovered:
        A(f"  first 40: {uncovered[:40]}")
        rescued2 = sum(1 for (_, _, r2) in uncovered_rescued_by if r2)
        A(f"  of these, second-largest prime is a witness: {rescued2}/{len(uncovered)}")
        maxrank = max(r for (_, r, _) in uncovered_rescued_by)
        A(f"  max rank-from-top needed among uncovered: {maxrank}")

    # (i) size census (wall map: could an inequality kill full degeneracy?)
    up = sum(1 for n in range(5, N + 1) if sign_psi[n])
    A(f"\n[(i) SIZE CENSUS] #{'{'}n: psi(n) > 2*psi(n/2){'}'} = {up}/{N-4}  "
      f"(B(n)^2 vs L_n comparable — no size contradiction either way)")

    # degenerate stretches per prime
    per_p = {}
    for (n, p, r, pos, k, fl) in degen_occ:
        per_p.setdefault(p, []).append(n)
    lens = [len(v) for v in per_p.values()]
    A(f"\n[EXTRA] primes with >=1 degenerate n: {len(per_p)} of {len(primes)}; "
      f"degenerate-n's per such prime: min={min(lens) if lens else 0} "
      f"max={max(lens) if lens else 0}")
    worst = sorted(per_p.items(), key=lambda kv: -len(kv[1]))[:12]
    A(f"  most-often-degenerate primes: {[(p, len(v), v[:8]) for p, v in worst]}")
    # which positions in P_n do degenerates occupy?
    posc = Counter(pos for (_, _, _, pos, _, _) in degen_occ)
    toppos = Counter()
    for (n, p, r, pos, k, fl) in degen_occ:
        toppos["top" if fl & 1 else ("2nd" if fl & 2 else ("bot" if fl & 4 else "mid"))] += 1
    A(f"  degenerate occurrences by position: {dict(toppos)}; pos-in-window histogram (first 12): "
      f"{dict(sorted(posc.items())[:12])}")

    # ---- THEOREM D verification: every n where the LARGEST prime q2 <= n is
    # degenerate.  Let q1 = second largest prime <= n, d = q2 - q1.  With no
    # prime power in (q1, n]:  r_{q2}(n) = R_{q2}, r_{q1}(n) = R_{q1}*q2 (mod q1),
    # so BOTH degenerate  <=>  q2 self-degenerate AND d = +/- R_{q1}^{-1} (mod q1).
    # K1'' predicts the conjunction never holds.  Dump the audit table.
    A("\n[THEOREM D AUDIT] every n with largest prime degenerate (rank>=1):")
    A("  n | q2 | q1 | gap d | R_{q1} | forbidden d-values {+R^-1, -R^-1} | pp bases in (q1,n] | collision?")
    primelist = primes
    collisions = 0
    seen = set()
    for (n, p, r, pos, k, fl) in degen_occ:
        if not (fl & 1) or n in seen:
            continue
        seen.add(n)
        i2 = bisect.bisect_left(primelist, p)
        q2 = primelist[i2]; q1 = primelist[i2 - 1]; d = q2 - q1
        R1 = up0[q1]
        inv = pow(R1, -1, q1)
        forb = sorted({inv, q1 - inv})
        pps = [m for m in pp_sorted if q1 < m <= n]
        bases = [event[m] for m in pps]
        col = (d in forb) and not bases
        collisions += col
        A(f"  n={n}: q2={q2} q1={q1} d={d} R={R1} forb={forb} pp={bases} "
          f"{'COLLISION' if col else 'safe'} (r_q2={r}, self-deg q2: {up0[q2] in (1, q2-1)})")
    A(f"  TOTAL Theorem-D collisions (would break K1''): {collisions}")

    # sign correlation among simultaneous degenerates
    same = diff = 0
    for n in n_with_degen:
        _, _, dg = compact[n]
        if len(dg) >= 2:
            signs = [1 if r == 1 else -1 for (_, r) in dg]
            if len(set(signs)) == 1:
                same += 1
            else:
                diff += 1
    A(f"\n[SIGNS] simultaneous-degenerate n's with all same sign: {same}, mixed: {diff}")

    return "\n".join(out)


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    print(run(N=N))
