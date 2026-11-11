#!/usr/bin/env python3
"""S27-BETA2 — INDEPENDENT verification of Theorems G / D / P (Erdos #317, K1 attack).

Fresh implementation: NO incremental residue ledger, exact big-int lcm(1..n)
maintained directly.  Cross-validates the engine (k1_evidence.py) and the
mathematical claims of K1_ATTACK.md:

  THEOREM G (master residue formula).  For prime p with sqrt(n) < p <= n:
      r_p(n) := (L_n/p) mod p  ==  R_p * prod{ base(q) : q^a in (p,n], a>=1 }  (mod p)
  where R_p = lcm(1..p-1) mod p and the product runs over ALL prime powers in
  (p,n] (a = 1 powers = the primes above p, contributing themselves).

  THEOREM D (two-largest specialization).  q2 = largest prime <= n, q1 = second
  largest WINDOW prime, d = q2-q1, B = prod bases of pp (a>=2) in (q2,n],
  B' = prod bases of pp (a>=2) in (q1,q2):
      (i)  r_{q2}(n) = R_{q2} * B  (mod q2)
      (ii) r_{q1}(n) = R_{q1} * B' * d * B  (mod q1)
  Both two-largest degenerate <=> R_{q2}*B = +-1 (mod q2) AND R_{q1}*B'*d*B = +-1 (mod q1).

  THEOREM P.  If R_{q2} not in {1,q2-1} and no prime power (a>=2) lies in (q2,n],
  then q2 is a K1-witness at n.

Checks performed (all EXACT):
  V1  Theorem G for every window prime of every n <= FULLK, and for random
      window-prime samples at 300 large n up to N.
  V2  self-degenerate primes R_p in {1,p-1} for all p <= N (direct big-int).
  V3  r_{q2}(n) computed DIRECTLY for every n in [5,N]; all n with largest
      window prime degenerate -> full Theorem-D audit row, incl. (i),(ii) check.
  V4  K1'' at every n <= N: both two largest window primes directly (no appeal
      to Theorem G at all).  K1 (all window primes) directly for n <= FULLK.
  V5  uncovered set (Thm P complement) recomputed; the n's where the second
      largest window prime is NOT a rescuer identified.
  V6  hand-verification values (R_37, R_47, R_53, R_163, R_167, ...) and the
      small-n table n in [5,12].

Run:  python3 k1_theoremD_check.py [N=300000] [FULLK=20000]
"""
import math, random, sys, time
from bisect import bisect_left, bisect_right

t0 = time.time()
N     = int(sys.argv[1]) if len(sys.argv) > 1 else 300000
FULLK = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
NSAMP = 300
random.seed(317317)

# ---------------- primes, prime powers, largest-prime array ----------------
s = bytearray([1]) * (N + 2)
s[0:2] = b"\x00\x00"
for i in range(2, math.isqrt(N + 1) + 1):
    if s[i]:
        s[i * i :: i] = bytearray(len(s[i * i :: i]))
primes = [i for i in range(2, N + 1) if s[i]]
isprime = s

ppv, ppbase = [], {}                      # prime powers q^a (a>=2) <= N
for q in primes:
    if q * q > N:
        break
    m = q * q
    while m <= N:
        ppv.append(m); ppbase[m] = q
        m *= q
ppv.sort()

lp = [0] * (N + 1)                        # largest prime <= n
for n in range(2, N + 1):
    lp[n] = n if isprime[n] else lp[n - 1]

sample_ns = sorted({random.randint(FULLK + 1, N) for _ in range(4 * NSAMP)})[:NSAMP]

# ---------------- sweep ----------------
R = {}                    # p -> lcm(1..p-1) mod p
L = 1
audit_rows = []           # (n, q2, r2, q1, r1, d, B, Bp, forbidden, clean, dinforb)
k1_fail, k1pp_fail = [], []
uncovered = []            # (n, q2, q1w, r1w_or_None)
not_rescued = []
g_checked = g_bad = 0
window_scan_n = window_scan_bad = 0
r2_all_checked = r2_all_bad = 0
samp_done = 0

# quick helper: events (value, base) for a<=1 prime powers = primes, a>=2 = ppv
def window_events(n):
    """all (value, base) with value in (n/2, n]: primes (base=itself) + pp a>=2."""
    i = bisect_right(primes, n // 2)
    ev = [(p, p) for p in primes[i: bisect_right(primes, n)]]
    j0 = bisect_right(ppv, n // 2); j1 = bisect_right(ppv, n)
    ev += [(ppv[j], ppbase[ppv[j]]) for j in range(j0, j1)]
    ev.sort(reverse=True)
    return ev

Lfull = {}                # n<=FULLK need L_n; keep in loop instead
for n in range(1, N + 1):
    g = math.gcd(L, n)
    L = L // g * n                       # L = lcm(1..n) exactly
    if n + 1 <= N and isprime[n + 1]:
        R[n + 1] = L % (n + 1)           # lcm(1..p-1) mod p
    if n < 5:
        continue

    q2 = lp[n]
    r2 = (L // q2) % q2                  # DIRECT
    r2_all_checked += 1
    if not (1 <= r2 <= q2 - 1):
        r2_all_bad += 1
    deg2 = r2 == 1 or r2 == q2 - 1

    # second-largest window prime
    idx = bisect_left(primes, q2)
    q1 = primes[idx - 1] if idx >= 1 and 2 * primes[idx - 1] > n else None
    r1 = (L // q1) % q1 if q1 else None
    deg1 = r1 is not None and (r1 == 1 or r1 == q1 - 1)

    # uncovered (Thm P complement) & rescue status
    i0 = bisect_right(ppv, q2); i1 = bisect_right(ppv, n)
    B = 1
    for j in range(i0, i1):
        B *= ppbase[ppv[j]]
    sd = R.get(q2) in (1, q2 - 1)
    if sd or (i1 - i0) > 0:
        uncovered.append((n, q2, q1))
        if not (q1 and not deg1):
            not_rescued.append((n, q2, r2, q1, r1))
    if deg2:
        if q1 and deg1:
            k1pp_fail.append((n, q2, r2, q1, r1))
        # Theorem D audit row
        d = q2 - q1 if q1 else None
        Bp = 1
        if q1:
            k0 = bisect_right(ppv, q1); k1_ = bisect_right(ppv, q2)
            for j in range(k0, k1_):
                Bp *= ppbase[ppv[j]]
        forb = clean = din = None
        if q1 and d is not None:
            inv = pow(R[q1], -1, q1)
            forb = sorted({inv, q1 - inv})
            clean = (Bp == 1 and B == 1)
            din = d in forb
        # verify (i) and (ii)
        ok_i = (R[q2] * B) % q2 == r2
        ok_ii = (q1 is None) or ((R[q1] * Bp * d * B) % q1 == r1)
        audit_rows.append((n, q2, r2, q1, r1, d, B, Bp, forb, clean, din, ok_i, ok_ii))

    # ---- full window scan + Theorem G for n <= FULLK ----
    if n <= FULLK:
        ev = window_events(n)
        wi = bisect_right(primes, n // 2)
        win = primes[wi: bisect_right(primes, n)]
        acc = 1; ei = 0; witnesses = len(win)
        for p in reversed(win):          # descending
            while ei < len(ev) and ev[ei][0] > p:
                acc = acc * ev[ei][1]    # exact big product
                ei += 1
            rp = (L // p) % p
            if rp == 1 or rp == p - 1:
                witnesses -= 1
            g_checked += 1
            if (R[p] * acc) % p != rp:
                g_bad += 1
                if g_bad <= 5:
                    print(f"  G-FAIL n={n} p={p}: direct={rp} formula={(R[p]*acc)%p}")
        window_scan_n += 1
        if witnesses == 0:
            k1_fail.append(n)
    elif sample_ns and n == sample_ns[0]:
        sample_ns.pop(0)
        ev = window_events(n)
        wi = bisect_right(primes, n // 2)
        win = primes[wi: bisect_right(primes, n)]
        sel = set(random.sample(win, min(40, len(win))))
        acc = 1; ei = 0; samp_done += 1
        for p in reversed(win):
            while ei < len(ev) and ev[ei][0] > p:
                acc = acc * ev[ei][1]
                ei += 1
            if p in sel:
                rp = (L // p) % p
                g_checked += 1
                if (R[p] * acc) % p != rp:
                    g_bad += 1
                    print(f"  G-FAIL(sample) n={n} p={p}: direct={rp} formula={(R[p]*acc)%p}")

    if n % 50000 == 0:
        print(f"  ... n={n}  ({time.time()-t0:.1f}s)", flush=True)

# ---------------- report ----------------
out = []
A = out.append
A("=" * 76)
A(f"THEOREM G/D/P INDEPENDENT CHECK — N={N}, FULLK={FULLK}  ({time.time()-t0:.1f}s)")
A("=" * 76)

A(f"\n[V1 Theorem G] identity checks: {g_checked}, failures: {g_bad}  "
  f"(full windows n<={FULLK}: {window_scan_n} n's; large samples: {samp_done})")
A(f"[V3] direct r_{{q2}}(n) computed for all n in [5,{N}]: {r2_all_checked} values, "
  f"out-of-range (bug): {r2_all_bad}")

sd_list = [(p, R[p]) for p in primes if R[p] == 1 or R[p] == p - 1]
A(f"\n[V2 SELF-DEGENERATE PRIMES p<={N}] (R_p = lcm(1..p-1) mod p = +-1): {sd_list}")

A(f"\n[V4] K1  failures (no witness prime at all), n<={FULLK}: {k1_fail}")
A(f"[V4] K1'' failures (two largest window primes both degenerate), n<={N}: {k1pp_fail}")
A(f"  n's with largest window prime degenerate: {len(audit_rows)}; "
  f"Theorem D (i) verified: {sum(1 for r in audit_rows if r[11])}/{len(audit_rows)}, "
  f"(ii) verified: {sum(1 for r in audit_rows if r[12])}/{len(audit_rows)}")

A(f"\n[V3 THEOREM D AUDIT — all largest-window-prime-degenerate n <= {N}:")
A("  n | q2 r2 | q1 r1 | d | B' | B | forbidden {+-R^-1} | clean? d-in-forb?")
for (n, q2, r2, q1, r1, d, B, Bp, forb, clean, din, ok_i, ok_ii) in audit_rows:
    A(f"  n={n}: q2={q2} r2={r2} | q1={q1} r1={r1} | d={d} | B'={Bp} B={B} | "
      f"forb={forb} | clean={clean} d_in_forb={din} | Di={ok_i} Dii={ok_ii} "
      f"{'*** COLLISION ***' if (din and clean) else ''}")

A(f"\n[V5 Theorem P coverage] uncovered n <= {N}: {len(uncovered)}")
A(f"  of these, second-largest window prime is NOT a rescuer: {len(not_rescued)}")
for t in not_rescued:
    A(f"    n={t[0]}: q2={t[1]} r_q2={t[2]} | q1={t[3]} r_q1={t[4]}")

A("\n[V6 hand-check values]")
for p in (5, 7, 11, 29, 37, 47, 53, 163, 167, 331, 337, 773, 787, 15767, 15773):
    if p in R:
        A(f"  R_{p} = lcm(1..{p-1}) mod {p} = {R[p]}"
          + ("   <- self-degenerate" if R[p] in (1, p - 1) else ""))

A("\n[V6 small-n table (n in [5,12]): window primes and residues]")
for n in range(5, 13):
    pass
# recompute small table exactly (cheap)
Ls = 1; rows = []
for n in range(1, 13):
    Ls = Ls // math.gcd(Ls, n) * n
    if n >= 5:
        win = [p for p in range(2, n + 1) if isprime[p] and 2 * p > n]
        rows.append((n, [(p, (Ls // p) % p) for p in win]))
for n, wr in rows:
    wit = [p for (p, r) in wr if r != 1 and r != p - 1]
    A(f"  n={n}: window={wr}  witnesses={wit}")

print("\n".join(out))
with open("k1_theoremD_check_output.txt", "w") as f:
    f.write("\n".join(out) + "\n")
print(f"\n[saved to k1_theoremD_check_output.txt; {time.time()-t0:.1f}s total]")
