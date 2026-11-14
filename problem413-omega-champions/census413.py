#!/usr/bin/env python3
"""
ERDOS #413 — THE CHAMPION WINDOW LAW + CENSUS (Kernel 61b engine).

Problem (corpus /tmp/ep-statements/413.txt): let omega(n) = # distinct primes
dividing n.  Are there infinitely many n such that for all m < n,
    m + omega(m) <= n ?
Can one show exists eps > 0 with infinitely many n where
    m + eps*omega(m) <= n   for all m < n ?

CALL n a CHAMPION iff  forall 1 <= m < n : m + omega(m) <= n.

THE WINDOW LAW (this file's mathematical core, mirrored in Lean):
    n champion  <=>  forall j in [1, n-1] : omega(n-j) <= j      (m = n-j)
THE TRIVIAL TAIL (also mirrored):
    2^omega(m) <= m  (product of distinct primes divides m), hence
    2^j > n-j  =>  omega(n-j) < j, so the window is FINITE:
    n champion <=> omega(n-j) <= j for all 1 <= j <= J(n), J(n) = floor(log2 n)+1.

This engine:
  (1) sieve omega to N=20000 (spf-sieve) — method A;
  (2) replicate the EXACT Lean kernel definition (omegaScan/stripF with
      fuel) — method L; assert A == L on [0, N];
  (3) cross-check omega against sympy on [1, 500] + a strided sample;
  (4) champion census by THREE methods (must agree on every n <= N):
        M1 direct running-max:  n champion <=> G(n-1) <= n,
             G(x) = max_{1<=m<=x} (m+omega(m));
        M2 full window:   forall j in [1,n-1]: omega(n-j) <= j;
        M3 bounded window: forall j in [1,min(n-1,J(n))]: omega(n-j) <= j,
             J(n) = floor(log2 n)+1 = n.bit_length().
  (5) verify the tail law empirically: 2^omega(m) <= m for all m <= N,
      and that every j > J(n) row is vacuous (omega(n-j) <= j automatic);
  (6) classify champions (n-1 = p^a structure, j=1 law), tight rows,
      witnesses m (m + omega(m) = n), gaps;
  (7) the eps-relaxation census (eps = 1/k, k=2,3,4): integer form
        n eps-champion <=> forall m<n: k*m + omega(m) <= k*n
                           <=> forall j in [1,n-1]: omega(n-j) <= k*j.
  (8) emit the Lean kernel constants (oTab 0..30, champBoard) as snippets.

Receipt: census413_output.txt.
"""

import sys
from math import log2, floor

sys.setrecursionlimit(100000)

N = 20000

# ---------------------------------------------------------------- method A
# smallest-prime-factor sieve -> omega(m) for all m in [0, N]
spf = list(range(N + 1))          # spf[i] initialized to i; spf[0]=0, spf[1]=1
i = 2
while i * i <= N:
    if spf[i] == i:                # i prime
        for j in range(i * i, N + 1, i):
            if spf[j] == j:
                spf[j] = i
    i += 1

omegaA = [0] * (N + 1)
for m in range(2, N + 1):
    p = spf[m]
    r = m // p
    while r % p == 0:
        r //= p
    omegaA[m] = 1 + (omegaA[r] if r > 1 else 0)

# ---------------------------------------------------------------- method L
# EXACT replication of the Lean kernel definition (fuel semantics).

def stripF(fuel, d, r):
    # Lean: def stripF | 0, _, r => r | f+1, d, r => if r % d = 0 then stripF f d (r/d) else r
    f = fuel
    while f > 0:
        if r % d == 0:
            r = r // d
            f -= 1
        else:
            return r
    return r

def omegaScan(fuel, d, r, c):
    # Lean: def omegaScan | 0, _, _, c => c
    #       | f+1, d, r, c => if r <= 1 then c else if d > r then c
    #                        else if r % d = 0 then omegaScan f (d+1) (stripF (r+1) d r) (c+1)
    #                        else omegaScan f (d+1) r c
    f = fuel
    while f > 0:
        if r <= 1 or d > r:
            return c
        if r % d == 0:
            r = stripF(r + 1, d, r)
            c += 1
        d += 1
        f -= 1
    return c                     # fuel exhausted (count so far)

def omegaL(n):
    return omegaScan(n + 2, 2, n, 0)

# method A == method L (the Lean kernel computes the true omega)
mismatch = [m for m in range(0, N + 1) if omegaA[m] != omegaL(m)]
assert not mismatch, f"LEAN-DEF MISMATCH at {mismatch[:10]}"
print(f"[LAW-0] Lean omegaScan == spf-omega on [0,{N}] : ALL {N+1} ROWS AGREE")

# ---------------------------------------------------------------- sympy xcheck
import sympy
bad = []
for m in range(1, 501):
    if omegaA[m] != len(sympy.primefactors(m)):
        bad.append(m)
for m in range(501, N + 1, 37):
    if omegaA[m] != len(sympy.primefactors(m)):
        bad.append(m)
assert not bad, f"SYMPY MISMATCH at {bad[:10]}"
print(f"[XCHK ] sympy.primefactors agrees: all m<=500 + stride-37 sample to {N} : "
      f"{500 + len(range(501, N+1, 37))} rows OK")

# ---------------------------------------------------------------- tail law
tail_bad = [m for m in range(1, N + 1) if (1 << omegaA[m]) > m]
assert not tail_bad, f"TAIL LAW VIOLATION at {tail_bad[:10]}"
print(f"[LAW-1] TRIVIAL TAIL: 2^omega(m) <= m for ALL m in [1,{N}] : "
      f"{N} rows OK (=> window is finite, J(n)=floor(log2 n)+1)")

def J(n):
    return n.bit_length()         # floor(log2 n)+1 for n>=1

# vacuity check: for j > J(n), omega(n-j) <= j automatically (sanity of the tail cut)
vac_bad = []
for n in range(2, N + 1):
    for j in range(J(n) + 1, n):          # j in (J(n), n-1]
        if omegaA[n - j] > j:
            vac_bad.append((n, j))
            break
assert not vac_bad, f"VACUITY FAILURE {vac_bad[:5]}"
print(f"[LAW-1b] vacuity: for every n<= {N}, every j > J(n) has omega(n-j) <= j : OK")

# ---------------------------------------------------------------- census: 3 methods
def champ_M1(n):
    """direct: n champion iff max_{1<=m<=n-1} (m+omega(m)) <= n"""
    if n == 1:
        return True
    return G[n - 1] <= n

G = [0] * (N + 2)                 # running max of m+omega(m)
for m in range(1, N + 2):
    if m <= N:
        G[m] = max(G[m - 1], m + omegaA[m])
    else:
        G[m] = G[m - 1]

def champ_M2(n):
    """full window"""
    return all(omegaA[n - j] <= j for j in range(1, n))

def champ_M3(n):
    """bounded window (the LAW: only j <= J(n) matter)"""
    hi = min(n - 1, J(n)) if n >= 2 else 0
    return all(omegaA[n - j] <= j for j in range(1, hi + 1))

disagree = [n for n in range(1, N + 1) if len({champ_M1(n), champ_M2(n), champ_M3(n)}) != 1]
assert not disagree, f"METHOD DISAGREEMENT at {disagree[:10]}"
print(f"[LAW-2] WINDOW LAW: M1 (running max) == M2 (full window) == M3 (bounded window J(n)) "
      f"on every n in [1,{N}] : {N} rows AGREE")

champions = [n for n in range(1, N + 1) if champ_M1(n)]
print(f"[CENS] champions <= {N} : COUNT = {len(champions)}")
print(f"[CENS] champion list:\n{champions}")

# gaps
gaps = [champions[i+1] - champions[i] for i in range(len(champions)-1)]
print(f"[GAPS] gaps: {gaps}")
if gaps:
    print(f"[GAPS] max gap = {max(gaps)} (after {champions[gaps.index(max(gaps))]}), "
          f"mean gap = {sum(gaps)/len(gaps):.3f}")

# ---------------------------------------------------------------- structure
# j=1 law: every champion n>=3 has omega(n-1) <= 1 => n-1 is a prime power.
def prime_power(x):
    """return (p,a) with x=p^a if x is a prime power (x>=2), else None"""
    if x < 2:
        return None
    p = spf[x]
    y, a = x, 0
    while y % p == 0:
        y //= p
        a += 1
    return (p, a) if y == 1 else None

cls = []
for n in champions:
    if n <= 2:
        cls.append((n, "special (n-1 = 1)"))
        continue
    pp = prime_power(n - 1)
    cls.append((n, f"n-1 = {pp[0]}^{pp[1]}" if pp else "NOT A PRIME POWER"))
npp = [c for c in cls if "NOT" in c[1]]
assert not npp, f"J=1 LAW VIOLATION {npp[:5]}"
npr = sum(1 for n in champions if n >= 3 and prime_power(n - 1)[1] == 1)
npw = sum(1 for n in champions if n >= 3 and prime_power(n - 1)[1] >= 2)
print(f"[LAW-3] J=1: every champion n>=3 has n-1 = p^a. prime (a=1): {npr}, "
      f"proper power (a>=2): {npw}, specials n=1,2: {2}")
pw_examples = [c for c in cls if "proper" not in c[1] and "^" in c[1] and "^1" not in c[1]][:12]
print(f"[LAW-3b] champions with n-1 a PROPER prime power: {pw_examples}")

# converse failures: prime powers p^a with p^a+1 NOT champion
pfail = [(x + 1, x) for x in range(2, N) if prime_power(x) and not champ_M1(x + 1)]
print(f"[LAW-3c] converse FAILS: {len(pfail)} of {sum(1 for x in range(2,N) if prime_power(x))} "
      f"prime powers x=p^a have x+1 champion. first fails (n, n-1): {pfail[:12]}")

# tight rows: j where omega(n-j) == j (binding constraints)
tight = {}
for n in champions:
    if n < 3:
        continue
    tight[n] = [j for j in range(1, min(n - 1, J(n)) + 1) if omegaA[n - j] == j]
n_with_tight = [n for n in tight if tight[n]]
print(f"[TIGHT] champions with a TIGHT row (omega(n-j)==j): {len(n_with_tight)}/{len(tight)}")
print(f"[TIGHT] tight-row map (first 25): "
      f"{ {n: tight[n] for n in n_with_tight[:25]} }")
mt = max((len(tight[n]) for n in tight), default=0)
print(f"[TIGHT] max tight rows in one champion = {mt}")

# witnesses m: m + omega(m) = n (for champions n>=3, the argmax satisfies f(m)=n)
wits = {}
for n in champions:
    if n < 3:
        continue
    wits[n] = [m for m in range(1, n) if m + omegaA[m] == n]
print(f"[WIT ] every champion n>=3 is f(m)=m+omega(m) of some m<n: "
      f"{all(wits[n] for n in wits)}  (first 25: { {n: wits[n] for n in champions[:25] if n>=3} })")

# window width actually needed: max j with omega(n-j) tight... vs J(n)
need = {}
for n in champions:
    if n >= 3:
        hi = min(n - 1, J(n))
        need[n] = max([j for j in range(1, hi + 1) if omegaA[n - j] > j - 1], default=0)
mx = max(need.values())
print(f"[WIND] max window row that binds at all (omega(n-j) >= j): {mx}; "
      f"J(20000) = {J(20000)}, J(30) = {J(30)}")

# ---------------------------------------------------------------- eps-relaxation
# eps = 1/k: n eps-champion <=> forall 1<=m<n: k*m + omega(m) <= k*n <=> omega(n-j) <= k*j
print("[EPS ] eps-champions (m + eps*omega(m) <= n for all m<n), integer form:")
for k in (1, 2, 3, 4):
    ec = [n for n in range(1, N + 1)
          if all(omegaA[n - j] <= k * j for j in range(1, n))]
    print(f"[EPS ] eps=1/{k}: count<= {N} = {len(ec)}; head {ec[:32]}")
    # running-max cross-check for the eps form
    Gk = [0] * (N + 2)
    for m in range(1, N + 1):
        Gk[m] = max(Gk[m - 1], k * m + omegaA[m])
    ec2 = [n for n in range(1, N + 1) if n == 1 or Gk[n - 1] <= k * n]
    assert ec == ec2, f"EPS MISMATCH k={k}"

# window funnel: how deep does the window ACTUALLY need to be for n <= N?
print("\n[FUN ] window funnel (candidates passing window rows 1..k, n in [1,N]):")
pool = set(range(1, N + 1))
for k in range(1, 16):
    pool = {n for n in pool if n < 2 or all(omegaA[n - j] <= j for j in range(1, min(k, n - 1) + 1))}
    print(f"[FUN ] rows 1..{k}: {len(pool)} candidates  (champions among them: "
          f"{sum(1 for n in pool if champ_M1(n))})")
k4 = {n for n in range(1, N + 1)
      if n < 2 or all(omegaA[n - j] <= j for j in range(1, min(4, n - 1) + 1))}
bad4 = [n for n in k4 if not champ_M1(n)]
print(f"[FUN ] window cut at k=4 == full window? extra non-champions passing k=4: {len(bad4)}")
eff = max(j for n in range(2, N + 1) for j in range(1, min(n - 1, J(n)) + 1)
          if omegaA[n - j] > j - 1)  # deepest row that ever BINDS (omega >= j)
print(f"[FUN ] deepest binding row over ALL n <= {N} (omega(n-j) >= j): {eff}")

# ---------------------------------------------------------------- Lean constants
oTab = [omegaL(m) for m in range(0, 31)]
champBoard = [n for n in range(0, 31) if champ_M1(n)]
print("\n[LEAN] ---- kernel constants (paste into Erdos413.lean) ----")
rows = []
for s in range(0, 31, 10):
    chunk = " | ".join(f"{m} => {oTab[m]}" for m in range(s, min(s + 10, 31)))
    rows.append(f"  | {chunk}")
print("[LEAN] def oTab : Nat → Nat\n" + "\n".join(rows) + "\n  | _ => 0")
print(f"[LEAN] def champBoard : List Nat := {champBoard}")
print(f"[LEAN] omega table [0..30] = {oTab}")
print(f"[LEAN] (List.range 31).map omega = {oTab}")

# board mirror: the EXACT Lean board statements, n = k+1 in [1,30]
def champRow(n):
    return all(m + 1 + omegaL(m + 1) <= n for m in range(0, max(n - 1, 0)))
def windowRow(n):
    return all(omegaL(n - (j + 1)) <= j + 1 for j in range(0, max(n - 1, 0)))
def bWinRow(n):
    return all(omegaL(max(n - (k + 1), 0)) <= k + 1 for k in range(0, 5))  # Nat sub floors at 0
board_dual = all(champRow(n) == windowRow(n) for n in range(1, 31))
board_bnd = all(champRow(n) == bWinRow(n) for n in range(1, 31))
board_ex = all(champRow(n) == (n in champBoard) for n in range(1, 31))
assert board_dual and board_bnd and board_ex, "BOARD MIRROR FAILURE"
print("[LEAN] board mirror (n in [1,30], the exact Lean statements):")
print(f"[LEAN]   champRow == windowRow (all 30 rows) : {board_dual}")
print(f"[LEAN]   champRow == bWinRow(J=5)           : {board_bnd}")
print(f"[LEAN]   champRow == champBoard.contains    : {board_ex}")

# extra omega sanity rows for the kernel (beyond the board)
for m, v in [(1, 0), (2, 1), (30, 3), (210, 4), (2310, 5), (30030, 6)]:
    assert omegaL(m) == v == len(sympy.primefactors(m)), f"omega sanity {m}"
print("[LEAN] omega sanity rows: omega 1=0, 2=1, 30=3, 210=4, 2310=5, 30030=6 : OK")

print("\n[GREEN] CENSUS413_ALL_GREEN")
