#!/usr/bin/env python3
"""Erdos 411 battery: dual-method verification (pure Python - no sympy)."""
def phi(x):
    if x <= 1: return 1 if x == 1 else 0
    r, n, d = 1, x, 2
    while d * d <= n:
        if n % d == 0:
            e = 0
            while n % d == 0: n //= d; e += 1
            r *= (d - 1) * d ** (e - 1)
        d += 1 if d == 2 else 2
    if n > 1: r *= n - 1
    return r
def gstep(x): return x + phi(x)
def odd(x):
    while x % 2 == 0: x //= 2
    return x
SIX = {1, 3, 5, 7, 35, 47}
def chain_entry(m0, cap=150):
    m = m0
    for k in range(cap):
        if m in SIX: return k
        m = odd(2 * m + phi(m))
        if m.bit_length() > 220: return None
    return None
cnt = [0]
def ck(name, cond):
    cnt[0] += 1
    if not cond: raise SystemExit(f"BATTERY411 FAIL: {name}")
    print(f"  ok: {name}", flush=True)
sol = wander = 0
for n in range(4, 2001, 2):
    if chain_entry(odd(n)) is not None: sol += 1
    else: wander += 1
ck(f"census sol={sol} wander={wander}", sol == 535 and wander == 464)
bad = 0
for n in range(4, 2001, 2):
    k = chain_entry(odd(n))
    if k is None: continue
    x = n; traj = [x]
    for _ in range(k + 12): x = gstep(x); traj.append(x)
    if not all(traj[K+2] == 2*traj[K] for K in range(k, k+10)): bad += 1
ck("dual-method doubling (535 solutions)", bad == 0)
ok6 = True
for a in range(1, 31):
    p = 2 ** a
    ok6 &= gstep(p) == 3*2**(a-1)
    ok6 &= gstep(3*p) == 2**(a+2)
    ok6 &= gstep(5*p) == 7*p
    ok6 &= gstep(7*p) == 5*2**(a+1)
    ok6 &= gstep(35*p) == 47*p
    ok6 &= gstep(47*p) == 35*2**(a+1)
ck("six chain laws a=1..30", ok6)
for n, found in ((10, 0), (94, 0), (222, 7), (1998, 9)):
    x = n; traj = [x]
    for _ in range(60): x = gstep(x); traj.append(x)
    K = next((K for K in range(50) if all(traj[K+2+i] == 2*traj[K+i] for i in range(12))), None)
    ck(f"n={n} doubling K={K}", K == found)
for n in (130, 500, 1000):
    x = n; traj = [x]
    for _ in range(60): x = gstep(x); traj.append(x)
    K = next((K for K in range(50) if all(traj[K+2+i] == 2*traj[K+i] for i in range(12))), None)
    ck(f"n={n} no doubling in 60", K is None)
okp = True
for n in range(1, 500, 2):
    x = n
    for _ in range(100):
        if x >= 3: okp &= (x % 2 == 1)
        x = gstep(x)
ck("parity odds stay odd", okp)
ck("phi even for odd x in [3,499]", all(phi(x) % 2 == 0 for x in range(3, 500, 2)))
tbl = set(m0 for m0 in range(1, 1002, 2) if chain_entry(m0) is not None)
ck("solution odd parts = 221", len(tbl) == 221)
ck("first wanderers split", 65 not in tbl and 67 in tbl and 85 not in tbl)
print(f"BATTERY411 GREEN: {cnt[0]} checks")
