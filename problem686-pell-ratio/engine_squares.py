import math, time
t0 = time.time()

# ============================================================
# ENGINE - #686 SQUARE k=2 CENSUS (the divisor-pair scan law)
# Statement (erdosproblems.com/686): Can every integer N >= 2 be
# written as N = prod_{1<=i<=k}(m+i) / prod_{1<=i<=k}(n+i) for some
# k >= 2 and m >= n+k?
#
# In-house reading (consistent with K16/Kill #20): n >= 1.
# k=2, N = t^2:  (m+1)(m+2) = t^2 (n+1)(n+2).
# Sub X = 2m+3, Y = 2n+3 (odd, Y >= 5, X >= Y+2):
#     (X - tY)(X + tY) = 1 - t^2.
# d1 = X - tY < 0, d2 = X + tY > 0, d1*d2 = 1 - t^2.
# X = (d1+d2)/2, Y = (d2-d1)/(2t).
# FINITE scan per t: divisor pairs of t^2 - 1.
# ============================================================

def divisors(n):
    ds = []
    d = 1
    while d * d <= n:
        if n % d == 0:
            ds.append(d)
            if d != n // d:
                ds.append(n // d)
        d += 1
    return sorted(ds)

print("=" * 70)
print("THE SQUARE k=2 CENSUS — divisor-pair scan, t = 2..300")
print("=" * 70)
rep = {}
for t in range(2, 301):
    M = t * t - 1  # d1 * d2 = -(M)
    sols = []
    for d2 in divisors(M):          # d2 > 0, d1 = -(M/d2) < 0
        d1 = -(M // d2)
        s = d1 + d2
        diff = d2 - d1
        if s <= 0 or s % 2 != 0:
            continue
        if diff % (2 * t) != 0:
            continue
        X = s // 2
        Y = diff // (2 * t)
        if X % 2 != 1 or Y % 2 != 1:
            continue
        if Y < 5 or X < Y + 2:
            continue
        m, n = (X - 3) // 2, (Y - 3) // 2
        assert (m + 1) * (m + 2) == t * t * (n + 1) * (n + 2), (t, m, n)
        sols.append((m, n))
    if sols:
        rep[t] = sols

print(f"  k=2-representable squares t^2 (n >= 1), t <= 300: {len(rep)}")
print()
for t, sols in rep.items():
    tag = ""
    if t % 4 == 2 and t >= 10:
        tag = "[Thm B family]"
    else:
        tag = "[SPORADIC]"
    print(f"  t={t:3d}  N={t*t:7d}  sols={sols[:4]}"
          f"{' ...' if len(sols) > 4 else ''}  {tag}")

print()
print("=" * 70)
print("THE CENSUS LAW CHECK")
print("=" * 70)
fam = {t for t in rep if t % 4 == 2 and t >= 10}
spor = {t for t in rep if not (t % 4 == 2 and t >= 10)}
missing_fam = [t for t in range(10, 301, 4) if t % 4 == 2 and t not in rep]
# t % 4 == 2: t = 10, 14, ... i.e. t ≡ 2 mod 4
expected_fam = [t for t in range(2, 301) if t % 4 == 2 and t >= 10]
print(f"  family t ≡ 2 (mod 4), t >= 10: present {len(fam)}/{len(expected_fam)}"
      f"  missing: {missing_fam}")
print(f"  SPORADICS (t not ≡ 2 mod 4 or t < 10): {sorted(spor)}")
print(f"  first non-representable t after sporadics: "
      f"{[t for t in range(2, 60) if t not in rep]}")

print()
print("=" * 70)
print("CROSS-CHECK vs Thm B polynomial family (m = s^2-2, n = d+1)")
print("=" * 70)
ok = True
for t in expected_fam:
    s = t // 2  # t = 2s, s odd >= 5
    d = (s - 5) // 2
    m, n = s * s - 2, d + 1
    if (m + 1) * (m + 2) != t * t * (n + 1) * (n + 2):
        ok = False
        print(f"  THM B FAILS at t={t}")
    elif t in rep and (m, n) not in rep[t]:
        print(f"  t={t}: Thm B witness ({m},{n}) NOT in scan list?!")
print(f"  Thm B family identity + scan membership: {'ALL OK' if ok else 'FAIL'}")

print()
print("=" * 70)
print("t=99 SPORADIC VERIFICATION (the derivation's odd-t Pell find)")
print("=" * 70)
if 99 in rep:
    for (m, n) in rep[99]:
        print(f"  t=99: (m+1)(m+2) = {(m+1)*(m+2)} = "
              f"9801 * {(n+1)*(n+2)} = 9801*{(n+1)*(n+2)}: "
              f"{(m+1)*(m+2) == 9801*(n+1)*(n+2)}  (m={m}, n={n})")

print()
print(f"TOTAL: {time.time() - t0:.1f}s")
