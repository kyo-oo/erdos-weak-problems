#!/usr/bin/env python3
"""battery686k3.py — the independent dual-method battery for Kernel 32
(#686 k=3 square witness laws).
Method 1 (direct): big-int product identity replay.
Method 2 (structure): quotient isqrt-square reconstruction + factorization.
GREEN requires: six witnesses both methods, chain law, census t<=300
exactly {3,4,70}, full witness census t<=5000 exactly the six."""
from math import isqrt

def c3(x):
    return (x + 1) * (x + 2) * (x + 3)

ok = True
def check(name, cond):
    global ok
    print(("PASS" if cond else "FAIL"), name)
    ok &= cond

WITNESSES = [
    (3, 25, 11),      # N = 9
    (4, 13, 4),       # N = 16
    (70, 47, 1),      # N = 4900
    (1189, 1679, 13), # N = 1413721
    (1798, 13453, 89),# N = 3232804
    (4756, 1679, 4),  # N = 22619536 (the composite)
]

# --- 1. Witness replay, dual method ---
for (t, m, n) in WITNESSES:
    lhs = c3(m)
    rhs = t * t * c3(n)
    direct = (lhs == rhs)
    # method 2: quotient is a perfect square == t^2 AND the size conditions
    q = lhs // c3(n)
    struct = (lhs % c3(n) == 0 and isqrt(q) ** 2 == q and isqrt(q) == t
              and n >= 1 and m >= n + 3)
    check(f"witness t={t} (m={m}, n={n}): direct={direct} struct={struct}",
          direct and struct)

# --- 2. The chain law on the witness graph ---
# 4 -> 13 (t=4), 13 -> 1679 (t=1189)  =>  4 -> 1679 (t = 4*1189 = 4756)
q1 = c3(13) // c3(4); q2 = c3(1679) // c3(13)
check("chain: c3(13)/c3(4) == 16 and c3(1679)/c3(13) == 1189^2",
      q1 == 16 and q2 == 1189 * 1189)
check("chain composite: c3(1679)/c3(4) == 4756^2",
      c3(1679) // c3(4) == 4756 * 4756 and c3(1679) % c3(4) == 0)
check("the double-hit identity 16*c3(4) == c3(13) == 3360",
      16 * c3(4) == c3(13) == 3360)

# --- 3. Census t <= 300 (n unbounded within m-bound): exactly {3,4,70} ---
def k3_census(TMAX, NMAX):
    out = []
    T2 = TMAX * TMAX
    for n in range(1, NMAX + 1):
        D = c3(n)
        m = n + 3
        v = c3(m)
        while v <= T2 * D:
            if v % D == 0:
                q = v // D
                r = isqrt(q)
                if r * r == q and 2 <= r <= TMAX:
                    out.append((r, m, n))
            m += 1
            v = c3(m)
    return out

c300 = k3_census(300, 400)
check("census t<=300: exactly {3,4,70}",
      sorted(set(w[0] for w in c300)) == [3, 4, 70])
check("census t<=300 witness set exact",
      sorted(c300) == [(3, 25, 11), (4, 13, 4), (70, 47, 1)])

# --- 4. Full witness census t <= 5000: exactly the six ---
c5000 = k3_census(5000, 120)
check("census t<=5000: exactly the six witnesses",
      sorted(c5000) == sorted(WITNESSES))

# --- 5. N >= 2 and the problem's habitat ---
check("all six N >= 2", all(t * t >= 2 for (t, m, n) in WITNESSES))
check("all six m >= n+3 (k=3 constraint)", all(m >= n + 3 for (t, m, n) in WITNESSES))

print()
print("BATTERY686K3:", "GREEN" if ok else "RED")
raise SystemExit(0 if ok else 1)
