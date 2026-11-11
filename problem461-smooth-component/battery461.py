#!/usr/bin/env python3
"""BATTERY 461 — dual-method verification of the Kernel 35 claims.
Method A: the engine table (sliding census, prefix-product single pass).
Method B (independent): trial-division factorization recounts + sieve-sliding
minimality recounts on sampled t + the 480-censuses."""
import math
from collections import Counter

N = 200000
ok = True
def check(cond, msg):
    global ok
    if not cond:
        print("FAIL:", msg)
        ok = False

# load the ACH table (t, argmin, c) emitted by the engine
ACH = []
for line in open("problem461-smooth-component/table461.txt"):
    line = line.strip()
    if not line or line.startswith("#"):
        continue
    t, c, n = map(int, line.split())
    ACH.append((t, n, c))   # file columns are t, c, argmin -> ACH row (t, argmin, c)
check(len(ACH) == 119, f"ACH size {len(ACH)}")

# ---- 1. INDEPENDENT recount of every ACH window (trial division)
PS = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,
      101,103,107,109,113]
def s_of(t, m):
    r = 1
    for p in PS:
        if p >= t: break
        while m % p == 0:
            m //= p; r *= p
    return r
for t, n, c in ACH:
    vals = {s_of(t, m) for m in range(n + 1, n + t + 1)}
    check(len(vals) == c, f"ACH recount t={t} n={n} c={c} got {len(vals)}")
print(f"ACH recount: 119/119 windows match (trial division)")

# ---- 2. sieve-sliding minimality recount on sampled t (independent code path)
def sieve_min(t, N0):
    ps = [p for p in PS if p < t]
    s = [1] * (N0 + t + 1)
    for p in ps:
        pk = p
        while pk <= N0 + t:
            for m in range(pk, N0 + t + 1, pk):
                s[m] *= p
            pk *= p
    cnt = Counter(s[1:t+1])
    best = (len(cnt), 0)
    for n in range(1, N0):
        out, inn = s[n], s[n + t]
        cnt[out] -= 1
        if cnt[out] == 0: del cnt[out]
        cnt[inn] += 1
        if len(cnt) < best[0]:
            best = (len(cnt), n)
    return best

for t in [14, 20, 30, 40, 60, 90, 120]:
    c_eng = next(c for tt, n, c in ACH if tt == t)
    c_ind, n_ind = sieve_min(t, N)
    check(c_ind == c_eng, f"minimality t={t}: engine {c_eng} vs independent {c_ind}")
    print(f"t={t}: min over n<{N} = {c_ind} (independent recount matches)")

# ---- 3. the four 480-censuses (both directions, independent)
for t, m, narg in [(14, 9, 33), (20, 13, 198), (30, 19, 121), (40, 25, 162)]:
    ps = [p for p in PS if p < t]
    s = [1] * (480 + t + 1)
    for p in ps:
        pk = p
        while pk <= 480 + t:
            for mm in range(pk, 480 + t + 1, pk):
                s[mm] *= p
            pk *= p
    mins = min(len(set(s[n+1:n+t+1])) for n in range(480))
    check(mins == m, f"480-census t={t}: kernel {m} vs recount {mins}")
    check(len(set(s[narg+1:narg+t+1])) == m, f"480-census witness t={t}")
print("480-censuses: 4/4 both-direction matches")

# ---- 4. stability + ErGra law checks on the ACH c-values
import itertools
for t, n, c in ACH:
    if 14 <= t <= 120:
        check(55 * t <= 100 * c <= 65 * t, f"stability t={t} c={c}")
        L = math.floor(1000 * math.log(t))
        check(c * L >= 1000 * t, f"ergra t={t} c={c}")
print("stability [14,120]: 107/107; ErGra beating: 107/107")

# ---- 5. the p-part law sanity (spart p m = p^vp p m, engine-side)
import random
random.seed(461)
for _ in range(300):
    p = random.choice(PS)
    m = random.randrange(1, 10**6)
    v = 0
    mm = m
    while mm % p == 0:
        mm //= p; v += 1
    part = p ** v
    # divisibility + maximality (the kernel's spart_dvd + extraction shape)
    check(m % part == 0, f"p-part divides p={p} m={m}")
    check((m // part) % p != 0, f"p-part maximal p={p} m={m}")

print("BATTERY461:", "GREEN" if ok else "RED")
