#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""AUDIT_W63 — the final independent verification of the W63 #961 frontier
extension, working ONLY from the committed receipts (census_k17.json,
census_k19.json) + a fresh brute smooth-number enumeration (independent code
path, no CF, no Pell machinery):

1. every census pair (x, x+1) re-verified directly: both sides k-smooth by
   prime stripping; X = 2x+1, Y = 2b with X^2 - a Y^2 = 1 EXACT; a = sf(x(x+1))
   (odd-valuation product); x(x+1) = a b^2.
2. fresh brute enumeration of ALL 19-smooth numbers <= 10^8 (covers the FULL
   range of both censuses: largest pair 11859211 < 10^8): consecutive pairs
   must EQUAL the 19-tier census list; the 17-smooth-filtered sublist must
   EQUAL the 17-tier census list.
3. f(k) re-derived for every k = 2..22 from the brute run structure and
   asserted against the certified table.
"""
import json
from math import isqrt

S19 = [2, 3, 5, 7, 11, 13, 17, 19]

def strip(n, ps):
    for p in ps:
        while n % p == 0:
            n //= p
    return n

def smooth(n, ps):
    return n >= 1 and strip(n, ps) == 1

def vp(n, p):
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v

c17 = json.load(open("census_k17.json"))
c19 = json.load(open("census_k19.json"))
x17 = sorted(set(r[0] for r in c17))
x19 = sorted(set(r[0] for r in c19))
assert len(x17) == 108 and len(x19) == 167 and x17[-1] == 336140 and x19[-1] == 11859210

# 1. direct pair re-verification from the receipts
for (xs, rows, ps) in ((x17, c17, S19[:7]), (x19, c19, S19)):
    for (x, a, n, Xs, Ys) in rows:
        X, Y = int(Xs), int(Ys)
        assert X * X - a * Y * Y == 1, "Pell identity FAILS x=%d" % x
        assert X == 2 * x + 1 and Y % 2 == 0, "shape FAILS x=%d" % x
        b = Y // 2
        assert x * (x + 1) == a * b * b, "x(x+1)=ab^2 FAILS x=%d" % x
        assert smooth(x, ps) and smooth(x + 1, ps) and smooth(b, ps), "smooth FAILS x=%d" % x
        sf = 1
        for p in ps:
            if vp(x * (x + 1), p) % 2:
                sf *= p
        assert sf == a, "dictionary FAILS x=%d" % x
print("1. all %d + %d census pairs re-verified from receipts (Pell identity,"
      % (len(c17), len(c19)))
print("   x(x+1)=ab^2, smoothness, dictionary a=sf(x(x+1))) — GREEN")

# 2. fresh brute enumeration of ALL 19-smooth <= 10^8 (full census range)
B = 10 ** 8
nums = []
p2 = 1
while p2 <= B:
    p23 = p2
    while p23 <= B:
        p235 = p23
        while p235 <= B:
            p2357 = p235
            while p2357 <= B:
                p235711 = p2357
                while p235711 <= B:
                    p23571113 = p235711
                    while p23571113 <= B:
                        p2357111317 = p23571113
                        while p2357111317 <= B:
                            n = p2357111317
                            while n <= B:
                                nums.append(n)
                                n *= 19
                            p2357111317 *= 17
                        p23571113 *= 13
                    p235711 *= 11
                p2357 *= 7
            p235 *= 5
        p23 *= 3
    p2 *= 2
nums.sort()
print("2. fresh brute: %d 19-smooth numbers <= 10^8" % len(nums))
bp19 = [(u, v) for u, v in zip(nums, nums[1:]) if v == u + 1]
assert [u for (u, v) in bp19] == x19, "19-tier pair list MISMATCH"
nset = set(nums)
bp17 = [(u, v) for (u, v) in bp19 if smooth(u, S19[:7]) and smooth(v, S19[:7])]
assert [u for (u, v) in bp17] == x17, "17-tier pair list MISMATCH"
print("   brute pairs == 19-tier census list (167) EXACT; 17-smooth-filtered")
print("   sublist == 17-tier census list (108) EXACT — GREEN (the brute covers")
print("   the full range of both censuses: largest pair 11859211 < 10^8)")

# 3. f(k) re-derived for k = 2..22 from the brute structure (independent of Pell)
def runs_of(pairlist):
    rr = []
    cur = [pairlist[0][0], pairlist[0][1]]
    for (u, v) in pairlist[1:]:
        if u == cur[-1]:
            cur.append(v)
        else:
            rr.append(tuple(cur))
            cur = [u, v]
    rr.append(tuple(cur))
    return rr

FK = {}
for k in range(2, 23):
    ps_k = [p for p in S19 if p <= k]
    # the k-smooth numbers <= 10^8 are exactly the 19-smooth ones whose prime
    # factors all lie <= k (k <= 22 < 23: every k-smooth number is 19-smooth,
    # so the brute set contains them all)
    ks = [m for m in nums if strip(m, ps_k) == 1]
    kp = [(u, v) for u, v in zip(ks, ks[1:]) if v == u + 1]
    kr = runs_of(kp) if kp else []
    # f(k) = 1 + max{L: L consecutive k-smooth all > k}; singletons count
    # (2k is k-smooth and > k for every k >= 2)
    best = 1
    for r in kr:
        s = sum(1 for j in r if j > k)
        if s > best:
            best = s
    FK[k] = best + 1
CERT = {2: 2, 3: 3, 4: 3, 5: 4, 6: 4, 7: 4, 8: 4, 9: 4, 10: 4, 11: 4, 12: 4,
        13: 6, 14: 6, 15: 6, 16: 6, 17: 6, 18: 6, 19: 6, 20: 6, 21: 6, 22: 6}
assert FK == CERT, "f-table MISMATCH: %s" % FK
print("3. f(k) re-derived independently for k = 2..22 from the brute structure:")
print("   %s" % [FK[k] for k in range(2, 23)])
print("   (matches the certified table — GREEN)")
print()
print("AUDIT_W63 ALL GREEN — the W63 frontier f(k)=6 (13<=k<=22) stands on")
print("independent brute verification of the complete 108-pair and 167-pair")
print("censuses (full range) + direct receipt re-verification.")
