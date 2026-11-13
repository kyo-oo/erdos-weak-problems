#!/usr/bin/env python3
# engine389c.py — the deep scan for n = 12..18 (numpy SPF sieve + array('i')).
# Background job; banks finds progressively into scan389_deep.txt.

import sys
import time
from array import array
from collections import defaultdict

import numpy as np

KMAX = int(10 ** 7)
ROWS = [12, 13, 14, 15, 16, 17, 18]

# numpy smallest-prime-factor sieve over [0, N]
N = 2 * KMAX + 40
t0 = time.time()
spf_np = np.arange(N, dtype=np.int64)
for i in range(2, int(N ** 0.5) + 1):
    if spf_np[i] == i:  # prime
        spf_np[i * i::i] = np.minimum(spf_np[i * i::i], i)
# keep only cells whose spf is themselves (i.e. untouched) — standard trick is
# different; we did: arange then min-fold with each prime. Result: spf[m] =
# smallest prime dividing m for m >= 2 (1 for m = 1, 0 for 0).
spf = array("l", spf_np.tobytes())
del spf_np
print("sieve N=%d built in %.1fs" % (N, time.time() - t0), flush=True)


def factor(m):
    fs = {}
    while m > 1:
        p = spf[m]
        e = 0
        while m % p == 0:
            m //= p
            e += 1
        fs[p] = fs.get(p, 0) + e
    return fs


def scan(n, Kmax):
    D = defaultdict(int)
    neg = [0]

    def touch(p, d):
        old = D[p]
        new = old + d
        D[p] = new
        if old < 0 and new >= 0:
            neg[0] -= 1
        elif old >= 0 and new < 0:
            neg[0] += 1

    for p, e in factor(n + 1).items():
        touch(p, +e)
    for p, e in factor(n).items():
        touch(p, -e)
    if neg[0] == 0:
        return 1
    for k in range(1, Kmax):
        for p, e in factor(n + k).items():
            touch(p, -2 * e)
        for p, e in factor(n + 2 * k).items():
            touch(p, +e)
        for p, e in factor(n + 2 * k + 1).items():
            touch(p, +e)
        if neg[0] == 0:
            return k + 1
    return None


with open("scan389_deep.txt", "w") as f:
    for n in ROWS:
        t0 = time.time()
        k = scan(n, KMAX)
        msg = ("n=%d: k=%s (Kmax=%d, %.1fs)" % (n, k, KMAX, time.time() - t0))
        print(msg, flush=True)
        f.write(msg + "\n")
        f.flush()
    print("DEEP SCAN DONE", flush=True)
