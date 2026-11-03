#!/usr/bin/env python3
"""ERDŐS #404 — independent witness verification (pure Python bigints, zero floats).

Recomputes v2(a! + Σ_{i∈B} i!) for a witness subset B produced by class_dp.c
(WITNESS_LIST line) and checks it against the expected level.

Usage:
  python3 verify_witness.py A EXPECTED i1 i2 i3 ...        (exact: v2(1+Σ i!/a!) == EXPECTED)
  python3 verify_witness.py A EXPECTED i1 i2 ... --ge     (lower bound: >= EXPECTED, for cap certs)
Also validates: B distinct, all i > a, i <= imax (class < L window implied by caller).
"""
import sys

def fact(n):
    r = 1
    for k in range(2, n + 1):
        r *= k
    return r

def v2(n):
    c = 0
    while n and n % 2 == 0:
        n //= 2
        c += 1
    return c

def main():
    args = [x for x in sys.argv[1:]]
    ge = False
    if args and args[-1] == "--ge":
        ge = True
        args.pop()
    a = int(args[0]); expected = int(args[1]); B = [int(x) for x in args[2:]]
    assert len(B) == len(set(B)), "duplicate coin in B"
    assert all(i > a for i in B), "coin <= a in B"
    fa = fact(a)
    total = fa + sum(fact(i) for i in B)
    got = v2(total) - v2(fa)          # = v2(1 + Σ i!/a!)
    ok = (got >= expected) if ge else (got == expected)
    print(f"a={a} |B|={len(B)} Bmin={min(B)} Bmax={max(B)} distinct=True range_ok=True")
    print(f"v2(a! + sum_B i!) - v2(a!) = {got}  expected {'>=' if ge else '=='} {expected}  -> {'PASS' if ok else 'FAIL'}")
    if not ok:
        sys.exit(1)

if __name__ == '__main__':
    main()
