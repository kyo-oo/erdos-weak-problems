#!/usr/bin/env python3
"""Exact finite checks; no Lean build and no universal existence assertion.

Command: python research/experiments/gst_selected_block_checks.py
Python enumerates subsets/permutation groups and uses its own sparse quotient
polynomials. Wolfram separately uses binomials and symbolic polynomial reduction.
"""
from collections import defaultdict
from fractions import Fraction as Q
from itertools import combinations, permutations
from math import comb, factorial
import json

CHECKS = 0

def check(v):
    global CHECKS
    CHECKS += 1
    if not v:
        raise AssertionError(f"check {CHECKS}")

def bn(n, k):
    return comb(n, k) if 0 <= k <= n else 0

def coefficients(r, m, s):
    return [bn(r-1, k-1)*bn(m, s-k)-bn(r, k)*bn(m-1, s-k-1)
            for k in range(max(0, s-m), min(r, s)+1)]

def compose(a, b):
    return tuple(a[b[i]] for i in range(len(a)))

def closure(gens, n):
    identity = tuple(range(n))
    found, queue = {identity}, [identity]
    for a in queue:
        for g in gens:
            b = compose(g, a)
            if b not in found:
                found.add(b)
                queue.append(b)
    return frozenset(found)

def subgroups(n):
    perms = list(permutations(range(n)))
    trivial = frozenset([tuple(range(n))])
    found, queue = {trivial}, [trivial]
    for h in queue:
        for g in perms:
            if g not in h:
                new = closure(list(h)+[g], n)
                if new not in found:
                    found.add(new)
                    queue.append(new)
    return sorted(found, key=lambda h: (len(h), sorted(h)))

def packages(group, n, r, s):
    subsets = {frozenset(i) for i in combinations(range(n), s)}
    ks = list(range(max(0, s-(n-r)), min(r, s)+1))
    parent = {k: k for k in ks}
    def root(k):
        while parent[k] != k:
            parent[k] = parent[parent[k]]
            k = parent[k]
        return k
    while subsets:
        seed = min(subsets, key=lambda x: tuple(sorted(x)))
        orbit = {frozenset(g[i] for i in seed) for g in group}
        check(orbit <= subsets)
        subsets -= orbit
        shell = sorted({sum(i < r for i in a) for a in orbit})
        for k in shell[1:]:
            parent[root(k)] = root(shell[0])
    output = defaultdict(list)
    for k in ks:
        output[root(k)].append(k)
    return sorted(output.values())

# Sparse polynomials in x,y,z,e,t, reduced by yz=1-x^2 at every product.
NV = 5
ZERO = (0,)*NV
def poly(q):
    return {ZERO: Q(q)} if q else {}
def var(i):
    powers = [0]*NV
    powers[i] = 1
    return {tuple(powers): Q(1)}
def add(*args):
    out = defaultdict(Q)
    for a in args:
        for powers, c in a.items():
            out[powers] += c
    return {p:c for p,c in out.items() if c}
def scale(q, a):
    return {p:Q(q)*c for p,c in a.items() if Q(q)*c}
def substitute(a, replacements):
    out = defaultdict(Q)
    for powers, c in a.items():
        remaining = list(powers)
        for i, value in replacements.items():
            c *= Q(value)**remaining[i]
            remaining[i] = 0
        out[tuple(remaining)] += c
    return {p:c for p,c in out.items() if c}
def mul(a, b):
    out = defaultdict(Q)
    for u, c in a.items():
        for v, d in b.items():
            power = [u[i]+v[i] for i in range(NV)]
            overlap = min(power[1], power[2])
            power[1] -= overlap
            power[2] -= overlap
            for j in range(overlap+1):
                reduced = power.copy()
                reduced[0] += 2*j
                out[tuple(reduced)] += c*d*comb(overlap, j)*(-1)**j
    return {p:c for p,c in out.items() if c}
def mm(a, b):
    return [[add(*(mul(a[i][k], b[k][j]) for k in range(2)))
             for j in range(2)] for i in range(2)]

def run():
    coefficient_rows = []
    # Compare the closed coefficients with direct occurrences of each root.
    for r in range(1, 7):
        for m in range(1, 7):
            n = r+m
            for s in range(n+1):
                ks = range(max(0, s-m), min(r, s)+1)
                row = coefficients(r, m, s)
                check(sum(row) == 0)
                for k, c in zip(ks, row):
                    counts = [0]*n
                    count = 0
                    for chosen in combinations(range(n), s):
                        if sum(i < r for i in chosen) == k:
                            count += 1
                            for i in chosen:
                                counts[i] += 1
                    check(len(set(counts[:r])) == 1)
                    check(len(set(counts[r:])) == 1)
                    check(counts[0]-counts[r] == c)
                    check(counts[0]*r+counts[r]*m == s*count)
                    # Independent power-sum values, no assumed Chow relation.
                    for p in range(1, 5):
                        actual = sum(sum((i+1)**p for i in chosen)
                                     for chosen in combinations(range(n), s)
                                     if sum(i < r for i in chosen) == k)
                        expected = (counts[0]*sum((i+1)**p for i in range(r))
                                    +counts[r]*sum((i+1)**p for i in range(r,n)))
                        check(actual == expected)
                if r <= 4 and m <= 4:
                    coefficient_rows.append([r, m, s, row])
            check(coefficients(r, m, r)[-1] == 1)

    group_rows = []
    for n, expected_groups in [(1,1),(2,2),(3,6),(4,30)]:
        groups = subgroups(n)
        check(len(groups) == expected_groups)
        transitive_count = case_count = neutral_count = nonzero_cases = 0
        for group in groups:
            transitive = len({g[0] for g in group}) == n
            transitive_count += transitive
            for r in range(1,n):
                for s in range(n+1):
                    case_count += 1
                    coeffs = dict(zip(range(max(0,s-(n-r)),min(r,s)+1),
                                      coefficients(r,n-r,s)))
                    partition = packages(group,n,r,s)
                    sums = [sum(coeffs[k] for k in part) for part in partition]
                    check(sum(sums) == 0)
                    if transitive:
                        check(all(c == 0 for c in sums))
                        neutral_count += 1
                    nonzero_cases += any(c != 0 for c in sums)
        group_rows.append([n,len(groups),transitive_count,case_count,
                           neutral_count,nonzero_cases])

    x,y,z,e,t = [var(i) for i in range(NV)]
    one = poly(1)
    projector = [[scale(Q(1,2),add(one,x)),scale(Q(1,2),y)],
                 [scale(Q(1,2),z),scale(Q(1,2),add(one,scale(-1,x)))]]
    check(mm(projector,projector) == projector)
    a = [[add(projector[0][0],e),projector[0][1]],
         [projector[1][0],add(projector[1][1],scale(-1,e))]]
    determinant = add(mul(add(t,scale(-1,a[0][0])),
                          add(t,scale(-1,a[1][1]))),
                      scale(-1,mul(a[0][1],a[1][0])))
    check(determinant == add(mul(t,t),scale(-1,t),scale(-1,mul(e,x)),
                             scale(-1,mul(e,e))))
    branch_rows = []
    for eps in [Q(1,10),Q(1,4),Q(1,3)]:
        branch = -(1+4*eps*eps)/(4*eps)
        lower = (1-2*eps)**2
        check(branch < -1)
        check(1-branch*branch != 0)
        check(lower > 0)
        check(1+4*eps*branch+4*eps*eps == 0)
        branch_rows.append([str(eps),str(branch),str(lower)])
    # Hostile parameter boundaries are actual matrix/polynomial controls.
    check(substitute(determinant,{3:0}) == mul(t,add(t,poly(-1))))
    scalar_boundary = [[substitute(entry,{0:-1,1:0,2:0,3:Q(1,2)})
                        for entry in row] for row in a]
    check(scalar_boundary == [[poly(Q(1,2)),poly(0)],
                              [poly(0),poly(Q(1,2))]])

    # Exterior sign: eta2 wedge eta1 is minus eta1 wedge eta2.
    u = [[poly(0),one],[poly(0),poly(0)]]
    v = [[poly(0),poly(0)],[one,poly(0)]]
    uv,vu = mm(u,v),mm(v,u)
    commutator = [[add(uv[i][j],scale(-1,vu[i][j])) for j in range(2)]
                  for i in range(2)]
    check(commutator == [[one,poly(0)],[poly(0),poly(-1)]])
    check(add(commutator[0][0],commutator[1][1]) == {})
    check(commutator != [[poly(0)]*2 for _ in range(2)])

    return {"all_passed":True,"assertion_count":CHECKS,
            "coefficient_rows":coefficient_rows,"subgroup_rows":group_rows,
            "branch_rows":branch_rows,"commutator":[[1,0],[0,-1]],
            "bounds":{"r_m":[1,6],"selector":"all 0..r+m",
                      "power_sum_degrees":[1,4],"all_subgroups_of_S_n":[1,4]},
            "nonclaims":["No universal Hodge source existence",
                         "No Lean compilation","Finite checks are not geometric proofs"]}

if __name__ == "__main__":
    print(json.dumps(run(),sort_keys=True,separators=(",",":")))
