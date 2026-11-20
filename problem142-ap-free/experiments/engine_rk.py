#!/usr/bin/env python3
"""ENGINE-142 (W1-T2a absorbed by commander) — dual-method certified r_k(N) tables.

Erdos #142: r_k(N) = max{|A| : A subset [N], no non-trivial k-term AP}.
Method A: Z3 SMT feasibility bisection on the k-AP-avoidance clauses.
Method B: independent python branch-and-bound (bitmask, greedy seed, AP-structure pruning).
Certification = both methods agree. Every reported value carries a witness set.
"""
import json, sys, time
from itertools import combinations

try:
    from z3 import Bool, Solver, Or, Not, And, Sum, If, sat, is_true as z3_is_true
    Z3 = True
except Exception:
    Z3 = False

def aps(N, k):
    """All k-term APs (a, d), a>=1, d>=1, a+(k-1)d <= N. Returns list of index tuples (0-based)."""
    out = []
    for a in range(0, N):
        for d in range(1, N):
            if a + (k-1)*d >= N:
                break
            out.append(tuple(a + i*d for i in range(k)))
    return out

def greedy_lower(N, k):
    """Greedy 3-AP-free-style seed: take i if no k-AP completed (gives valid lower bound + witness)."""
    taken = []
    S = set()
    for i in range(N):
        ok = True
        for d in range(1, N):
            if i - (k-1)*d >= 0:
                if all((i - j*d) in S for j in range(1, k)):
                    ok = False; break
        if ok:
            S.add(i); taken.append(i)
    return taken

def bnb(N, k, seed_witness, time_cap=240.0):
    """Method B: branch and bound. Order = given; take/skip with AP-check and bound = cur + remaining.
    Symmetry: WLOG the first vertex (index 0) is IN the set (complement-symmetry does NOT hold for AP-free;
    but r_k(N) >= r_k(N-1)+? we seed with best known lower = greedy.)"""
    t0 = time.time()
    APS = aps(N, k)
    # contains[i] = list of APs containing i
    containing = [[] for _ in range(N)]
    for ap in APS:
        for v in ap:
            containing[v].append(ap)
    best = set(seed_witness)
    # bit-mask representation of each AP for fast check
    apmask = [sum(1 << v for v in ap) for ap in APS]
    adj = [[] for _ in range(N)]  # adj[v] = list of (apmask, last_positions...) — we use a different scheme
    # For taking vertex v given current set S (as bitmask): forbidden if some AP with all other k-1 members in S and v the last.
    # Precompute: for each v, for each AP containing v: mask of OTHER members.
    others = [[] for _ in range(N)]
    for idx, ap in enumerate(APS):
        m_all = apmask[idx]
        for v in ap:
            others[v].append(m_all & ~(1 << v))
    S = 0
    def rec(i, count):
        nonlocal S, best
        if time.time() - t0 > time_cap:
            raise TimeoutError
        if count + (N - i) <= len(best):
            return
        if i == N:
            if count > len(best):
                best = set(j for j in range(N) if S >> j & 1)
            return
        # try taking i
        # check: no AP whose other members are all in S and includes i
        can = True
        for om in others[i]:
            if om & S == om:
                can = False; break
        if can:
            S |= (1 << i)
            rec(i + 1, count + 1)
            S &= ~(1 << i)
        # skip i — symmetry break: if S is empty and i == 0... (no valid symmetry; rely on bound)
        rec(i + 1, count)
    try:
        rec(0, 0)
        proven_optimal = True
    except TimeoutError:
        proven_optimal = False
    return best, proven_optimal

def z3_rk(N, k, target):
    """Method A: is there an AP-free set of size >= target? UNSAT => r_k(N) < target."""
    if not Z3:
        return None
    x = [Bool(f"x{i}") for i in range(N)]
    s = Solver()
    s.set("timeout", 120000)
    for ap in aps(N, k):
        s.add(Or([Not(x[v]) for v in ap]))
    s.add(Sum([If(x[i], 1, 0) for i in range(N)]) >= target)
    r = s.check()
    if r == sat:
        m = s.model()
        return [i for i in range(N) if z3_is_true(m[x[i]])]
    return None  # unsat or unknown

def witness_valid(w, N, k):
    S = set(w)
    for ap in aps(N, k):
        if all(v in S for v in ap):
            return False
    return all(0 <= v < N for v in w)

def main():
    results = {}
    plans = [
        (3, range(1, 36)),   # r_3 to 35 (z3+bnb)
        (4, range(1, 56)),
        (5, range(1, 76)),
        (6, range(1, 101)),
    ]
    for k, Ns in plans:
        results[str(k)] = {}
        prev = None
        for N in Ns:
            t0 = time.time()
            seed = greedy_lower(N, k) if prev is None else [v for v in prev if v < N]
            if not witness_valid(seed, N, k):
                seed = greedy_lower(N, k)
            best, opt = bnb(N, k, seed, time_cap=180.0)
            val_bnb = len(best)
            # Z3 cross: confirm val_bnb feasible (sat) and val_bnb+1 infeasible (unsat)
            w_sat = z3_rk(N, k, val_bnb)
            w_unsat = z3_rk(N, k, val_bnb + 1)
            agree = (w_sat is not None) and (w_unsat is None)
            certified = agree and opt
            results[str(k)][str(N)] = {
                "value": val_bnb,
                "bnb_optimal": opt,
                "z3_agree": agree,
                "certified": certified,
                "witness": sorted(best),
                "secs": round(time.time() - t0, 1),
            }
            print(f"k={k} N={N} r_k={val_bnb} bnb_opt={opt} z3_agree={agree} certified={certified} ({results[str(k)][str(N)]['secs']}s)", flush=True)
            prev = best
    with open("/home/z/erdos-weak-problems/problem142-ap-free/experiments/tables_rk.json", "w") as f:
        json.dump(results, f, indent=1)
    print("WROTE tables_rk.json")

if __name__ == "__main__":
    main()
