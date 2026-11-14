#!/usr/bin/env python3
"""W66-P306-S STRATEGIST — probe census for #306 semiprime Egyptian representations.

Census over ALL reduced rationals a/b, 0 < a/b < 1, b squarefree, b <= B.
Representation = finite sum of DISTINCT reciprocals of semiprimes n = p*q
with p < q primes (the campaign's distinct-prime class).

Engines (escalation):
  A.  greedy DFS over a bounded semiprime table (branch + suffix-sum prune)
  D.  pair-window exact solver: over a prime window P (containing primes(b)),
      M = prod(P), items M/(p*q) for p<q in P, exact subset-sum to a*M/b
      (the CRT-window frame — escalating windows 19/23/29/31/37/41/47/53/61).
  B.  CRT peel: kill prime p of the denominator via a term 1/(p*q) with
      q = c * a^{-1} mod p (q prime), residual k/(c*q); repeat, then greedy.

Output: PROBE306_W66_B<B>.json (checkpointed per b) + stdout log.
"""
import sys, time, json, bisect
sys.setrecursionlimit(20000)
from fractions import Fraction
from math import gcd
import sympy

T0 = time.time()
PRIMES = list(sympy.primerange(2, 2_100_000))
SEMI_CAP = 4_000_000
SEMIS = []
BIG_CUT = 23
NPR = len(PRIMES)
for i, p in enumerate(PRIMES):
    if i + 1 < NPR and p * PRIMES[i + 1] > SEMI_CAP:
        break
    for j in range(i + 1, NPR):
        q = PRIMES[j]
        n = p * q
        if n > SEMI_CAP:
            break
        SEMIS.append((n, p))
SEMIS.sort()
SEMIS = [n for n, _ in SEMIS]
SUFFIX = [0.0] * (len(SEMIS) + 1)
for k in range(len(SEMIS) - 1, -1, -1):
    SUFFIX[k] = SUFFIX[k + 1] + 1.0 / SEMIS[k]
print(f"[tables] semiprimes<={SEMI_CAP}: {len(SEMIS)} "
      f"({time.time()-T0:.1f}s)", flush=True)

# prime windows for engine D (cumulative prime lists)
WINDOWS = {}
acc = []
for p in PRIMES:
    if p > 61:
        break
    acc.append(p)
    WINDOWS[p] = list(acc)


def is_squarefree(b):
    return all(e == 1 for e in sympy.factorint(b).values())


def check_rep(dens, a, b):
    if len(set(dens)) != len(dens):
        return False
    s = Fraction(0)
    for n in dens:
        f = sympy.factorint(n)
        if len(f) != 2 or max(f.values()) != 1:
            return False
        s += Fraction(1, n)
    return s == Fraction(a, b)


# ---------- engine A: greedy DFS ----------
def greedy(r, cap_nodes=300_000, branch=10, tmo=4.0, first_moves=None,
           max_terms=100):
    nodes = [0]
    t0 = time.time()
    best = [None]
    min_term = Fraction(1, SEMIS[-1])

    def rec(rem, idx, chosen):
        if nodes[0] > cap_nodes or time.time() - t0 > tmo:
            return False
        nodes[0] += 1
        if rem == 0:
            best[0] = list(chosen)
            return True
        if len(chosen) >= max_terms:
            return False
        if rem < min_term:
            return False
        n_min = -(-rem.denominator // rem.numerator)
        if chosen:
            n_min = max(n_min, chosen[-1] + 1)
        j = bisect.bisect_left(SEMIS, n_min, lo=idx)
        if j >= len(SEMIS):
            return False
        if float(rem) > SUFFIX[j] + 1e-12:
            return False
        tried = 0
        for k in range(j, len(SEMIS)):
            n = SEMIS[k]
            if rem < Fraction(1, n):
                continue
            if float(rem) - 1.0 / n > SUFFIX[k + 1] + 1e-12:
                break
            chosen.append(n)
            ok = rec(rem - Fraction(1, n), k + 1, chosen)
            chosen.pop()
            if ok:
                return True
            tried += 1
            if tried >= branch or nodes[0] > cap_nodes:
                break
        return False

    if first_moves:
        for fm in first_moves:
            if r < Fraction(1, fm):
                continue
            chosen = [fm]
            jj = bisect.bisect_left(SEMIS, fm + 1)
            if rec(r - Fraction(1, fm), jj, chosen):
                return best[0]
        return None
    if rec(r, 0, []):
        return best[0]
    return None


# ---------- engine D: pair-window exact subset-sum ----------
def pair_window_solve(r, wmax, node_cap=1_500_000, tmo=8.0):
    a, b = r.numerator, r.denominator
    need = set(sympy.factorint(b).keys())
    P = sorted(need | set(WINDOWS[wmax]))
    M = 1
    for p in P:
        M *= p
    if M % b != 0:
        return None
    T = a * (M // b)
    pairs = []
    for i in range(len(P)):
        for j in range(i + 1, len(P)):
            d = P[i] * P[j]
            pairs.append((d, M // d))
    pairs.sort(key=lambda t: -t[1])
    vals = [v for _, v in pairs]
    dens = [d for d, _ in pairs]
    n = len(pairs)
    suf = [0] * (n + 1)
    for k in range(n - 1, -1, -1):
        suf[k] = suf[k + 1] + vals[k]
    if T > suf[0] or T < 0:
        return None
    sol = [None]
    nodes = [0]
    t0 = time.time()

    def dfs(k, rem, acc):
        if sol[0] is not None or nodes[0] > node_cap or \
           time.time() - t0 > tmo:
            return
        nodes[0] += 1
        if rem == 0:
            sol[0] = list(acc)
            return
        if k >= n or rem > suf[k] or rem < 0:
            return
        v = vals[k]
        if v <= rem:
            acc.append(dens[k])
            dfs(k + 1, rem - v, acc)
            if sol[0] is not None:
                return
            acc.pop()
        dfs(k + 1, rem, acc)

    dfs(0, T, [])
    return sol[0]


# ---------- engine B: CRT peel ----------
def peel_terms(r, max_rounds=8, used=None):
    terms = []
    used = set(used or set())
    cur = r
    for _ in range(max_rounds):
        if cur == 0:
            break
        a, b = cur.numerator, cur.denominator
        if b == 1:
            break
        fac = sorted(sympy.factorint(b).keys())
        p = fac[-1]
        c = b // p
        try:
            t = (c * pow(a, -1, p)) % p
        except ValueError:
            break
        cands = [q for q in PRIMES[:400] if q > p and q % p == t
                 and q not in fac and (p * q) not in used][:6]
        if not cands:
            break
        placed = False
        for q in cands:
            n = p * q
            r1 = cur - Fraction(1, n)
            if r1 <= 0:
                continue
            if all(e == 1 for e in sympy.factorint(r1.denominator).values()):
                terms.append(n)
                used.add(n)
                cur = r1
                placed = True
                break
        if not placed:
            break
    return terms, cur


def solve_full(r, budget_s=14.0):
    t_deadline = time.time() + budget_s
    # A: greedy
    res = greedy(r, tmo=3.0)
    if res and check_rep(res, r.numerator, r.denominator):
        return res, "A-greedy"
    # D: pair-window escalation
    for wmax in (13, 17, 19, 23, 29, 31, 37, 41, 47, 53, 61):
        if time.time() > t_deadline:
            break
        res = pair_window_solve(r, wmax,
                                tmo=max(0.5, t_deadline - time.time()))
        if res:
            dens = sorted(set(res))
            if check_rep(dens, r.numerator, r.denominator):
                return dens, f"D-window{wmax}"
    # B: peel then greedy close
    pt, rem = peel_terms(r)
    if pt and rem > 0:
        res = greedy(rem, cap_nodes=150_000, branch=8,
                    tmo=max(1.0, t_deadline - time.time()))
        if res and not (set(pt) & set(res)):
            all_d = pt + res
            if check_rep(all_d, r.numerator, r.denominator):
                return all_d, "B-peel"
    return None, "FAIL"


def squarefree_bs(B):
    return [b for b in range(2, B + 1) if is_squarefree(b)]


def main():
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    out_path = sys.argv[2] if len(sys.argv) > 2 else f"PROBE306_W66_B{B}.json"
    bs = squarefree_bs(B)
    state = {"B": B, "done": [], "results": {}, "fails": []}
    try:
        with open(out_path) as f:
            prev = json.load(f)
        if prev.get("B") == B:
            state = prev
            print(f"[resume] {len(state['done'])} b-classes already done",
                  flush=True)
    except Exception:
        pass
    t_start = time.time()
    total = hit = 0
    for b in bs:
        if b in state["done"]:
            rb = state["results"].get(str(b), {})
            total += len(rb)
            hit += sum(1 for v in rb.values() if v is not None)
            continue
        res_b = {}
        tg = [Fraction(a, b) for a in range(1, b) if gcd(a, b) == 1]
        for r in tg:
            dens, engine = solve_full(r)
            key = f"{r.numerator}/{r.denominator}"
            if dens is not None:
                res_b[key] = {"dens": dens, "engine": engine,
                              "nterms": len(dens), "maxden": max(dens)}
                hit += 1
            else:
                res_b[key] = None
                state["fails"].append(key)
            total += 1
        state["results"][str(b)] = res_b
        state["done"].append(b)
        with open(out_path, "w") as f:
            json.dump(state, f)
        print(f"[census B<={B}] b={b}: "
              f"{sum(1 for v in res_b.values() if v is not None)}/{len(tg)}"
              f" | running {hit}/{total} ({time.time()-t_start:.0f}s)",
              flush=True)
    print(f"\n=== PROBE CENSUS B<={B}: {hit}/{total} rationals represented ===",
          flush=True)
    print("FAILS:", state["fails"], flush=True)
    with open(out_path, "w") as f:
        json.dump(state, f)


if __name__ == "__main__":
    main()
