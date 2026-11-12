import sys, time
from fractions import Fraction

def gen_S(bound):
    s = set()
    a = 1
    while a <= bound:
        b = a
        while b <= bound:
            c = b
            while c <= bound:
                s.add(c)
                c *= 7
            b *= 4
        a *= 3
    return sorted(s)

def subset_search(elems, target, deadline):
    # elems ascending; find subset with sum of reciprocals == target (Fraction)
    n = len(elems)
    rec = [Fraction(0)]*(n+1)
    for i in range(n-1,-1,-1):
        rec[i] = rec[i+1] + Fraction(1, elems[i])
    nodes = [0]
    def dfs(i, cur, chosen):
        nodes[0]+=1
        if nodes[0] % 200000 == 0 and time.time()>deadline: raise TimeoutError
        if cur == target: return list(chosen)
        if cur > target: return None
        if i>=n: return None
        if cur + rec[i] < target: return None
        # include
        nc = cur + Fraction(1, elems[i])
        if nc <= target:
            chosen.append(elems[i])
            r = dfs(i+1, nc, chosen)
            if r is not None: return r
            chosen.pop()
        r = dfs(i+1, cur, chosen)
        return r if r is not None else None
    try:
        return dfs(0, Fraction(0), []), nodes[0]
    except TimeoutError:
        return "TIMEOUT", nodes[0]

t0=time.time()
for bound in [100, 300, 1000, 3000, 10000]:
    S=[x for x in gen_S(bound) if x>1]
    r, nodes = subset_search(S, Fraction(1), t0+25)
    print("bound", bound, "elems", len(S), "nodes", nodes, "result", r, flush=True)
    if isinstance(r, list):
        # verify
        assert sum(Fraction(1,x) for x in r)==1
        print("VERIFIED UNIT REPRESENTATION:", r, flush=True)
        break
