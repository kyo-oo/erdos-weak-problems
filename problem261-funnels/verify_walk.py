from fractions import Fraction as F

def walk(n, cap=2_000_000):
    # Engine convention: n=1 -> start (3,2); n>=2 -> (n+1,n). State (N,v): take iff 2v>=N; v'=2v-N else 2v; N' = N+1.
    N, v = (3, 2) if n == 1 else (n + 1, n)
    takes = []
    while v != 0 and N <= cap:
        if 2 * v >= N:
            takes.append(N); v = 2 * v - N
        else:
            v = 2 * v
        N += 1
    return (N if v == 0 else None), takes

def greedy_frac(n, cap=2_000_000):
    # Independent method: exact-Fraction greedy, explicit witness, no walk state.
    # n=1: pieces forced >= 3 (the principled start (2,1) yields the degenerate t=1 witness {2}).
    x, a, W = F(n, 2 ** n), (3 if n == 1 else n + 1), []
    while x > 0 and a <= cap:
        p = F(a, 2 ** a)
        if x >= p:
            x -= p; W.append(a)
        a += 1
    return (a if x == 0 else None), W   # death modulus D = (last take) + 1 = a on exit

# (1) n<=400: methods agree; witnesses valid; invariants hold.
for n in range(1, 401):
    D1, tk = walk(n)
    D2, W = greedy_frac(n)
    assert D1 == D2 and tk == W and D1 is not None, n
    assert len(W) >= 2 and all(w > n for w in W) and len(set(W)) == len(W), n
    assert D1 % 2 == 1 and D1 > n
    # exact end-to-end: witness sums back to target
    assert sum(F(a, 2 ** a) for a in W) == F(n, 2 ** n)
print("n<=400: walk == exact-Fraction greedy (D, witness); t>=2; pieces>n; distinct; D odd; D>n; sum==n/2^n")

# (2) full cross-check against the C-engine receipts (v2_deaths.txt, n<=400)
eng = {}
for line in open("engine/run261/v2_deaths.txt"):
    p = line.split()
    if len(p) >= 2 and p[0].isdigit():
        eng[int(p[0])] = int(p[1])
bad = [n for n in range(1, 401) if eng.get(n) != walk(n)[0]]
assert not bad, bad[:10]
print(f"engine cross-check: all {min(400,len(eng))}-of-{len(eng)} receipts (n<=400) match my independent Python walk; 0 mismatches")

# (3) named deep receipts + exact integer identity check
for n, D in [(56, 12231), (100, 393), (200, 217), (3817, 155943)]:
    d, tk = walk(n, cap=3_000_000)
    assert d == D, (n, d, D)
    assert sum(a << (D - 1 - a) for a in tk) == n << (D - 1 - n)   # n*2^{D-1-n} = sum a*2^{D-1-a}
print("deep receipts: n=56->12231, n=100->393, n=200->217, n=3817->155943 (integer-scaled identity re-proven)")

# (4) coalescence determinism receipt: n=1 and n=2 share start (3,2) -> same D=9
assert walk(1)[0] == walk(2)[0] == 9 and walk(1)[1] == walk(2)[1] == [3, 6, 8]
print("coalescence: n=1,n=2 share start state (3,2); identical future; D=9; witness {3,6,8}")

# (5) the degenerate principled start for n=1: (2,1) dies at D=3 with the t=1 witness {2}
N, v, tk = 2, 1, []
while v != 0:
    if 2 * v >= N: tk.append(N); v = 2 * v - N
    else: v = 2 * v
    N += 1
assert (N, tk) == (3, [2])
print("principled n=1 start (2,1): dies D=3, witness {2} (t=1, degenerate) -> sub-Q2(1) instead uses {3,6,8}")

# (6) sample witnesses for the writeup table
for n in (1, 2, 3, 4, 5, 11, 26):
    d, tk = walk(n)
    print(f"  n={n}: D={d}, room={d-1-n}, witness W={tk}")
