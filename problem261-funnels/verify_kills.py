from fractions import Fraction as F
import itertools
def v(S): return sum(F(a, 2**a) for a in S)
ok = []
# (1) Borwein-Loring family (sub-Q1) + kernel identity, m<=30 (integer-scaled; exact Frac m<=10)
for m in range(1, 31):
    n = 2**(m+1) - m - 2
    assert sum((n+j) << (m-j) for j in range(1, m+1)) == n << m          # n2^m = sum (n+j)2^{m-j}
    assert sum(j * 2**(m-j) for j in range(1, m+1)) == 2**(m+1) - m - 2
    if m <= 10:
        W = list(range(n+1, n+m+1))
        assert v(W) == F(n, 2**n) and all(w > n for w in W) and len(set(W)) == m
ok.append("BoLo family m<=30: n/2^n=sum_{j=1..m}(n+j)/2^{n+j}; kernel id sum j2^{m-j}=2^{m+1}-m-2")
# (2) TOWER: halving identity via INTEGER scaling (k<=30), telescoping, disjointness, gaps
mk = [2**(k+2) - k - 3 for k in range(31)]
for k in range(31):
    m = mk[k]
    assert sum((m+i) << (k+1-i) for i in range(1, k+2)) == m << (k+1)   # {m_k}={m_k+1..m_k+k+1}
    for j in range(1, k+2):                                             # telescoping partial identity (integer form)
        assert sum((m+i) << (j-i) for i in range(1, j+1)) == (m+2)*(1 << j) - (m+j+2)
for k in range(13):                                                      # exact-Fraction spot check, small k
    assert v([mk[k]]) == v(list(range(mk[k]+1, mk[k]+k+2))), k
iv = [(mk[k], mk[k]+k+1) for k in range(31)]
for (a1, b1), (a2, b2) in itertools.combinations(iv, 2): assert b1 < a2 or b2 < a1
gaps = [mk[k+1] - (mk[k]+k+2) for k in range(30)]
assert all(g >= 1 for g in gaps) and gaps[-1] > 10**9
ok.append(f"TOWER: halving id k<=30 (int-scaled, exact Frac k<=13), telescoping id, regions disjoint, inter-cluster gaps grow to {gaps[-1]}")
# (3) x* partial sum + binary cluster receipt
xs = sum(F(mk[k], 2**mk[k]) for k in range(12))
def bits(fr, upto):
    s, out = fr, []
    for pos in range(1, upto):
        if s >= F(1, 2**pos): out.append(pos); s -= F(1, 2**pos)
    return out
ok.append(f"x* partial(12)={float(xs):.16f}; 1-bits<=60: {bits(xs,60)}")
# (4) three representations of 1/2 + block collision (Kill #5)
for S in ([2], [3, 6, 8], [4, 5, 6]): assert v(S) == F(1, 2)
assert v([4, 5]) == v([3, 8])
ok.append("1/2 reps {2},{3,6,8},{4,5,6}; block {4,5}=={3,8}")
# (5) AP rationality exact closed form
for (c, d) in [(9, 24), (1, 1), (5, 7), (1234, 99)]:
    q = F(1, 2**d)
    closed = F(1, 2**c) * (F(c) / (1-q) + F(d) * q / (1-q)**2)
    K = 400 // d + 1
    part = sum(F(c+k*d, 2**(c+k*d)) for k in range(K+1))
    assert 0 < closed - part < F(1, 2**200), (c, d)
ok.append("AP identity sum_{k>=0}(c+kd)2^{-(c+kd)}=2^{-c}[c/(1-q)+dq/(1-q)^2], 4 cases, |tail|<2^-200")
# (6) run-surplus identity via INTEGER scaling (incl. the sign-flip point)
for (s, d) in [(5, 3), (9, 24), (100, 7), (16777190, 24)]:
    lhs = sum((s+i) << (d-1-i) for i in range(1, d)) - (s << (d-1))     # =2^d-(s+d+1) iff identity
    assert lhs == (1 << d) - (s+d+1), (s, d)
assert 2**24 - 24 - 1 == 16777191 and 2**23 - 24 < 16777191 < 2**24 - 24
ok.append("run-surplus id (int-scaled) 4 cases; sign flip exactly at s=2^d-d-1 (=16777191 at d=24; fixes session-011 typo)")
# (7) gadget equation on Kill#6 census collision samples
for (s, E) in [(9, [10, 11, 13, 14]), (13, [14, 15, 16, 20, 21, 24]), (21, [22, 23, 24, 26, 27, 32]), (35, [36, 37, 38, 39, 42, 43, 45, 46])]:
    assert v([s]) == v(E)
    J = [e - s for e in E]
    assert F(s) * (1 - sum(F(1, 2**j) for j in J)) == sum(F(j, 2**j) for j in J)
ok.append("gadget equation s(1-sigma_J)=tau_J verified on 4 census collisions incl {9}={10,11,13,14}")
# (8) v([1..N]) = 2-(N+2)2^{-N} (x=2 uniqueness data)
for N in (1, 2, 5, 10, 50, 200):
    assert sum(F(a, 2**a) for a in range(1, N+1)) == 2 - F(N+2, 2**N)
ok.append("v([1..N])=2-(N+2)2^{-N} (N<=200) => v(N)=2; uniqueness of S=N proven in text")
print("\n".join("PASS " + s for s in ok))
