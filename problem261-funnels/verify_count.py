import numpy as np

def pattern_sets(T, mincard):
    # Enumerate ALL 2^T patterns P subseteq {1..T}: A_P=sum 2^{T-j}, S_P=sum j*2^{T-j};
    # n = S_P/(2^T-A_P) when integral, n>=1, |P|>=mincard.  Returns set of certified n.
    m = np.arange(1 << T, dtype=np.int64)
    A = np.zeros_like(m); S = np.zeros_like(m); card = np.zeros_like(m)
    for j in range(1, T + 1):
        bit = (m >> (j - 1)) & 1
        A += bit << (T - j); S += bit * (j << (T - j)); card += bit
    den = (1 << T) - A                     # in [1, 2^T]
    q, r = np.divmod(S, den)
    sel = (r == 0) & (q >= 1) & (card >= mincard)
    return set(np.unique(q[sel]).tolist())

S2, Sany = {}, {}
for T in range(1, 21):
    Sany[T] = pattern_sets(T, 1)           # any nonempty pattern (toggle supply)
    S2[T] = pattern_sets(T, 2)             # sub-Q2-valid (t>=2)
    assert len(S2[T]) <= (1 << T) and len(Sany[T]) <= (1 << T)
    print(f"T={T:2d}: |S_T(t>=2)|={len(S2[T]):5d} <= 2^T={1<<T:6d};  max n certified={max(Sany[T])}")
for T in range(1, 20):
    assert S2[T] <= S2[T+1] and Sany[T] <= Sany[T+1], T   # witnesses persist at larger windows
print("monotonicity S_T subseteq S_{T+1}: verified (same witness, larger window)")

# Cross-check vs session-011 Corollary 2.2 (their 'singleton family', window<=20, s<=200):
c22 = {1,2,3,4,5,6,7,9,11,12,13,15,17,18,19,21,26,27,32,35,57,73,78,116,120,125,166,197,198,199,200}
mine = {n for n in Sany[20] if n <= 200}
print("session-011 Corollary 2.2 (window<=20, n<=200): exact match =", mine == c22)

# Minimal rooms vs greedy rooms (n<=200): greedy room >= minimal room always.
def walkD(n):
    N, v = (3, 2) if n == 1 else (n + 1, n)
    while v != 0:
        v = 2*v - N if 2*v >= N else 2*v
        N += 1
    return N
room = {n: min(T for T in range(1, 21) if n in Sany[T]) for n in range(1, 201) if any(n in Sany[T] for T in range(1, 21))}
viol = [n for n in room if walkD(n) - 1 - n < room[n]]
print(f"n<=200 with a representation at window<=20: {len(room)}/200; greedy-room >= min-room violations: {viol}")
strict = [(n, walkD(n)-1-n, room[n]) for n in sorted(room) if walkD(n)-1-n > room[n]][:12]
print("greedy strictly suboptimal (n, greedy room, min room):", strict)

# The COUNT theorem's punchline data:
print(f"largest n with room<=20: {max(Sany[20])}; |S_20|={len(Sany[20])}; i.e. only {len(Sany[20])} values of n "
      f"have ANY representation with pieces in (n,n+20]; every other n (incl. all n>{max(Sany[20])}) needs room>20")
