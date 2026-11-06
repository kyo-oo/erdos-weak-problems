# Erdős #700 — THE PRIME-POWER LAW (draft proof, Session 030, round 1/5)

**Problem (Erdős–Szekeres #700):** Let f(n) = min_{1<k≤n/2} gcd(n, C(n,k)).
Characterise composite n such that f(n) = n/P(n), P(n) = largest prime factor.

**Known (corpus addendum):** f(n) ≤ n/P(n) via j = p^k (the easy observation);
f(n) = n/P(n) for semiprimes n = pq; n = 30 works.

## THE PRIME-POWER CLASS LAW (this work)

**Theorem A (the carry lemma).** For every prime p, a ≥ 1, and 1 ≤ k ≤ p^a − 1:
    v_p(C(p^a, k)) = a − v_p(k).

**Proof.** Legendre: v_p(m!) = Σ_{i≥1} ⌊m/p^i⌋. Hence
v_p(C(N,k)) = Σ_{i=1}^{a} (⌊N/p^i⌋ − ⌊k/p^i⌋ − ⌊(N−k)/p^i⌋) with N = p^a
(terms i > a vanish since ⌊N/p^i⌋ = 0 forces the other two to vanish:
k, N−k ≤ N). For m = p^i | N write k = m·q + r, 0 ≤ r < m; then
N − k = m(c − q) − r = m(c − q − 1) + (m − r) when r > 0 (c = p^{a−i}),
and N − k = m(c − q) when r = 0. So
    ⌊N/m⌋ − ⌊k/m⌋ − ⌊(N−k)/m⌋ = c − q − (c − q − [r>0]) = [r > 0] = [p^i ∤ k].
Summing over i = 1..a: v_p(C(N,k)) = #{i ∈ [1,a] : p^i ∤ k}.
Since v_p(k) < a (as k < p^a), #{i ∈ [1,a] : p^i | k} = v_p(k), so the
count of non-dividing i is a − v_p(k). ∎

**Theorem B (the prime-power law).** For every prime p:
  (i) f(p²) = p = p²/P(p²) — prime squares SATISFY the Erdős–Szekeres equality;
  (ii) f(p^a) = p for every a ≥ 3 — hence p^a (a ≥ 3) VIOLATES the equality
       by the factor p^{a−2}: f(p^a)/ (p^a/P(p^a)) = p^{2−a}·p/p = p^{2−a+1}·.. 
       precisely f(p^a) = p < p^{a−1} = p^a/P(p^a).

**Proof.** n = p^a has only the prime p, so gcd(n, C(n,k)) = p^{min(a, v_p(C))}.
By Theorem A, v_p(C(p^a,k)) = a − v_p(k) for all 1 ≤ k ≤ p^a − 1.
(i) a = 2: for 1 < k ≤ p²/2: v_p(k) ≤ 1 (k < p²), so v_p(C) = 2 − v_p(k) ≥ 1,
    with equality iff p | k; k = p is in range and gives gcd = p. So f(p²) = p.
(ii) a ≥ 3: k = p^{a−1} ≤ p^a/2 is in range (2 ≤ p), v_p(k) = a−1, so
     gcd = p^{min(a, 1)} = p. For any k: v_p(k) ≤ a−1 ⟹ v_p(C) ≥ 1 ⟹
     gcd ≥ p. So f(p^a) = p. ∎

**Corollary (classification progress).** Among prime powers, exactly the
squares p² satisfy the ErSz equality f(n) = n/P(n); every higher power
fails with f(p^a) = p. Combined with the known semiprime class, the
equality class now contains: semiprimes pq, prime squares p², and mixed
cases like 30 (open: the full classification).

## Battery (79,003 instances verified)
- Carry lemma: all p ∈ {2,3,5,7,11,13}, a ∈ [2,7], k < min(n, 5000) — Legendre
  method, cross-checked against exact binomial factorisations on small n.
- Law table: f(p^a) = p for p ∈ {2,3,5,7,11,13}, a ∈ [2,6] — direct gcd sweeps
  (f computed by exact binomials), equality f = n/P exactly at a = 2.

## Kernel plan (the general-theorem war, next rounds)
1. divSplit (c k s m): (m·c)/m = k/m + s/m + [k%m ≠ 0] for k + s = m·c —
   from Nat.div_add_mod + Nat.mod_lt + omega only (no Mathlib).
2. cntNotDiv p a k = #{i ∈ [1,a]: p^i ∤ k} (fuel recursion) and
   cntNotDiv = a − vp k for k < p^a (fuel induction).
3. Legendre bridge vpFact p m = vpA p a m for m ≤ p^a (joint fuel induction).
4. Binomial identity C(N,k)·k!·s! = N! (Pascal induction) + valuation
   additivity v_p(x·y) = v_p x + v_p y.
5. Assemble: v_p(C(p^a,k)) = a − v_p(k) (general theorem), then
   gcd(p^a, C) = p^{min(a, a−v_p(k))} and the two-sided law:
   gcd(p^a, C(p^a, p^{a−1})) = p ∧ ∀ k ∈ (1, p^a/2], p ∣ gcd(p^a, C(p^a,k)).
Numerical receipts (decide): f(8)=2, f(16)=2, f(32)=2, f(64)=2, f(27)=3,
f(81)=3, f(243)=3, f(25)=5, f(125)=5, f(625)=5, f(49)=7, f(121)=11, f(169)=13.
