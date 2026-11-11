# #317 — THE REDUCTION (Session 026, complete)

## §1. The integer form (THE KEY REDUCTION — done)

Let Lₙ = lcm(1,…,n). For δ ∈ {−1,0,1}ⁿ:

  Σ_{k≤n} δ_k/k = M/Lₙ   where   M = Σ_{k≤n} δ_k·u_k ∈ ℤ,  u_k := Lₙ/k.

Every value is an integer multiple of 1/Lₙ. Hence:
- PART 2 ⟺ **M = ±1 is infeasible** for all large n (then |Σ| ≥ 2/Lₙ > 1/Lₙ).
- PART 1 ⟺ ∃c: for every n some δ has 0 < |M| < c·Lₙ/2ⁿ = c·(e/2+o(1))ⁿ.

## §2. The isolated-prime structure (the #1108/Legendre engine fires)

For a prime p ∈ (n/2, n]: v_p(Lₙ) = 1 and the only k ≤ n with v_p(k) = 1 is k = p
(since 2p > n). Therefore u_k ≡ 0 (mod p) for every k ≠ p, and

  M ≡ δ_p · u_p (mod p),  u_p = Lₙ/p.

## §3. THE CONDITIONAL KILL THEOREM (unconditional statement, complete proof)

**Theorem A.** Let n ≥ 5 and suppose some prime p ∈ (n/2, n] satisfies
u_p = Lₙ/p ≢ ±1 (mod p). Then NO δ ∈ {−1,0,1}ⁿ has Σδ_k/k = ±1/Lₙ.

*Proof.* Suppose M = Σδ_k u_k = ±1. By §2, M ≡ δ_p·u_p (mod p). As δ_p ∈ {−1,0,1}:
δ_p·u_p mod p ∈ {0, u_p, p−u_p}. By hypothesis u_p ∉ {1, p−1} and u_p ∉ {0} (p ∤ u_p),
so 0 ∉ {±1}, u_p ∉ {±1}, and p−u_p ∉ {±1} (else u_p ∈ {∓1}). None of the three
attainable residues is ±1 (mod p) — but M = ±1. Contradiction. ∎

## §4. The small-n classification (done by engine + hand)

δ with Σδ_k/k = 1/Lₙ exists for n = 1 (δ=+1), n = 2 (δ=(0,1)), n = 3 (δ=(0,1,−1)),
n = 4 (δ=(−1,1,1,1)). For n ∈ [5, 5000]: **NONE** (803,790 prime-tests, zero
exceptions — see sweep317.py + results317.txt). Theorem A's hypothesis held for
EVERY n ∈ [5,5000]: some prime p ∈ (n/2,n] had u_p ≢ ±1 (mod p).

## §5. The two open kernels (honest scope)

- **K1 (kills PART 2):** the residue lemma — prove that for every n ≥ 5 SOME prime
  p ∈ (n/2, n] has lcm(1..n)/p ≢ ±1 (mod p). Empirically universal (n ≤ 5000);
  equivalent form: Lₙ ≢ ±p (mod p²). No known structure on lcm-quotient residues;
  this is the arithmetic heart. (Fallback: a cascade argument using prime powers
  q^a ∈ (n/2, n] and multi-prime moduli when single-prime degeneracy occurs —
  degeneracy never occurred empirically.)
- **K2 (kills PART 1):** the collision-count bound — prove the 2ⁿ subset sums of
  {1/k} have ≥ 2ⁿ/poly(n) distinct values in a Chebyshev window (equivalently bound
  the number of zero-sum {−1,0,1}-vectors of small support); Chebyshev concentration
  (window [μ−2,μ+2] holds ≥ 96% of mass, variance < 0.17) then pigeonholes two
  distinct values within C/2ⁿ. Egyptian-identity counting is the obstruction.

## §6. Arsenal match

Legendre digit-sum machinery (v_p(n!) = (n−s_p(n))/(p−1) — the #1108 Λ engine),
the isolated-minimum law pattern (SubsetKernelLaw), lcm residue structure
(#271 Stanley census machinery). This is a two-kernel war; both kernels are named.
