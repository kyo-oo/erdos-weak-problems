# Erdős #317 — Signed harmonic sums: exponentially small values + the minimal-value classification

**Statement (teorth/erdosproblems.com/317, OPEN):**

> Let c > 0 ... exists δ_k ∈ {−1,0,1} for 1 ≤ k ≤ n with 0 < |Σ_{1≤k≤n} δ_k/k| < c/2ⁿ?
> Is it true that for sufficiently large n, for any δ_k ∈ {−1,0,1},
> |Σ_{1≤k≤n} δ_k/k| > 1/[1,…,n] (the lcm) whenever the left-hand side is not zero?

**Success contract (what a COMPLETE resolution means):**
- PART 1 (positive): exhibit an absolute constant c and prove: for EVERY n ≥ 1 there
  exists δ ∈ {−1,0,1}ⁿ with 0 < |Σδ_k/k| < c/2ⁿ.
- PART 2 (negative/classification): prove: for all sufficiently large n, NO δ ∈ {−1,0,1}ⁿ
  has Σδ_k/k = ±1/Lₙ (Lₙ = lcm(1..n)) — equivalently every nonzero signed sum exceeds
  1/Lₙ. (We prove below this fails to be improvable: values 1/Lₙ occur at n ≤ 4 and
  never again in [5, 5000].)
- Weaker results that do NOT count: part-only resolutions, bounds c(n) → 0, finite
  verification ranges without the general theorem, "for infinitely many n" variants.

**Kills on this problem:** none yet (front opened Session 026; see DERIVATION.md —
the reduction theorem + the engine sweep are done; two kernels remain).
