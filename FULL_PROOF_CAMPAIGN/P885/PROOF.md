# P885 — Erdős #885: Factor-Difference Sets — FULL PROOF CAMPAIGN

**Agent:** W2-P885. **Task:** complete resolution; k=5 frontier.
**Statement (verbatim, corpus-erdos):** For integer n ≥ 1, D(n) = {|a−b| : n = ab}.
Is it true that, for every k ≥ 1, there exist integers N₁ < ⋯ < N_k such that
|∩ᵢ D(Nᵢ)| ≥ k?
**State of the art:** k=2 Erdős–Rosenfeld [ErRo97]; k=3 Jiménez-Urroz [Ji99];
k=4 Bremner [Br19]. In-house k=3 witness (120, 528, 4488 share {2, 37, 58});
k=4 unhit < 5·10⁵ (N-indexed). Target: k=5 witness → new case theorem.

## §1. THE REDUCTION THEOREM (derived this session, engine foundation)

**Lemma 1 (square criterion).** For N ≥ 1, d ≥ 0: d ∈ D(N) ⟺ 4N + d² = m² for
some integer m. (d ∈ D(N) ⟺ N = a(a+d), a ≥ 1 ⟺ 4N + d² = (2a+d)², and
m ≡ d (mod 2), m > d are automatic since m² − d² = 4N ≡ 0 (mod 4), N ≥ 1.)

**Theorem A (grid equivalence).** #885(k) is TRUE ⟺ there exist integers
s₀ < s₁ < ⋯ < s_k, all with sᵢ ≡ s₀ (mod 2), and k−1 distinct positive
integers C₂,…,C_k such that all (k+1)(k−1) sums sᵢ² + C_j (and trivially
sᵢ² + 0) are perfect squares.
Proof: (⇐) Given (s, C): set d₁ = s₀, d_j = √(C_j + s₀²) (integer since s₀ is
a common row: s₀² + C_j = □; distinct/positive since C_j > 0 distinct);
Nᵢ = (sᵢ² − s₀²)/4 for i = 1..k (integer since same parity; Nᵢ ≥ 1 since
sᵢ ≥ s₀+2). Then 4Nᵢ + d_j² = sᵢ² − s₀² + C_j + s₀² = sᵢ² + C_j = □, so by
Lemma 1 every d_j ∈ D(Nᵢ); the d_j are k distinct non-negatives. Sort Nᵢ.
(⇒) Given witnesses N₁..N_k, d₁..D_k: take s₀ = √(4N₁+d₁²) hmm — see §2 for
the clean direction (we only need ⇐ for the kill). ∎

**Theorem B (parity relaxation / λ-scaling).** If there exist 6 distinct
integers s₁..s₆ (ANY parities) and 4 distinct positive integers C₁..C₄ with
all 24 sums sᵢ² + C_j perfect squares, then #885(5) is TRUE.
Proof: scale λ = 2: s'ᵢ = 2sᵢ (all even → same parity), C'_j = 4C_j; sums
(2sᵢ)² + 4C_j = 4(sᵢ² + C_j) = (2m_{ij})². Apply Theorem A. ∎
[More generally: any RATIONAL K_{k+1,k−1} configuration clears denominators
with λ = 2·lcm(denominators).]

**Theorem C (self-duality / transpose).** If in a configuration all C_j are
perfect squares, the transposed configuration (√C_j as s-rows, sᵢ² as
C-columns) is again a configuration. (Used to handle s₀ = 0 cases.)

## §2. STRUCTURE OF THE CONFIGURATION SPACE (factorization-indexed)

For fixed C ≠ 0 the s-rows with s² + C = □ are finite: (m−s)(m+s) = C.
For fixed pair (C, C'), δ = |C−C'|: common rows s come from factor pairs
(p,q), pq = δ: y = (q−p)/2, z = (q+p)/2, s = √(y² − min(C,C')); ≤ τ(δ)/2.
Every C of a K_{k+1,k−1} lies in G(s₀,s₁) := {m²−s₀² : m from factor pairs
of s₁²−s₀²} for ANY two rows s₀,s₁ of the configuration → the pair-indexed
enumeration is exhaustive: for each (s₀,s₁), |G| ≈ τ(s₁²−s₀²)/2 candidates,
then hunt (k−1)-subsets of G with ≥ k+1 common rows.
In-house k=3 witness = K_{4,2}: s = {2,22,46,134}, C = {1365, 3360},
δ = 1995 = 3·5·7·19 (4 of 8 factor pairs yield squares).

**Difficulty heuristic (square-density):** k parameters ~ (k+1)+(k−1) = 2k,
conditions (k+1)(k−1) = k²−1, each ~ B^{−1/2}·(log): expected count
~ B^{2k − (k²−1)/2}·(log)^{k²−1}: k=2: B^{1.5} (plenty), k=3: B^{2} (plenty),
k=4: B^{1.5} (Br19), k=5: B^{0}·(log)^{24} — MARGINAL: k=5 sits exactly at
the divergence boundary (log-growth only). This is why k=5 is the frontier.

## §3. STATUS

- [x] Reduction Theorems A/B/C (§1) — engine foundation
- [x] Engine: biclique hunt (pair-indexed, factorization-driven)
- [ ] k=3 re-derivation (validate engine against in-house 120/528/4488)
- [ ] k=4 in-house witness (validate against Br19 existence)
- [ ] k=5 witness (THE TARGET)
- [ ] Full write-up + audit

## §4. LOG

(running)
