# P273 — Covering system with distinct moduli p−1 (p ≥ 5 prime) — FULL PROOF

**Agent W2-P273. Status: IN PROGRESS — construction lane.**
Target: explicit covering system {x ≡ a_i (mod n_i)}: distinct n_i, every n_i = p_i − 1,
p_i ≥ 5 prime, ∪ classes = ℤ. The witness table = unconditional proof.

## §1. THE REDUCTION (parity halving)

Every modulus n = p−1 = 2m is even. A class a mod 2m lies in one parity.
- x = 2y (even): x ≡ 2b (mod 2m) ⟺ y ≡ b (mod m).
- x = 2y+1 (odd): x ≡ 2c+1 (mod 2m) ⟺ y ≡ c (mod m).

**Lemma 1.** A covering system with distinct moduli {2m_i}, 2m_i = p_i − 1, p_i ≥ 5 prime,
exists ⟺ there exist two covering systems of ℤ, C_E = {(b_j, m_j)}, C_O = {(c_k, m'_k)},
with all m_j, m'_k ∈ M := {m ≥ 2 : 2m+1 prime}, pairwise distinct (disjoint modulus sets).
Lift: (b, m) ↦ class (2b mod 2m) [p = 2m+1]; (c, m) ↦ (2c+1 mod 2m).

*Proof.* (⇐) even integers 2y: y covered by C_E ⟹ 2y ≡ 2b_j (mod 2m_j). Odd: C_O.
Distinct m ⟹ distinct moduli 2m = p−1. (⇒) split classes by residue parity, halve. ∎

This explains round-1's 9.58% plateau: the annealing fought BOTH covers simultaneously
without the structure. Density check: need Σ_E 1/m ≥ 1 and Σ_O 1/m ≥ 1,
i.e. Σ 1/(p−1) ≥ 1 total — consistent with 1.1057 available (each side ~0.55).

## §2. THE CONSTRUCTION ENGINE — split-tiling trees

**Lemma 2 (tree lemma).** Let T be a finite prefix-split tree of residue classes:
root (0 mod 1); each internal node (c mod ν) split by a prime q into children
(c + jν mod qν), j = 0..q−1 (these partition the node). Leaves (c_j mod ν_j)
partition ℤ (Σ_j 1/ν_j = 1). Suppose each leaf is assigned a distinct m_j ∈ M
with m_j | ν_j. Then {(c_j mod m_j)} is a covering system of ℤ with distinct
moduli in M. (x ≡ c_j mod ν_j ⟹ x ≡ c_j mod m_j.)

**Corollary.** Two such trees T_E, T_O with globally distinct assigned m's
(T_E even m, T_O odd m — automatically disjoint), lifted by Lemma 1
⟹ **covering system with distinct moduli p−1.**

No residue search: residues come from the tree. Each leaf needs a fresh divisor
m ∈ M of its modulus ν (Hall-type; pools huge — M ∩ div(ν) grows with ν).

## §3. STATUS

- [x] Reduction derived (§1)
- [x] Tree engine designed (§2)
- [ ] engine273.py: greedy tree growth, both trees close
- [ ] Witness table + full verification
- [ ] PROOF.md final

## §4. LOG

- t0: read BRIEF §0–§3, §5-W2-P273 + all problem273-pminus1-covering/ files
  (hunt273{,b,c,d}.py, anneal273.py, L=720720 log). Reduction §1 found; engine designed.
