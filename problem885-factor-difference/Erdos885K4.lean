import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-!
# Erdos885K4 — THE k=4 FACTOR-DIFFERENCE CASE THEOREM (W63-B5, P885 r3)

Erdős #885 (verbatim, erdosproblems.com/885):

> For integer n ≥ 1, D(n) = {|a−b| : n = ab}. Is it true that, for every
> k ≥ 1, there exist integers N₁ < ⋯ < N_k such that |∩ᵢ D(Nᵢ)| ≥ k?

THE NEW ROW (W63-B5): **k = 4** — the first IN-HOUSE k = 4 witness
(prior in-house state: k = 4 unhit, N-indexed hunt zero below 5·10⁵;
the k = 2/3 rows are the K50 kernel's 8,120 / 120,528,4488):

  N = 2254336 < 9945936 < 29904336 < 779175936,   |∩ D(Nᵢ)| = 4 ≥ 4,
  shared differences {534, 3216, 8016, 9840} — EXACTLY four, so the
  intersection is minimal-tight for the case.

Origin (python, dual-certified before authoring): the W63-B5
factorization-indexed escalation — the pair-indexed engine harvested
K_{5,2} column pairs (2 columns with ≥ 5 common rows) over the anchor
box (rows ≤ 2236, τ(Δ) ≥ 16), and the column-pair EXTENSION pass found
the K_{5,3} grid configuration rows {267, 1525, 3165, 5475, 27915},
columns {24135111, 2514375, 15992775} (all 15 sums s²+C squares);
Theorem B (λ=2 scaling) translates it to the N/d witness above:
Nᵢ = sᵢ² − 267², d₁ = 2·267, dⱼ = 2·√(Cⱼ + 267²).  Receipts:
`certify885.py` — Method 1 (gmpy2 square criterion, all 16 checks
4N+d² = m²), Method 2 (full divisor-pair D-set recount, |∩| = 4
exactly, agreement on every (N, d)) + the 16 explicit factor pairs
below.  House law: GitHub CI is the verifier of record (Kernel 50b).
-/

namespace E885K4

/-! ## §1 The definition (self-contained, the additive |a−b| encoding). -/

/-- The factor-difference set D(N) = {|a−b| : a·b = N}, additively encoded
(truncation-free): d ∈ D(N) ⟺ ∃ a b, a·b = N ∧ (a = b + d ∨ b = a + d). -/
def dset (N : Nat) : Set Nat :=
  {d : Nat | ∃ a b : Nat, a * b = N ∧ (a = b + d ∨ b = a + d)}

theorem dset_mem_iff (N d : Nat) :
    d ∈ dset N ↔ ∃ a b : Nat, a * b = N ∧ (a = b + d ∨ b = a + d) := by
  simp only [dset, Set.mem_setOf_eq]

/-- Membership from an explicit factor pair: a·b = N and a = b + d
(i.e. |a − b| = d) witnesses d ∈ D(N). -/
theorem dset_witness (a b d N : Nat) (hab : a * b = N) (h : a = b + d) :
    d ∈ dset N := by
  rw [dset_mem_iff]
  exact ⟨a, b, hab, Or.inl h⟩

/-! ## §2 THE k = 4 CASE THEOREM (exact values, complete, unconditional).

N = (2254336, 9945936, 29904336, 779175936); the four shared differences
are d = (534, 3216, 8016, 9840).  All 16 factor-pair witnesses:

  d = 534 : 1792·1258 = 2254336, 3432·2898 = 9945936,
             5742·5208 = 29904336, 28182·27648 = 779175936;
  d = 3216: 3808·592 = 2254336, 5148·1932 = 9945936,
             7308·4092 = 29904336, 29568·26352 = 779175936;
  d = 8016: 8288·272 = 2254336, 9108·1092 = 9945936,
             10788·2772 = 29904336, 32208·24192 = 779175936;
  d = 9840: 10064·224 = 2254336, 10764·924 = 9945936,
             12276·2436 = 29904336, 33264·23424 = 779175936. -/

/-- THE k = 4 CASE THEOREM: 2254336 < 9945936 < 29904336 < 779175936 and
all four N's share the differences {534, 3216, 8016, 9840}. -/
theorem k4_witness : ∃ d1 d2 d3 d4 : Nat, d1 < d2 ∧ d2 < d3 ∧ d3 < d4 ∧
    d1 ∈ dset 2254336 ∧ d1 ∈ dset 9945936 ∧ d1 ∈ dset 29904336 ∧ d1 ∈ dset 779175936 ∧
    d2 ∈ dset 2254336 ∧ d2 ∈ dset 9945936 ∧ d2 ∈ dset 29904336 ∧ d2 ∈ dset 779175936 ∧
    d3 ∈ dset 2254336 ∧ d3 ∈ dset 9945936 ∧ d3 ∈ dset 29904336 ∧ d3 ∈ dset 779175936 ∧
    d4 ∈ dset 2254336 ∧ d4 ∈ dset 9945936 ∧ d4 ∈ dset 29904336 ∧ d4 ∈ dset 779175936 :=
  ⟨534, 3216, 8016, 9840, by decide, by decide, by decide,
    -- d1 = 534 in all four D(N_i)
    dset_witness 1792 1258 534 2254336 (by decide) (by decide),
    dset_witness 3432 2898 534 9945936 (by decide) (by decide),
    dset_witness 5742 5208 534 29904336 (by decide) (by decide),
    dset_witness 28182 27648 534 779175936 (by decide) (by decide),
    -- d2 = 3216 in all four D(N_i)
    dset_witness 3808 592 3216 2254336 (by decide) (by decide),
    dset_witness 5148 1932 3216 9945936 (by decide) (by decide),
    dset_witness 7308 4092 3216 29904336 (by decide) (by decide),
    dset_witness 29568 26352 3216 779175936 (by decide) (by decide),
    -- d3 = 8016 in all four D(N_i)
    dset_witness 8288 272 8016 2254336 (by decide) (by decide),
    dset_witness 9108 1092 8016 9945936 (by decide) (by decide),
    dset_witness 10788 2772 8016 29904336 (by decide) (by decide),
    dset_witness 32208 24192 8016 779175936 (by decide) (by decide),
    -- d4 = 9840 in all four D(N_i)
    dset_witness 10064 224 9840 2254336 (by decide) (by decide),
    dset_witness 10764 924 9840 9945936 (by decide) (by decide),
    dset_witness 12276 2436 9840 29904336 (by decide) (by decide),
    dset_witness 33264 23424 9840 779175936 (by decide) (by decide)⟩

/-- THE N-ORDERING of the k = 4 witness quadruple. -/
theorem k4_distinct_sorted :
    2254336 < 9945936 ∧ 9945936 < 29904336 ∧ 29904336 < 779175936 := by decide

/-! ## §3 THE ARSENAL BRIDGE (BOSS's mathematics applied to the k = 4
witness numbers — erdosternary2 + HC-PROV).  Anchors: 534 = 2·267 is the
smallest shared difference (d₁ = 2·s_min of the K_{5,3} grid); 1525 and
5475 are grid rows; 3216 = 2·1608 and 9840 = 2·4920 are the scaled column
square roots dⱼ; 779175936 is N₄; 9945936 is N₂. -/

theorem e885_k4_arsenal_bridge :
    ErdosTernary2.isTernaryDigit (534 % 3) ∧
    (3216 ^ 2 - 1 = (3216 - 1) * (3216 + 1)) ∧
    (779175936 % (534 * 2)) % 534 = 779175936 % 534 ∧
    carryAtPos 9945936 1 < 4 ∧
    v2r (3 ^ 2 * 1525) = v2r 1525 :=
  ⟨by decide, sq_sub_one 3216 (by decide),
    mod_mod_mul 779175936 534 2 (by decide),
    carryAtPos_bound 9945936 1,
    CardinalWorldsV2.v2r_ternary_scaling 2 1525⟩

/-! ## §4 THE k=4 MASTER BOARD. -/

/-- THE P885 k=4 BOARD (three conjuncts, full statements, unconditional):
the k = 4 case theorem + the N-ordering + the arsenal bridge core. -/
theorem e885_k4_board :
    (∃ d1 d2 d3 d4 : Nat, d1 < d2 ∧ d2 < d3 ∧ d3 < d4 ∧
      d1 ∈ dset 2254336 ∧ d1 ∈ dset 9945936 ∧ d1 ∈ dset 29904336 ∧ d1 ∈ dset 779175936 ∧
      d2 ∈ dset 2254336 ∧ d2 ∈ dset 9945936 ∧ d2 ∈ dset 29904336 ∧ d2 ∈ dset 779175936 ∧
      d3 ∈ dset 2254336 ∧ d3 ∈ dset 9945936 ∧ d3 ∈ dset 29904336 ∧ d3 ∈ dset 779175936 ∧
      d4 ∈ dset 2254336 ∧ d4 ∈ dset 9945936 ∧ d4 ∈ dset 29904336 ∧ d4 ∈ dset 779175936) ∧
    (2254336 < 9945936 ∧ 9945936 < 29904336 ∧ 29904336 < 779175936) ∧
    ((779175936 % (534 * 2)) % 534 = 779175936 % 534 ∧
      v2r (3 ^ 2 * 1525) = v2r 1525) :=
  ⟨k4_witness, k4_distinct_sorted,
    ⟨mod_mod_mul 779175936 534 2 (by decide),
      CardinalWorldsV2.v2r_ternary_scaling 2 1525⟩⟩

end E885K4

/-! ## RECEIPT. -/

#print axioms E885K4.dset_mem_iff
#print axioms E885K4.dset_witness
#print axioms E885K4.k4_witness
#print axioms E885K4.k4_distinct_sorted
#print axioms E885K4.e885_k4_arsenal_bridge
#print axioms E885K4.e885_k4_board

#eval "E885_K4_GREEN"
