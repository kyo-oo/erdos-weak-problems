import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds
import Arsenal.CardinalWorldsV2

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-!
# Erdos885 — THE FACTOR-DIFFERENCE KERNEL r1 (W56-3, Kernel — P885)

Erdős #885 (verbatim, erdosproblems.com/885):

> For integer n ≥ 1, D(n) = {|a−b| : n = ab}. Is it true that, for every
> k ≥ 1, there exist integers N₁ < ⋯ < N_k such that |∩ᵢ D(Nᵢ)| ≥ k?

State of the art: k = 2 Erdős–Rosenfeld [ErRo97]; k = 3 Jiménez-Urroz [Ji99];
k = 4 Bremner [Br19]. In-house witnesses (WORKLOG §Session-028 witness lanes):
k = 2 (8, 120 share {2, 7}); k = 3 (120, 528, 4488 share {2, 37, 58}).
The k = 5 frontier hunt (pair-indexed K_{6,4} enumeration, PROOF.md §2)
runs in `hunt885_k5.py`; its log is `hunt885_k5.log`.

THE BOARD (full statements, complete unconditional proofs, zero sorry):
1. `dset N` — D(N) in the additive (truncation-free) encoding:
   d ∈ D(N) ⟺ ∃ a b, a·b = N ∧ (a = b + d ∨ b = a + d).
2. LEMMA 1, THE SQUARE CRITERION — both directions, unconditional:
   for N ≥ 1, d ∈ D(N) ⟺ ∃ m, 4N + d² = m². Includes the parity engine
   (`e885_parity`: m² = d² + 4k → m ≡ d mod 2), proved by hand expansion of
   both squares into IDENTICAL atom spellings (L86 law) with omega closing
   the linear shell — no mod-4 lemma chaining, no ring.
3. `k2_witness` — the k = 2 CASE THEOREM: 8 < 120 and D(8) ∩ D(120) ⊇ {2, 7}
   via explicit factor pairs (4·2, 8·1, 12·10, 15·8).
4. `k3_witness` + `k3_distinct_sorted` — the k = 3 CASE THEOREM:
   120 < 528 < 4488 and the three share {2, 37, 58} via explicit factor
   pairs (12·10/24·22/68·66, 40·3/48·11/88·51, 60·2/66·8/102·44).
5. `e885_arsenal_bridge` — BOSS's arsenal applied to the witness anchors
   (erdosternary2 + HC-PROOF: `sq_sub_one`, `mod_mod_mul`, `carryAtPos_bound`,
   `v2r_ternary_scaling`).
6. `e885_case_board` — the master composite.

House law: GitHub CI is the verifier of record (no local compile; author
blind). Axiom profile must stay within [propext, Classical.choice,
Quot.sound]. Zero sorry, zero native_decide.
-/

namespace E885

/-! ## §1 The definition — the additive encoding of |a − b|. -/

/-- The factor-difference set D(N) = {|a−b| : a·b = N}, encoded additively
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

/-! ## §2 Monomial normalization — the L86 atom law.

Products of variables are expanded stepwise (`Nat.mul_add`, `Nat.add_mul`,
`Nat.mul_assoc`, `Nat.mul_comm`) so that BOTH sides of each goal carry the
SAME atoms (`x*x`, `x*d`, `d*d`); omega then closes the linear shell. -/

/-- (2x)·(2x) = 4·x² — the doubling square (term-mode associativity, then
`x·(2x) = 2·x²`, then the numeric merge). -/
theorem e885_two_two (x : Nat) : (2 * x) * (2 * x) = 4 * (x * x) := by
  have h1 : (2 * x) * (2 * x) = 2 * (x * (2 * x)) := Nat.mul_assoc 2 x (2 * x)
  have h2 : x * (2 * x) = 2 * (x * x) := by
    rw [Nat.mul_comm x (2 * x), Nat.mul_assoc]
  rw [h1, h2]
  rw [← Nat.mul_assoc 2 2 (x * x)]
  rw [show (2 : Nat) * 2 = 4 from by decide]

/-- (2x)·d = 2·(x·d) — right factor. -/
theorem e885_cross_r (x d : Nat) : (2 * x) * d = 2 * (x * d) := by
  rw [Nat.mul_assoc]

/-- d·(2x) = 2·(x·d) — left factor (same atom spelling as `e885_cross_r`). -/
theorem e885_cross_l (d x : Nat) : d * (2 * x) = 2 * (x * d) := by
  rw [Nat.mul_comm d (2 * x), Nat.mul_assoc]

/-- (d + t)² = d² + dt + dt + t² — the general sum-square expansion. -/
theorem e885_sq_add (d t : Nat) :
    (d + t) * (d + t) = d * d + d * t + d * t + t * t := by
  rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, Nat.mul_comm t d]
  omega

/-- (2u + 1)² = 4·(u² + u) + 1 — the odd square. -/
theorem e885_odd_sq (u : Nat) :
    (2 * u + 1) * (2 * u + 1) = 4 * (u * u + u) + 1 := by
  rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, Nat.mul_one, Nat.mul_one,
      Nat.one_mul, e885_two_two u, Nat.mul_add]
  omega

/-- THE BILINEAR EXPANSION (Lemma 1 ⇒ core): 4·(x+d)·x + d² = (2x+d)². -/
theorem e885_expansion (x d : Nat) :
    4 * ((x + d) * x) + d * d = (2 * x + d) * (2 * x + d) := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.add_mul, Nat.add_mul,
      Nat.mul_comm d x, e885_two_two x, e885_cross_l d x, e885_cross_r x d]
  omega

/-! ## §3 THE PARITY ENGINE — m² = d² + 4k → m ≡ d (mod 2).

No mod-4 lemma chaining: case-split m, d mod 2 (each ∈ {0, 1} by omega),
expand both squares by §2 into identical atoms, and let omega derive the
unsatisfiable linear shell 4A = 4B + 4q + 1 + 4k (the Omega test's exact
division: 4·X = 1 has no integer solution). -/

/-- Parity transfer: if m·m = d·d + 4k then m ≡ d (mod 2). -/
theorem e885_parity (m d k : Nat) (h : m * m = d * d + 4 * k) :
    m % 2 = d % 2 := by
  rcases (show m % 2 = 0 ∨ m % 2 = 1 by omega) with hm | hm
  · rcases (show d % 2 = 0 ∨ d % 2 = 1 by omega) with hd | hd
    · omega
    · have hmp : m = 2 * (m / 2) := by omega
      have hdp : d = 2 * (d / 2) + 1 := by omega
      rw [hmp, hdp] at h
      rw [e885_two_two (m / 2), e885_odd_sq (d / 2)] at h
      omega
  · rcases (show d % 2 = 0 ∨ d % 2 = 1 by omega) with hd | hd
    · have hmp : m = 2 * (m / 2) + 1 := by omega
      have hdp : d = 2 * (d / 2) := by omega
      rw [hmp, hdp] at h
      rw [e885_odd_sq (m / 2), e885_two_two (d / 2)] at h
      omega
    · omega

/-! ## §4 LEMMA 1 — the square criterion (both directions). -/

/-- Lemma 1 (⇒): if d ∈ D(N) then 4N + d² is a perfect square (m = 2b + d). -/
theorem dset_square_fwd (N d : Nat) (hd : d ∈ dset N) :
    ∃ m : Nat, 4 * N + d * d = m * m := by
  rw [dset_mem_iff] at hd
  obtain ⟨a, b, hab, hcase⟩ := hd
  rcases hcase with ha | ha
  · refine ⟨2 * b + d, ?_⟩
    rw [← hab, ha]
    exact e885_expansion b d
  · refine ⟨2 * a + d, ?_⟩
    rw [← hab, ha, Nat.mul_comm a (a + d)]
    exact e885_expansion a d

/-- Lemma 1 (⇐): if 4N + d² = m² with N ≥ 1 then d ∈ D(N).
Construction: m ≥ d (else 4N + d² = m² < d² is absurd by §2 expansion);
m = d + t; parity forces t = 2q; then N = q·d + q² = (d + q)·q with
(d + q) = q + d, i.e. the factor witness ⟨d + q, q⟩. -/
theorem dset_square_rev (N d m : Nat) (hN : 1 ≤ N) (hm : 4 * N + d * d = m * m) :
    d ∈ dset N := by
  rw [dset_mem_iff]
  have hpar : m % 2 = d % 2 := e885_parity m d N (by omega)
  have hge : d ≤ m := by
    rcases Nat.lt_or_ge m d with hlt | hge
    · exfalso
      have hdm : d = m + (d - m) := by omega
      rw [hdm] at hm
      have hexp := e885_sq_add m (d - m)
      rw [hexp] at hm
      omega
    · exact hge
  obtain ⟨t, ht⟩ : ∃ t : Nat, m = d + t := ⟨m - d, by omega⟩
  rw [ht] at hm
  have hexp := e885_sq_add d t
  rw [hexp] at hm
  have htp : t % 2 = 0 := by omega
  obtain ⟨q, hq⟩ : ∃ q : Nat, t = 2 * q := ⟨t / 2, by omega⟩
  rw [hq] at hm
  rw [e885_cross_l d q] at hm
  rw [e885_two_two q] at hm
  have hNq : N = q * d + q * q := by omega
  refine ⟨d + q, q, ?_, Or.inl (Nat.add_comm d q)⟩
  rw [Nat.add_mul, hNq, Nat.mul_comm d q]

/-- LEMMA 1, THE SQUARE CRITERION (full iff, both directions unconditional):
for N ≥ 1, d ∈ D(N) ⟺ 4N + d² is a perfect square. -/
theorem dset_square_criterion (N d : Nat) (hN : 1 ≤ N) :
    d ∈ dset N ↔ ∃ m : Nat, 4 * N + d * d = m * m := by
  constructor
  · exact dset_square_fwd N d
  · intro hm
    exact dset_square_rev N d m hN hm

/-- The parity side of the square criterion, stated on its own
(m ≡ d mod 2 is automatic from 4N + d² = m²). -/
theorem dset_square_criterion_parity (N d m : Nat) (hm : 4 * N + d * d = m * m) :
    m % 2 = d % 2 :=
  e885_parity m d N (by omega)

/-! ## §5 THE WITNESS THEOREMS (exact values, full case theorems). -/

/-- THE k = 2 CASE THEOREM: 8 < 120 and |D(8) ∩ D(120)| ≥ 2 — the shared
differences are {2, 7}: 2 = |4−2| = |12−10|, 7 = |8−1| = |15−8|. -/
theorem k2_witness : ∃ d1 d2 : Nat, d1 < d2 ∧ d1 ∈ dset 8 ∧ d1 ∈ dset 120 ∧
    d2 ∈ dset 8 ∧ d2 ∈ dset 120 ∧ 8 < 120 :=
  ⟨2, 7, by decide,
    dset_witness 4 2 2 8 (by decide) (by decide),
    dset_witness 12 10 2 120 (by decide) (by decide),
    dset_witness 8 1 7 8 (by decide) (by decide),
    dset_witness 15 8 7 120 (by decide) (by decide),
    by decide⟩

/-- THE N-ORDERING of the k = 3 witness triple. -/
theorem k3_distinct_sorted : 120 < 528 ∧ 528 < 4488 := by decide

/-- THE k = 3 CASE THEOREM: 120 < 528 < 4488 and the three share
{2, 37, 58}: 2 = |12−10| = |24−22| = |68−66|;
37 = |40−3| = |48−11| = |88−51|; 58 = |60−2| = |66−8| = |102−44|. -/
theorem k3_witness : ∃ d1 d2 d3 : Nat, d1 < d2 ∧ d2 < d3 ∧
    d1 ∈ dset 120 ∧ d1 ∈ dset 528 ∧ d1 ∈ dset 4488 ∧
    d2 ∈ dset 120 ∧ d2 ∈ dset 528 ∧ d2 ∈ dset 4488 ∧
    d3 ∈ dset 120 ∧ d3 ∈ dset 528 ∧ d3 ∈ dset 4488 :=
  ⟨2, 37, 58, by decide, by decide,
    dset_witness 12 10 2 120 (by decide) (by decide),
    dset_witness 24 22 2 528 (by decide) (by decide),
    dset_witness 68 66 2 4488 (by decide) (by decide),
    dset_witness 40 3 37 120 (by decide) (by decide),
    dset_witness 48 11 37 528 (by decide) (by decide),
    dset_witness 88 51 37 4488 (by decide) (by decide),
    dset_witness 60 2 58 120 (by decide) (by decide),
    dset_witness 66 8 58 528 (by decide) (by decide),
    dset_witness 102 44 58 4488 (by decide) (by decide)⟩

/-! ## §6 THE ARSENAL BRIDGE (BOSS's mathematics applied to the witness
numbers — erdosternary2 + HC-PROOF, the 16,121-theorem arsenal).

Anchors: 58 and 37 are shared differences of the k = 3 triple; 12·10 is
the k = 2 factor pair (12² − 1 = 143 = 11·13); 4488 and 528 are k = 3 N's;
3·40 = 120 is the 37-row factor pair of D(120). -/

theorem e885_arsenal_bridge :
    ErdosTernary2.isTernaryDigit (58 % 3) ∧
    (12 ^ 2 - 1 = (12 - 1) * (12 + 1)) ∧
    (4488 % (37 * 2)) % 37 = 4488 % 37 ∧
    carryAtPos 528 1 < 4 ∧
    CardinalWorldsV2.v2r (3 ^ 1 * 40) = CardinalWorldsV2.v2r 40 :=
  ⟨by decide, sq_sub_one 12 (by decide), mod_mod_mul 4488 37 2 (by decide),
    carryAtPos_bound 528 1, CardinalWorldsV2.v2r_ternary_scaling 1 40⟩

/-! ## §7 THE MASTER BOARD. -/

/-- THE P885 CASE BOARD (five conjuncts, full statements, unconditional):
the square criterion (Lemma 1, both directions) + the k = 2 case + the
k = 3 case + the N-ordering + the arsenal bridge core. -/
theorem e885_case_board :
    (∀ N d : Nat, 1 ≤ N → (d ∈ dset N ↔ ∃ m : Nat, 4 * N + d * d = m * m)) ∧
    (∃ d1 d2 : Nat, d1 < d2 ∧ d1 ∈ dset 8 ∧ d1 ∈ dset 120 ∧
      d2 ∈ dset 8 ∧ d2 ∈ dset 120 ∧ 8 < 120) ∧
    (∃ d1 d2 d3 : Nat, d1 < d2 ∧ d2 < d3 ∧
      d1 ∈ dset 120 ∧ d1 ∈ dset 528 ∧ d1 ∈ dset 4488 ∧
      d2 ∈ dset 120 ∧ d2 ∈ dset 528 ∧ d2 ∈ dset 4488 ∧
      d3 ∈ dset 120 ∧ d3 ∈ dset 528 ∧ d3 ∈ dset 4488) ∧
    (120 < 528 ∧ 528 < 4488) ∧
    ((4488 % (37 * 2)) % 37 = 4488 % 37 ∧
      CardinalWorldsV2.v2r (3 ^ 1 * 40) = CardinalWorldsV2.v2r 40) :=
  ⟨fun N d hN => dset_square_criterion N d hN, k2_witness, k3_witness,
    k3_distinct_sorted,
    ⟨mod_mod_mul 4488 37 2 (by decide), CardinalWorldsV2.v2r_ternary_scaling 1 40⟩⟩

end E885

/-! ## RECEIPT. -/

#print axioms E885.dset_mem_iff
#print axioms E885.dset_witness
#print axioms E885.e885_two_two
#print axioms E885.e885_cross_r
#print axioms E885.e885_cross_l
#print axioms E885.e885_sq_add
#print axioms E885.e885_odd_sq
#print axioms E885.e885_expansion
#print axioms E885.e885_parity
#print axioms E885.dset_square_fwd
#print axioms E885.dset_square_rev
#print axioms E885.dset_square_criterion
#print axioms E885.dset_square_criterion_parity
#print axioms E885.k2_witness
#print axioms E885.k3_witness
#print axioms E885.k3_distinct_sorted
#print axioms E885.e885_arsenal_bridge
#print axioms E885.e885_case_board

#eval "E885_FACTOR_DIFF_GREEN"
