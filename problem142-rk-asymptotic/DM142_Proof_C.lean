import Mathlib
import FC.Combinatorics.AP.Basic
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds

/-!
# DM142_Proof_C — U-GEN-0: THE BLOCK FLOOR LAW (W84-142A)

BOSS's W84 order: the derived-and-engine-validated laws of the W80-142U
upper envelope, kernel'd over the OFFICIAL definition (FC/Combinatorics/
AP/Basic.lean, byte-identical to google-deepmind/formal-conjectures
@ 2207c54d):

    noncomputable abbrev r := Set.IsAPOfLengthFree.maxCard

This kernel proves **LAW U-GEN-0** (NEW_LAWS_142.md, complete; derived
WORKLOG_W80_142U.md event 3; engine-validated 56/56 by engine142uppergen.py
— codes X and Y agreeing on every table):

1. **THE BLOCK FLOOR LAW, ALL k ≥ 3, ALL N ≥ 1** `u_gen_zero` :
   `r k N ≤ N − N / k` (Nat division = floor). Partition [1, N] into
   ⌊N/k⌋ consecutive k-blocks + tail; a full k-block is a non-trivial
   k-AP (difference 1), so a k-AP-free set misses ≥ 1 point from each
   full block; the tail contributes ≤ N mod k. Banked at
   `N − ⌊N/k⌋ = ⌊N/k⌋·(k−1) + (N mod k)`.
2. **TIGHTNESS AT N = k** `u_gen_zero_tight` : `r k k = k − 1`
   (k ≥ 3). The ≤ side is U-GEN-0 at N = k (k/k = 1); the ≥ side is the
   witness {1, …, k−1} (any (k−1)-set is k-AP-free: a k-AP has ENat-card
   k, which cannot fit inside a set of cardinality k − 1).
3. The window engine: `window_isAP` (a full k-block IS an official
   k-AP with difference 1), `window_bound` (a k-AP-free set meets each
   full block in ≤ k−1 points), `window_union_bound` (the induction
   accumulating ⌊N/k⌋ block bounds), `core_bound` (assembly + the
   truncated-ℕ arithmetic spine).

The frozen F-UP-1 floor `N − ⌊N/k⌋ + 1` follows by +1; SLIDE-GEN's d=1
window mechanism is exactly this kernel's block engine (same partition,
no size hypothesis — the statement needs no N-hypothesis beyond 1 ≤ N);
both recorded in the lane worklog WORKLOG_W84_142C.md.

## ARSENAL BRIDGE (read-before-cite, file:line verified this session)
- `Arsenal.CardinalWorlds.mul_add_div_lemma` [Arsenal/CardinalWorlds.lean:143]
  — the division bookkeeping of the block count (worklog D3's derivation
  spine): the tightness companion's `k / k = 1` IS the block-count identity
  `(k·1 + 0)/k = 1 + 0/k` — genuinely used below (`u_gen_zero_tight`).
- `Arsenal.CardinalWorlds.mod_mod_mul` [Arsenal/CardinalWorlds.lean:140] —
  the residue discipline of the block/tail split: cited by the W80-142U
  derivation (D3); the kernel's residue fact is carried by
  `Nat.div_add_mod` + `Nat.mod_lt` (core), so mod_mod_mul is not
  load-bearing here — recorded honestly.

## HOUSE MACHINERY ATTRIBUTION
§0 follows the green sibling DM142_Proof_A.lean (W82-142A, CI-green on
run 45036892102): `nsmul_nat`, `coe_lt_coe_k`, `maxCard_ge_of_witness`
(copied verbatim with attribution), plus this lane's own `coe_sub` /
`apFree_subset` transfer lemmas.

## LAWS OF THE HOUSE
Zero sorry/sorryAx; zero native_decide; `#print axioms` on every headline;
CI (`kernel-dm-w84`, step 142DM-C) is the only Lean verdict. Never
compiled locally — GitHub Actions only.
-/
set_option maxHeartbeats 16000000
set_option maxRecDepth 262144

namespace DM142C

/-- The OFFICIAL r_k(N) — the same abbrev DM142_Official.lean declares. -/
noncomputable abbrev r : ℕ → ℕ → ℕ := Set.IsAPOfLengthFree.maxCard

/-! ## §0 House machinery (the DM142_Proof_A idiom, attributed) -/

/-- The ℕ-smul identity (the official set-builder writes `a + n • d`). -/
theorem nsmul_nat (i d : ℕ) : i • d = i * d := by simp

/-- Cast: `i < k` lifts through the ℕ∞ coercion (DM142_Proof_A idiom). -/
theorem coe_lt_coe_k {i k : ℕ} (h : i < k) : ((i : ℕ) : ENat) < ((k : ℕ) : ENat) :=
  by exact_mod_cast h

/-- Finset subset → coerced-set subset (via mem_coe, the green idiom). -/
theorem coe_sub {S T : Finset ℕ} (h : S ⊆ T) : (↑S : Set ℕ) ⊆ (↑T : Set ℕ) := by
  intro z hz
  exact Finset.mem_coe.2 (h (Finset.mem_coe.1 hz))

/-- AP-freeness passes to subsets (official definition, one line). -/
theorem apFree_subset {s t : Set ℕ} {k : ℕ∞} (hs : s.IsAPOfLengthFree k)
    (hst : t ⊆ s) : t.IsAPOfLengthFree k := by
  intro u hut hu
  exact hs u (hut.trans hst) hu

/-- AP-freeness passes to Finset intersections on the left. -/
theorem apFree_coe_inter_left (S W : Finset ℕ) {k : ℕ∞}
    (h : (↑S : Set ℕ).IsAPOfLengthFree k) :
    (↑(S ∩ W) : Set ℕ).IsAPOfLengthFree k :=
  apFree_subset h (coe_sub Finset.inter_subset_left)

/-- The sSup-membership transfer (from the maxCard definition alone;
DM142_Proof_A.lean §0, copied verbatim with attribution). -/
theorem maxCard_ge_of_witness {k N : ℕ} (S : Finset ℕ)
    (hsub : S ⊆ Finset.Icc 1 N) (hfree : (S : Set ℕ).IsAPOfLengthFree k) :
    S.card ≤ Set.IsAPOfLengthFree.maxCard k N := by
  simp only [Set.IsAPOfLengthFree.maxCard]
  refine le_csSup ?_ ⟨S, hsub, hfree, rfl⟩
  refine ⟨(Finset.Icc 1 N).card, mem_upperBounds.2 ?_⟩
  rintro n ⟨T, hTsub, -, rfl⟩
  exact Finset.card_mono hTsub

/-! ## §1 THE WINDOW LAW: a full k-block is an official k-AP -/

/-- **The window-AP lemma.** For k ≥ 1 and any offset m, the block
{m+1, …, m+k} (as a coerced Finset) is an official arithmetic progression
of length k with first term m+1 and difference 1. -/
theorem window_isAP (m k : ℕ) (hk : 1 ≤ k) :
    Set.IsAPOfLength (↑(Finset.Icc (m + 1) (m + k)) : Set ℕ) ((k : ℕ) : ENat) := by
  refine ⟨m + 1, 1, ?_, ?_⟩
  · show (↑(Finset.Icc (m + 1) (m + k)) : Set ℕ).encard = ((k : ℕ) : ENat)
    have hcard : (Finset.Icc (m + 1) (m + k)).card = k := by
      rw [Nat.card_Icc]; omega
    rw [Set.encard_coe_eq_coe_finsetCard, hcard]
  · ext x
    constructor
    · intro hx
      have hxc : x ∈ Finset.Icc (m + 1) (m + k) := Finset.mem_coe.1 hx
      simp only [Finset.mem_Icc] at hxc
      obtain ⟨h1, h2⟩ := hxc
      exact ⟨x - (m + 1), coe_lt_coe_k (by omega), by
        rw [nsmul_nat, Nat.mul_one, Nat.add_sub_cancel' h1]⟩
    · rintro ⟨n, hn, heq⟩
      have hn' : n < k := by exact_mod_cast hn
      rw [nsmul_nat, Nat.mul_one] at heq
      refine Finset.mem_coe.2 ?_
      simp only [Finset.mem_Icc]
      omega

/-! ## §2 THE WINDOW BOUND: each full block costs ≥ 1 point -/

/-- **The per-block bound.** A k-AP-free Finset S (k ≥ 2) meets any full
k-block in at most k − 1 points: if it met all k, the block itself would
be a k-AP (difference 1) inside S, contradicting freeness (k ≥ 2). -/
theorem window_bound (k m : ℕ) (hk : 2 ≤ k) (S : Finset ℕ)
    (hSfree : (↑S : Set ℕ).IsAPOfLengthFree ((k : ℕ) : ENat)) :
    (S ∩ Finset.Icc (m + 1) (m + k)).card ≤ k - 1 := by
  by_contra hcon
  push_neg at hcon
  have hsubW : S ∩ Finset.Icc (m + 1) (m + k) ⊆ Finset.Icc (m + 1) (m + k) :=
    Finset.inter_subset_right
  have hcardW : (Finset.Icc (m + 1) (m + k)).card = k := by
    rw [Nat.card_Icc]; omega
  have hle : (S ∩ Finset.Icc (m + 1) (m + k)).card ≤
      (Finset.Icc (m + 1) (m + k)).card := Finset.card_mono hsubW
  have heq : S ∩ Finset.Icc (m + 1) (m + k) = Finset.Icc (m + 1) (m + k) :=
    Finset.eq_of_subset_of_card_le hsubW (by omega)
  have hWSfin : Finset.Icc (m + 1) (m + k) ⊆ S := by
    rw [← heq]; exact Finset.inter_subset_left
  have hWSc : (↑(Finset.Icc (m + 1) (m + k)) : Set ℕ) ⊆ (↑S : Set ℕ) :=
    coe_sub hWSfin
  have hap : Set.IsAPOfLength (↑(Finset.Icc (m + 1) (m + k)) : Set ℕ)
      ((k : ℕ) : ENat) := window_isAP m k (by omega)
  have hbad := hSfree _ hWSc hap
  have hle1 : k ≤ 1 := by exact_mod_cast hbad
  omega

/-! ## §3 THE BLOCK INDUCTION: ⌊N/k⌋ blocks, one point lost each -/

/-- **The window-union bound.** For k ≥ 2, any k-AP-free Finset S with
S ⊆ [1, Q·k] satisfies |S| ≤ Q·(k − 1): induction on Q, one block peeled
per step, `window_bound` paying k − 1 each time. -/
theorem window_union_bound (k : ℕ) (hk : 2 ≤ k) :
    ∀ (Q : ℕ) (S : Finset ℕ), (↑S : Set ℕ).IsAPOfLengthFree ((k : ℕ) : ENat) →
      S ⊆ Finset.Icc 1 (Q * k) → S.card ≤ Q * (k - 1) := by
  intro Q
  induction Q with
  | zero =>
      intro S hfree hsub
      rw [Nat.zero_mul] at hsub ⊢
      have hcard0 : (Finset.Icc 1 0).card = 0 := by rw [Nat.card_Icc]
      have h0 : S.card ≤ (Finset.Icc 1 0).card := Finset.card_mono hsub
      omega
  | succ q ih =>
      intro S hfree hsub
      have hcover : S = (S ∩ Finset.Icc 1 (q * k)) ∪
          (S ∩ Finset.Icc (q * k + 1) (q * k + k)) := by
        ext x
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_Icc]
        constructor
        · intro hxS
          have hxI : x ∈ Finset.Icc 1 ((q + 1) * k) := hsub hxS
          simp only [Finset.mem_Icc] at hxI
          obtain ⟨h1, h2⟩ := hxI
          rw [Nat.add_mul, Nat.one_mul] at h2
          by_cases hxq : x ≤ q * k
          · left; exact ⟨hxS, ⟨h1, hxq⟩⟩
          · right; exact ⟨hxS, ⟨by omega, by omega⟩⟩
        · rintro (⟨hxS, -⟩ | ⟨hxS, -⟩)
          · exact hxS
          · exact hxS
      have hcu : S.card ≤ (S ∩ Finset.Icc 1 (q * k)).card +
          (S ∩ Finset.Icc (q * k + 1) (q * k + k)).card := by
        have hcardeq : S.card =
            ((S ∩ Finset.Icc 1 (q * k)) ∪
              (S ∩ Finset.Icc (q * k + 1) (q * k + k))).card :=
          congrArg Finset.card hcover
        rw [hcardeq]
        exact Finset.card_union_le _ _
      have hA : (S ∩ Finset.Icc 1 (q * k)).card ≤ q * (k - 1) :=
        ih (S ∩ Finset.Icc 1 (q * k)) (apFree_coe_inter_left S _ hfree)
          Finset.inter_subset_right
      have hB : (S ∩ Finset.Icc (q * k + 1) (q * k + k)).card ≤ k - 1 :=
        window_bound k (q * k) hk S hfree
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-! ## §4 THE CORE BOUND: assembly over blocks + tail -/

/-- **The core bound.** For k ≥ 2, N ≥ 1 implicit in hSsub: every
k-AP-free S ⊆ [1, N] satisfies |S| ≤ N − ⌊N/k⌋. The blocks [1, p]
(p = ⌊N/k⌋·k) pay q·(k−1) by §3; the tail (p, N] pays N − p; the
truncated-ℕ arithmetic spine: q·(k−1) = p − q and (p − q) + (N − p) =
N − q. -/
theorem core_bound (k N : ℕ) (hk : 2 ≤ k) (S : Finset ℕ)
    (hSsub : S ⊆ Finset.Icc 1 N)
    (hSfree : (↑S : Set ℕ).IsAPOfLengthFree ((k : ℕ) : ENat)) :
    S.card ≤ N - N / k := by
  obtain ⟨p, hp, hsum⟩ : ∃ p : ℕ, p = N / k * k ∧ p + N % k = N := by
    refine ⟨N / k * k, rfl, ?_⟩
    have h := Nat.div_add_mod N k
    rw [Nat.mul_comm (N / k) k]
    exact h
  have hqp : N / k ≤ p := by
    rw [hp]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hcover : S = (S ∩ Finset.Icc 1 p) ∪ (S ∩ Finset.Icc (p + 1) N) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_Icc]
    constructor
    · intro hxS
      have hxI : x ∈ Finset.Icc 1 N := hSsub hxS
      simp only [Finset.mem_Icc] at hxI
      obtain ⟨h1, h2⟩ := hxI
      by_cases hxp : x ≤ p
      · left; exact ⟨hxS, ⟨h1, hxp⟩⟩
      · right; exact ⟨hxS, ⟨by omega, by omega⟩⟩
    · rintro (⟨hxS, -⟩ | ⟨hxS, -⟩)
      · exact hxS
      · exact hxS
  have hcu : S.card ≤ (S ∩ Finset.Icc 1 p).card +
      (S ∩ Finset.Icc (p + 1) N).card := by
    have hcardeq : S.card =
        ((S ∩ Finset.Icc 1 p) ∪ (S ∩ Finset.Icc (p + 1) N)).card :=
      congrArg Finset.card hcover
    rw [hcardeq]
    exact Finset.card_union_le _ _
  have hA : (S ∩ Finset.Icc 1 p).card ≤ N / k * (k - 1) := by
    have hpe : Finset.Icc 1 p = Finset.Icc 1 (N / k * k) := by rw [hp]
    rw [hpe]
    exact window_union_bound k hk (N / k) _ (apFree_coe_inter_left S _ hSfree)
      Finset.inter_subset_right
  have hB : (S ∩ Finset.Icc (p + 1) N).card ≤ N - p := by
    refine le_trans (Finset.card_mono Finset.inter_subset_right) ?_
    rw [Nat.card_Icc]
    omega
  have hqk1 : N / k * (k - 1) = p - N / k := by
    have h1 := Nat.mul_sub (N / k) k 1
    rw [Nat.mul_one] at h1
    rw [h1, ← hp]
  have hple : p ≤ N := by omega
  omega

/-! ## §5 LAW U-GEN-0: the headline over the official r -/

/-- **LAW U-GEN-0 (the block floor law).** For every k ≥ 3 and N ≥ 1:
`r k N ≤ N − ⌊N/k⌋` over the official `Set.IsAPOfLengthFree.maxCard`.
Derived in WORKLOG_W80_142U.md event 3 (D3), engine-validated 56/56
(engine142uppergen.py, codes X/Y), now kernel'd. -/
theorem u_gen_zero (k N : ℕ) (hk : 3 ≤ k) (hN : 1 ≤ N) :
    r k N ≤ N - N / k := by
  simp only [Set.IsAPOfLengthFree.maxCard]
  refine csSup_le ⟨(1 : ℕ), ⟨({1} : Finset ℕ), ?_, ?_, rfl⟩⟩ ?_
  · intro z hz
    simp only [Finset.mem_singleton] at hz
    rw [hz]
    simp only [Finset.mem_Icc]
    omega
  · intro t hts ht
    have hcardt : ENat.card t = ((k : ℕ) : ENat) := ht.card
    have hsub : t ⊆ ({1} : Set ℕ) := by
      intro y hy
      have hy1 : y ∈ (↑({1} : Finset ℕ) : Set ℕ) := hts hy
      simp only [Finset.mem_coe, Finset.mem_singleton] at hy1
      rw [hy1]
      simp
    have hle : t.encard ≤ ({1} : Set ℕ).encard := Set.encard_le_encard hsub
    rw [Set.encard_singleton] at hle
    have hcardt' : t.encard = ((k : ℕ) : ENat) := hcardt
    have hbad : ((k : ℕ) : ENat) ≤ ((1 : ℕ) : ENat) := by
      rw [← hcardt']; exact hle
    have hfin : k ≤ 1 := by exact_mod_cast hbad
    omega
  · rintro n ⟨S, hSsub, hSfree, rfl⟩
    exact core_bound k N (by omega) S hSsub hSfree

/-! ## §6 TIGHTNESS AT N = k -/

/-- The lower witness at N = k: {1, …, k−1} is k-AP-free (a k-AP has
cardinality k — it cannot fit in a set of cardinality k − 1). -/
theorem r_kk_ge (k : ℕ) (hk : 3 ≤ k) : k - 1 ≤ r k k := by
  have hfree : (↑(Finset.Ico 1 k) : Set ℕ).IsAPOfLengthFree ((k : ℕ) : ENat) := by
    intro t hts ht
    have hcardt : ENat.card t = ((k : ℕ) : ENat) := ht.card
    have hle : t.encard ≤ (↑(Finset.Ico 1 k) : Set ℕ).encard :=
      Set.encard_le_encard hts
    rw [Set.encard_coe_eq_coe_finsetCard, Nat.card_Ico] at hle
    have hcardt' : t.encard = ((k : ℕ) : ENat) := hcardt
    have hbad : ((k : ℕ) : ENat) ≤ ((k - 1 : ℕ) : ENat) := by
      rw [← hcardt']; exact hle
    have hfin : k ≤ k - 1 := by exact_mod_cast hbad
    exact absurd hfin (by omega)
  have hsub : Finset.Ico 1 k ⊆ Finset.Icc 1 k := by
    intro x hx
    simp only [Finset.mem_Ico, Finset.mem_Icc] at hx ⊢
    omega
  have h1 : k - 1 = (Finset.Ico 1 k).card := (Nat.card_Ico 1 k).symm
  rw [h1]
  exact maxCard_ge_of_witness (Finset.Ico 1 k) hsub hfree

/-- **U-GEN-0 TIGHT AT N = k.** For k ≥ 3: `r k k = k − 1`. The ≤ side
is U-GEN-0 at N = k (with `k / k = 1` via the Arsenal block-count lemma
`mul_add_div_lemma`, CardinalWorlds.lean:143 — the genuine D3 division
bookkeeping); the ≥ side is the witness {1, …, k−1}. -/
theorem u_gen_zero_tight (k : ℕ) (hk : 3 ≤ k) : r k k = k - 1 := by
  apply le_antisymm
  · have hle := u_gen_zero k k hk (by omega)
    have hkk : k / k = 1 := by
      have h1 := mul_add_div_lemma 1 0 k (by omega)
      rw [Nat.mul_one, Nat.add_zero, Nat.zero_div, Nat.add_zero] at h1
      exact h1
    rw [hkk] at hle
    exact hle
  · exact r_kk_ge k hk

/-! ## §7 The board -/

theorem dm142c_board :
    (∀ k N : ℕ, 3 ≤ k → 1 ≤ N → r k N ≤ N - N / k) ∧
    (∀ k : ℕ, 3 ≤ k → r k k = k - 1) :=
  ⟨fun k N hk hN => u_gen_zero k N hk hN, fun k hk => u_gen_zero_tight k hk⟩

#print axioms DM142C.window_isAP
#print axioms DM142C.window_bound
#print axioms DM142C.window_union_bound
#print axioms DM142C.core_bound
#print axioms DM142C.u_gen_zero
#print axioms DM142C.r_kk_ge
#print axioms DM142C.u_gen_zero_tight
#print axioms DM142C.dm142c_board

#eval "DM142C_UGEN0_GREEN"

end DM142C
