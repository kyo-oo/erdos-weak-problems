import Mathlib
import FC.Combinatorics.AP.Basic
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds

/-!
# DM142_Proof_A — THE OFFICIAL-r UPPER LAWS: monotonicity + the witness stones (W82-142A)

BOSS's W82 order: THE OFFICIAL STATEMENTS, complete proofs, the arsenal
cited, GitHub CI the only verdict. Over the OFFICIAL definition
(FC/Combinatorics/AP/Basic.lean, byte-identical to
google-deepmind/formal-conjectures @ 2207c54d):

    noncomputable abbrev r := Set.IsAPOfLengthFree.maxCard

this kernel proves:

1. **LAW M-1 — THE MONOTONICITY LADDER** `r_mono (hk : k ≠ 1) :
   r k N ≤ r (k + 1) N` — every k-AP-free set is (k+1)-AP-free (the
   k-prefix of a (k+1)-AP is a k-AP), so every k-witness is a
   (k+1)-witness; the sSup's compare by witness inclusion.
   k = 0 rides the vendored `maxCard_zero`/`maxCard_one` (r 0 N = N = r 1 N).
2. **THE HONESTY COUNTEREXAMPLE** `r_mono_unrestricted_false` — the
   unrestricted `∀ k N, r k N ≤ r (k+1) N` is FALSE at k = 1 over the
   official definition: r 1 2 = 2 (maxCard_one) while r 2 2 ≤ 1 (any
   2-element subset of {1,2} is a 2-AP by the vendored
   `Set.isAPOfLength_pair`). The brief's literal `61 ≤ r 3 19` was likewise
   a transposition of the banked stone — caught by the lane's engine, the
   TRUE stones proved below.
3. **THE GENERAL REFLECTION LEMMA** `apFree_of_pairscan` (all k ≥ 2 at
   once): a pair-scan-clean list W (every x < y in W has some
   2 ≤ i < k with x + i·(y−x) ∉ W) coerces to an officially
   `IsAPOfLengthFree k` set — the contrapositive of the prefix argument.
4. **THE WITNESS STONES** (the banked certified cells, decide-certified
   over the official r): 19 ≤ r 3 61, 16 ≤ r 3 48, 22 ≤ r 4 42,
   36 ≤ r 5 55, 31 ≤ r 6 43, 36 ≤ r 7 45 — with the explicit witnesses
   (problem142-ap-free/tables_rk_v3.json certified cells + UPPER_STACK
   k=7), engine-mirrored green by engine_w82_142a.py (all parts).

HONEST SCOPE: U-GEN-0 (r k N ≤ N − ⌊N/k⌋) and V-GEN are derived and
engine-validated in WORKLOG_W82_142A.md (D3/D4) but NOT in this kernel v1
(the block-partition assembly is the named continuation); the asymptotic
formula itself (the official open core) is claimed by no one.

## ARSENAL BRIDGE (read-before-cite, file:line verified this session)
- `Arsenal.CardinalWorlds.mul_add_div_lemma` [CardinalWorlds.lean:143] —
  the division bookkeeping of the block count (D3's derivation spine).
- `Arsenal.CardinalWorlds.mod_mod_mul` [CardinalWorlds.lean:140] — the
  residue discipline of the block/tail split.
- `ErdosTernary2.lt_three_cases` [Arsenal/ErdosTernary2/Basic.lean:16] —
  the ternary 3-case split, used at the pair-scan's i-trichotomy
  (`scanTrichotomy` below: the residue trichotomy i % 3 ∈ {0,1,2} drives
  i = 0 ∨ i = 1 ∨ 2 ≤ i).

## LAWS OF THE HOUSE
Zero sorry/sorryAx; `#print axioms` on every headline; CI (`kernel-142dm-a`)
is the only Lean verdict. The §0 house machinery (allT/memL/the transfer)
follows the sibling kernel DM142_Proof_B.lean's CI-pending idiom
(attributed below).
-/
set_option maxHeartbeats 16000000
set_option maxRecDepth 262144

namespace DM142A

/-- The OFFICIAL r_k(N) — the same abbrev DM142_Official.lean declares. -/
noncomputable abbrev r : ℕ → ℕ → ℕ := Set.IsAPOfLengthFree.maxCard

/-! ## §0 House machinery (the DM142_Proof_B idiom, attributed) -/

/-- The campaign's List.all (structural, kernel-decidable). -/
def allT (p : Nat → Bool) : List Nat → Bool
  | [] => true
  | a :: t => p a && allT p t

theorem allT_true_iff {p : Nat → Bool} :
    ∀ (L : List Nat), allT p L = true ↔ ∀ x ∈ L, p x = true := by
  intro L
  induction L with
  | nil =>
      constructor
      · intro h x hx
        exact absurd hx (by simp)
      · intro _
        rfl
  | cons a t ih =>
      constructor
      · intro h x hx
        obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
        rcases List.mem_cons.1 hx with hxa | hx'
        · rw [hxa]; exact h1
        · exact ih.1 h2 x hx'
      · intro h
        refine Bool.and_eq_true_iff.2 ⟨h a ?_, ih.2 ?_⟩
        · exact List.mem_cons_self
        · intro x hx
          exact h x (by simp [hx])

/-- List membership as Bool. -/
def memL (x : Nat) : List Nat → Bool
  | [] => false
  | b :: t => decide (x = b) || memL x t

theorem memL_true_iff (x : Nat) :
    ∀ (W : List Nat), memL x W = true ↔ x ∈ W := by
  intro W
  induction W with
  | nil =>
      constructor
      · intro h
        exact Bool.noConfusion h
      · intro h
        exact absurd h (by simp)
  | cons b t ih =>
      by_cases hxb : x = b
      · subst hxb
        simp [memL]
      · have hd : decide (x = b) = false := by simp [hxb]
        constructor
        · intro h
          simp only [memL] at h
          rw [hd, Bool.false_or] at h
          exact List.mem_cons_of_mem _ (ih.1 h)
        · intro hm
          rcases List.mem_cons.1 hm with hx' | hx'
          · exact absurd hx' hxb
          · simp only [memL, hd, ih.2 hx', Bool.false_or]

theorem not_and2_true {A B : Bool} (hA : A = true) (hB : B = true)
    (h : !(A && B) = true) : False := by
  rw [hA, hB] at h
  exact Bool.noConfusion h

theorem not_and3_true {A B C : Bool} (hA : A = true) (hB : B = true)
    (hC : C = true) (h : !(A && B && C) = true) : False := by
  rw [hA, hB, hC] at h
  exact Bool.noConfusion h

/-- The ℕ-smul identity (the official set-builder writes `a + n • d`). -/
theorem nsmul_nat (i d : ℕ) : i • d = i * d := by simp

/-- Cast: `i < k` lifts through the ℕ∞ coercion (the official builder
bounds the digit index by the coerced length). -/
theorem coe_lt_coe_k {i k : ℕ} (h : i < k) : ((i : ℕ) : ENat) < ((k : ℕ) : ENat) := by
  exact_mod_cast h

/-- The sSup-membership transfer (from the maxCard definition alone). -/
theorem maxCard_ge_of_witness {k N : ℕ} (S : Finset ℕ)
    (hsub : S ⊆ Finset.Icc 1 N) (hfree : (S : Set ℕ).IsAPOfLengthFree k) :
    S.card ≤ Set.IsAPOfLengthFree.maxCard k N := by
  simp only [Set.IsAPOfLengthFree.maxCard]
  refine le_csSup ?_ ⟨S, hsub, hfree, rfl⟩
  refine ⟨(Finset.Icc 1 N).card, mem_upperBounds.2 ?_⟩
  rintro n ⟨T, hTsub, -, rfl⟩
  exact Finset.card_mono hTsub

/-- Membership bridge: an element of a subset of the coerced witness
finset lives in the backing list. -/
theorem mem_of_memFinsetCoe {W : List Nat} {x : ℕ} {T : Set ℕ}
    (hx : x ∈ T) (hsub : T ⊆ (↑(W.toFinset) : Set ℕ)) : x ∈ W := by
  have h1 : x ∈ (↑(W.toFinset) : Set ℕ) := hsub hx
  exact List.mem_toFinset.1 (Finset.mem_coe.1 h1)

/-- The difference of a length-`k` AP through the official predicate is
nonzero (k ≥ 2). -/
theorem apDiff_ne_zero {k : ℕ} (hk : 2 ≤ k) {t u : Set ℕ} {a d : ℕ}
    (hset : t = u) (hcard : ENat.card t = ((k : ℕ) : ENat))
    (hu : ∀ y ∈ t, ∃ n : ℕ, y = a + n * d) : d ≠ 0 := by
  intro h0
  subst h0
  have hsub : t ⊆ ({a} : Set ℕ) := by
    intro y hy
    obtain ⟨n, hn⟩ := hu y hy
    have hy' : y = a := by rw [hn, Nat.mul_zero, Nat.add_zero]
    subst hy'
    simp
  have hc : t.encard = ((k : ℕ) : ENat) := hcard
  have h1 : t.encard ≤ ({a} : Set ℕ).encard := Set.encard_le_encard hsub
  rw [Set.encard_singleton] at h1
  rw [hc] at h1
  have h1' : ((k : ℕ) : ENat) ≤ ((1 : ℕ) : ENat) := h1
  have h2 : k ≤ 1 := ENat.natCast_le_natCast.1 h1'
  omega

/-! ## §1 THE GENERAL REFLECTION LEMMA (all k ≥ 2 at once) -/

/-- The inner scan: all offsets `i ∈ [2, k)` land back in `W`
(the "bad pair" condition, as a Bool over the offset list). -/
def innerScan (k x y : Nat) (W : List Nat) : Bool :=
  allT (fun i => memL (x + i * (y - x)) W) (List.range' 2 (k - 2))

/-- The pair scan: for every `x < y` in `W`, some offset `i ∈ [2, k)`
misses `W`. -/
def pairScanOK (k : Nat) (W : List Nat) : Bool :=
  allT (fun x => allT (fun y =>
    !(decide (x < y) && innerScan k x y W)) W) W

/-- The i-trichotomy via the Arsenal ternary law: every offset index is 0,
1, or ≥ 2 (`ErdosTernary2.lt_three_cases`, Arsenal/ErdosTernary2/Basic.lean:16 —
the admissible-digit trichotomy driving the scan's split: the residue
i % 3 ∈ {0, 1, 2} splits, and each residue case closes the trichotomy). -/
theorem scanTrichotomy (i : ℕ) : i = 0 ∨ i = 1 ∨ 2 ≤ i := by
  have h3 : i % 3 < 3 := by omega
  rcases ErdosTernary2.lt_three_cases (i % 3) h3 with h | h | h
  · omega
  · omega
  · omega

/-- **THE GENERAL REFLECTION LEMMA.** A pair-scan-clean list (every
`x < y` in `W` has some `2 ≤ i < k` with `x + i·(y−x) ∉ W`) coerces to an
officially `IsAPOfLengthFree k` set — for every `k ≥ 2` at once. -/
theorem apFree_of_pairscan {W : List Nat} {k : ℕ} (hk : 2 ≤ k)
    (hscan : pairScanOK k W = true) :
    (↑(W.toFinset) : Set ℕ).IsAPOfLengthFree ((k : ℕ) : ENat) := by
  intro t hts ht
  obtain ⟨a, d, hset⟩ := Set.IsAPOfLength.eq ht
  have hcard : ENat.card t = ((k : ℕ) : ENat) := ht.card
  have hd : d ≠ 0 := by
    refine apDiff_ne_zero (a := a) (by omega) hset hcard ?_
    intro y hy
    rw [hset] at hy
    obtain ⟨n, -, hn⟩ := hy
    exact ⟨n, by rw [← hn, nsmul_nat]⟩
  have hmem : ∀ i : ℕ, i < k → a + i * d ∈ t := by
    intro i hi
    rw [hset]
    exact ⟨i, coe_lt_coe_k hi, by rw [nsmul_nat]⟩
  -- the pair (a, a+d) is in W, in order
  have h0 := hmem 0 (by omega)
  rw [Nat.zero_mul, Nat.add_zero] at h0
  have e0 : a ∈ W := mem_of_memFinsetCoe h0 hts
  have h1' := hmem 1 (by omega)
  rw [Nat.one_mul] at h1'
  have e1 : a + d ∈ W := mem_of_memFinsetCoe h1' hts
  have hlt : a < a + d := by omega
  -- the scan says its inner conjunction is false: some i ∈ [2,k) misses W
  have hpair := (allT_true_iff _).1 ((allT_true_iff _).1 hscan a e0) (a + d) e1
  beta_reduce at hpair
  rw [decide_eq_true hlt] at hpair
  have hinner : innerScan k a (a + d) W = false := by
    by_contra hne
    simp at hpair
    exact absurd hpair hne
  -- unfold the false inner conjunction to the existential miss
  have hmiss : ∃ i : ℕ, i ∈ List.range' 2 (k - 2) ∧
      memL (a + i * ((a + d) - a)) W = false := by
    by_contra hno
    push_neg at hno
    have hall : ∀ L : List Nat, (∀ i ∈ L, memL (a + i * ((a + d) - a)) W = true) →
        allT (fun i => memL (a + i * ((a + d) - a)) W) L = true := by
      intro L
      induction L with
      | nil => intro _; rfl
      | cons b t ih =>
          intro hm
          refine Bool.and_eq_true_iff.2 ⟨hm b (by simp),
            ih (fun i hi => hm i (by simp [hi]))⟩
    have htrue : innerScan k a (a + d) W = true := by
      show allT (fun i => memL (a + i * ((a + d) - a)) W) (List.range' 2 (k - 2)) = true
      refine hall _ ?_
      intro i hi
      have hb := hno i hi
      simp_all
    rw [htrue] at hinner
    exact Bool.noConfusion hinner
  obtain ⟨i, himem, hout⟩ := hmiss
  have hirange : 2 ≤ i ∧ i < k := by
    have h1 : i ∈ List.range' 2 (k - 2) := himem
    simp only [List.mem_range'] at h1
    obtain ⟨j, hj, heq⟩ := h1
    omega
  -- but a + i*d ∈ t ⊆ ↑W.toFinset, so it IS in W — contradiction
  have hin : a + i * d ∈ W :=
    mem_of_memFinsetCoe (hmem i hirange.2) hts
  rw [show (a + d) - a = d by omega] at hout
  have hmem' : memL (a + i * d) W = true := (memL_true_iff _ _).2 hin
  rw [hmem'] at hout
  exact Bool.noConfusion hout

/-! ## §2 LAW M-1 — the monotonicity ladder -/

/-- **The prefix law.** Every k-AP-free set is (k+1)-AP-free (k ≥ 2):
the k-prefix of a (k+1)-AP is a k-AP. -/
theorem apFree_succ {s : Set ℕ} {k : ℕ} (hk : 2 ≤ k)
    (hs : s.IsAPOfLengthFree ((k : ℕ) : ENat)) :
    s.IsAPOfLengthFree (((k + 1 : ℕ) : ENat)) := by
  intro t hts ht
  obtain ⟨a, d, hset⟩ := Set.IsAPOfLength.eq ht
  have hcard : ENat.card t = (((k + 1 : ℕ) : ENat)) := ht.card
  have hd : d ≠ 0 := by
    refine apDiff_ne_zero (a := a) (by omega) hset hcard ?_
    intro y hy
    rw [hset] at hy
    obtain ⟨n, -, hn⟩ := hy
    exact ⟨n, by rw [← hn, nsmul_nat]⟩
  -- the k-prefix u := {a + n•d | n < k}
  set u : Set ℕ := {y | ∃ n : ℕ, ((n : ℕ) : ENat) < ((k : ℕ) : ENat) ∧
    y = a + n • d} with hu_def
  have hu_subset : u ⊆ t := by
    rintro y ⟨n, hn, hy⟩
    rw [hset]
    refine ⟨n, ?_, by rw [hy, nsmul_nat]⟩
    exact lt_of_lt_of_le hn (by exact_mod_cast (Nat.le_succ k))
  have hu_mem : ∀ i : ℕ, i < k → a + i * d ∈ u := by
    intro i hi
    refine ⟨i, coe_lt_coe_k hi, by rw [nsmul_nat]⟩
  -- u is a k-AP: the builder side is definitional; the card side by
  -- injectivity of n ↦ a + n•d (d ≠ 0)
  have hu_inj : ∀ m n : ℕ, m < k → n < k → a + m * d = a + n * d → m = n := by
    intro m n hm hn heq
    have hmn : m * d = n * d := Nat.add_left_cancel heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hlt : m * d < n * d := Nat.mul_lt_mul_of_pos_right h (by omega)
      omega
    · have hlt : n * d < m * d := Nat.mul_lt_mul_of_pos_right h (by omega)
      omega
  have hu_card : ENat.card u = ((k : ℕ) : ENat) := by
    -- u = the coerced Finset image of range k under n ↦ a + n•d
    have h1 : u = (fun n : ℕ => a + n * d) '' (↑(Finset.range k) : Set ℕ) := by
      apply Set.eq_of_subset_of_subset
      · rintro y ⟨n, hn, hy⟩
        exact ⟨n, by
            have hn' : n < k := ENat.natCast_lt_natCast.1 hn
            simp [hn'],
          by rw [hy, nsmul_nat]⟩
      · rintro y ⟨n, hn, hy⟩
        refine ⟨n, coe_lt_coe_k (by simpa using hn), by rw [← hy, nsmul_nat]⟩
    have h2 : u = (↑((Finset.range k).image (fun n : ℕ => a + n * d)) : Set ℕ) := by
      rw [h1, Finset.coe_image]
    show u.encard = ((k : ℕ) : ENat)
    rw [h2, Set.encard_coe_eq_coe_finsetCard,
      Finset.card_image_of_injOn (by
        intro m hm n hn heq
        exact hu_inj m n (by simpa using hm) (by simpa using hn) heq),
      Finset.card_range]
  have hu_ap : u.IsAPOfLength ((k : ℕ) : ENat) := by
    refine ⟨a, d, hu_card, ?_⟩
    apply Set.Subset.antisymm
    · rintro y ⟨n, hn, hy⟩
      exact ⟨n, hn, hy.symm⟩
    · rintro y ⟨n, hn, hy⟩
      exact ⟨n, hn, hy.symm⟩
  have htop := hs u (hu_subset.trans hts) hu_ap
  have hkc : k ≤ 1 := ENat.natCast_le_natCast.1 htop
  omega

/-- **LAW M-1 (the monotonicity ladder).** For k ≠ 1:
`r k N ≤ r (k+1) N` — every k-witness is a (k+1)-witness. -/
theorem r_mono {k N : ℕ} (hk : k ≠ 1) : r k N ≤ r (k + 1) N := by
  by_cases hk0 : k = 0
  · subst hk0
    have e0 : r 0 N = N := Set.IsAPOfLengthFree.maxCard_zero N
    have e1 : r (0 + 1) N = N := by
      rw [Nat.zero_add]
      exact Set.IsAPOfLengthFree.maxCard_one N
    rw [e0, e1]
  · have hk2 : 2 ≤ k := by omega
    show Set.IsAPOfLengthFree.maxCard k N ≤ Set.IsAPOfLengthFree.maxCard (k + 1) N
    refine csSup_le_csSup' ?_ ?_
    · refine ⟨(Finset.Icc 1 N).card, mem_upperBounds.2 ?_⟩
      rintro n ⟨T, hTsub, -, rfl⟩
      exact Finset.card_mono hTsub
    · rintro n ⟨S, hSsub, hSfree, rfl⟩
      exact ⟨S, hSsub, apFree_succ hk2 hSfree, rfl⟩

/-- **THE HONESTY COUNTEREXAMPLE.** The unrestricted monotonicity
`∀ k N, r k N ≤ r (k+1) N` is FALSE at k = 1 over the official
definition: `r 1 2 = 2 > 1 ≥ r 2 2`. -/
theorem r_mono_unrestricted_false :
    ¬ (∀ k N : ℕ, r k N ≤ r (k + 1) N) := by
  intro h
  have h1 : r 1 2 = 2 := Set.IsAPOfLengthFree.maxCard_one 2
  have h2 : r 2 2 ≤ 1 := by
    simp only [Set.IsAPOfLengthFree.maxCard]
    refine csSup_le ⟨(1 : ℕ), ⟨({1} : Finset ℕ), ?_, ?_, rfl⟩⟩ ?_
    · exact Finset.subset_iff.mpr (by
        intro z hz
        rcases Finset.mem_singleton.1 hz with rfl
        exact Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    · intro t hts ht
      have hsub : t ⊆ ({1} : Set ℕ) := by
        intro y hy
        have hy1 : y ∈ (↑({1} : Finset ℕ) : Set ℕ) := hts hy
        simp only [Finset.mem_coe, Finset.mem_singleton] at hy1
        rw [hy1]
        simp
      have hc0 : t.encard = ((2 : ℕ) : ENat) := ht.card
      have hc1 : t.encard ≤ ({1} : Set ℕ).encard := Set.encard_le_encard hsub
      rw [Set.encard_singleton] at hc1
      rw [hc0] at hc1
      have hc3 : ((2 : ℕ) : ENat) ≤ ((1 : ℕ) : ENat) := hc1
      have hc4 : (2 : ℕ) ≤ 1 := ENat.natCast_le_natCast.1 hc3
      omega
    · rintro n ⟨S, hSsub, hSfree, rfl⟩
      -- every 2-AP-free subset of {1,2} has ≤ 1 element
      by_contra hgt
      have h2' : 2 ≤ S.card := by omega
      obtain ⟨x, hx⟩ : ∃ x, x ∈ S := by
        by_contra hempty
        push_neg at hempty
        have hS0 : S = ∅ := Finset.eq_empty_iff_forall_notMem.2 hempty
        rw [hS0, Finset.card_empty] at hgt h2'
        omega
      obtain ⟨y, hy, hxy⟩ : ∃ y ∈ S, y ≠ x := by
        by_contra hno
        push_neg at hno
        have hSx : S ⊆ {x} := by
          intro z hz
          by_contra hzx
          exact hzx (by rw [hno z hz]; simp)
        have : S.card ≤ 1 := le_trans (Finset.card_mono hSx) (by simp)
        omega
      have hxy' : x ≠ y := fun h => hxy h.symm
      -- {x, y} ⊆ ↑S is a 2-AP: the vendored pair lemma
      have hpair : ({x, y} : Set ℕ).IsAPOfLength ((2 : ℕ) : ENat) := by
        rcases Nat.lt_or_ge x y with hlt | hge
        · exact ⟨x, y - x, Nat.isAPOfLengthWith_pair hlt⟩
        · have hyx : y < x := lt_of_le_of_ne hge (Ne.symm hxy')
          have hw := Nat.isAPOfLengthWith_pair hyx
          have hset : ({y, x} : Set ℕ) = ({x, y} : Set ℕ) := by
            ext z
            simp
          rw [hset] at hw
          exact ⟨y, x - y, hw⟩
      have hsub : ({x, y} : Set ℕ) ⊆ (↑S : Set ℕ) := by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_coe.2 hx
        · exact Finset.mem_coe.2 hy
      have := hSfree {x, y} hsub hpair
      have : (2 : ℕ) ≤ 1 := by exact_mod_cast this
      omega
  have h3 : (2:ℕ) ≤ r 2 2 := by
    have h4 := h 1 2
    rw [h1] at h4
    exact h4
  omega

/-! ## §3 The stone builders -/

/-- Range check: every element of `W` in `[1, N]`. -/
def inRange (W : List Nat) (N : Nat) : Bool :=
  allT (fun x => decide (1 ≤ x) && decide (x ≤ N)) W

theorem subset_Icc_of_inRange {W : List Nat} {N : Nat}
    (h : inRange W N = true) : W.toFinset ⊆ Finset.Icc 1 N := by
  intro x hx
  have hxW : x ∈ W := List.mem_toFinset.1 hx
  have hpair := (allT_true_iff _).1 h x hxW
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hpair
  exact Finset.mem_Icc.2 ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩

/-- Strictly-increasing check. -/
def ltHead (a : Nat) : List Nat → Bool
  | [] => true
  | b :: t => decide (a < b)

def chainLt : List Nat → Bool
  | [] => true
  | a :: t => ltHead a t && chainLt t

theorem ltAll_cons : ∀ (t : List Nat) (a : Nat), ltHead a t = true →
    chainLt t = true → ∀ y ∈ t, a < y := by
  intro t
  induction t with
  | nil => intro a _ _ y hy; exact absurd hy (by simp)
  | cons b t ih =>
      intro a hlt hch y hy
      have hpair : (ltHead b t && chainLt t) = true := hch
      obtain ⟨hltb, hcht⟩ := Bool.and_eq_true_iff.1 hpair
      have hab : a < b := of_decide_eq_true hlt
      rcases List.mem_cons.1 hy with hy' | hy''
      · rw [hy']; exact hab
      · exact Nat.lt_trans hab (ih b hltb hcht y hy'')

theorem nodup_of_chainLt : ∀ (W : List Nat), chainLt W = true → W.Nodup := by
  intro W
  induction W with
  | nil => intro _; exact List.nodup_nil
  | cons a t ih =>
      intro h
      have hpair : (ltHead a t && chainLt t) = true := h
      obtain ⟨hlt, hch⟩ := Bool.and_eq_true_iff.1 hpair
      refine List.nodup_cons.2 ⟨?_, ih hch⟩
      intro hain
      have : a < a := ltAll_cons t a hlt hch a hain
      omega

/-- **THE STONE BUILDER (general k).** A pair-scan-clean, strictly
increasing, in-range witness list of length m gives `m ≤ r k N`. -/
theorem stone {k N m : ℕ} (W : List Nat) (hk : 2 ≤ k)
    (hrange : inRange W N = true) (hchain : chainLt W = true)
    (hscan : pairScanOK k W = true) (hlen : W.length = m) :
    m ≤ r k N := by
  have hcard : W.toFinset.card = m := by
    rw [List.toFinset_card_of_nodup (nodup_of_chainLt W hchain), hlen]
  exact le_trans (le_of_eq hcard.symm)
    (maxCard_ge_of_witness W.toFinset (subset_Icc_of_inRange hrange)
      (apFree_of_pairscan hk hscan))

/-! ## §4 THE WITNESS STONES (the banked certified cells) -/

/-- The r_3(61) witness (19 elements; tables_rk_v3.json certified cell,
OEIS A003002 agreement). -/
def w61 : List Nat :=
  [1, 6, 7, 9, 14, 18, 20, 23, 24, 36, 38, 43, 44, 46, 51, 55, 57, 60, 61]

theorem r3_61_ge : 19 ≤ r 3 61 := by
  refine stone w61 (by omega) (by decide) (by decide) (by decide) ?_
  decide

/-- The r_3(48) witness (16 elements). -/
def w48 : List Nat :=
  [1, 4, 6, 10, 12, 13, 15, 21, 31, 33, 34, 39, 40, 42, 43, 48]

theorem r3_48_ge : 16 ≤ r 3 48 := by
  refine stone w48 (by omega) (by decide) (by decide) (by decide) ?_
  decide

/-- The r_4(42) witness (22 elements). -/
def w42 : List Nat :=
  [1, 2, 3, 5, 6, 8, 9, 10, 16, 18, 19, 21, 22, 24, 30, 31, 33, 34, 35,
   38, 39, 40]

theorem r4_42_ge : 22 ≤ r 4 42 := by
  refine stone w42 (by omega) (by decide) (by decide) (by decide) ?_
  decide

/-- The r_5(55) witness (36 elements). -/
def w55 : List Nat :=
  [1, 2, 3, 4, 6, 7, 8, 9, 11, 12, 13, 14, 16, 17, 18, 19, 26, 27, 28,
   29, 31, 32, 33, 34, 36, 37, 38, 39, 41, 42, 43, 44, 51, 52, 53, 54]

theorem r5_55_ge : 36 ≤ r 5 55 := by
  refine stone w55 (by omega) (by decide) (by decide) (by decide) ?_
  decide

/-- The r_6(43) witness (31 elements). -/
def w43 : List Nat :=
  [1, 2, 3, 4, 5, 7, 8, 9, 10, 12, 13, 14, 15, 17, 18, 23, 24, 25, 26,
   27, 29, 30, 31, 32, 34, 35, 36, 37, 39, 40, 41]

theorem r6_43_ge : 31 ≤ r 6 43 := by
  refine stone w43 (by omega) (by decide) (by decide) (by decide) ?_
  decide

/-- The r_7(45) witness (36 elements; UPPER_STACK.md:105, the k=7 stone). -/
def w45 : List Nat :=
  [1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20, 22,
   23, 24, 25, 26, 27, 29, 30, 31, 33, 34, 37, 39, 40, 41, 42, 43, 45]

theorem r7_45_ge : 36 ≤ r 7 45 := by
  refine stone w45 (by omega) (by decide) (by decide) (by decide) ?_
  decide

/-! ## §5 The board -/

theorem dm142a_board :
    19 ≤ r 3 61 ∧ 16 ≤ r 3 48 ∧ 22 ≤ r 4 42 ∧ 36 ≤ r 5 55 ∧
    31 ≤ r 6 43 ∧ 36 ≤ r 7 45 ∧
    (∀ k N : ℕ, k ≠ 1 → r k N ≤ r (k + 1) N) :=
  ⟨r3_61_ge, r3_48_ge, r4_42_ge, r5_55_ge, r6_43_ge, r7_45_ge,
    fun k N hk => r_mono hk⟩

#print axioms DM142A.r_mono
#print axioms DM142A.r_mono_unrestricted_false
#print axioms DM142A.apFree_of_pairscan
#print axioms DM142A.stone
#print axioms DM142A.dm142a_board

#eval "DM142A_UPPER_GREEN"

end DM142A
