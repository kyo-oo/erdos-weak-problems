import Mathlib
import FC.Combinatorics.AP.Basic
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds

/-!
# DM142 PROOF B — THE LOWER-STONE KERNEL over the OFFICIAL r_k(N) (W82-142B)

Erdős Problem #142, official statement (erdosproblems.com/142, prize $10000;
vendored verbatim in `DM142_Official.lean` from
google-deepmind/formal-conjectures @ 2207c54d):

> Let $r_k(N)$ be the largest possible size of a subset of $\{1,\ldots,N\}$
> that does not contain any non-trivial $k$-term arithmetic progression.
> Prove an asymptotic formula for $r_k(N)$.

THE OFFICIAL r (verbatim, `FC/Combinatorics/AP/Basic.lean:223`):
`Set.IsAPOfLengthFree.maxCard (k N : ℕ) : ℕ :=
  sSup {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N) (_ : (S : Set ℕ).IsAPOfLengthFree k}`.
This kernel's `r` is that definition (an abbrev, exactly as
`DM142_Official.lean` declares `Erdos142.r`); every stone below is a theorem
about the official object.

## WHAT THIS KERNEL PROVES (all complete, zero sorry, decide-certified)

1. **THE sSup-MEMBERSHIP TRANSFER** `maxCard_ge_of_witness`: any Finset `S`
   with `S ⊆ Finset.Icc 1 N`, `(↑S : Set ℕ).IsAPOfLengthFree k` and
   `S.card = m` yields `m ≤ maxCard k N` — derived from the maxCard
   definition alone (le_csSup + the card bound `Finset.card_mono`).

2. **THE OFFICIAL-DEF BRIDGES** (from the FC file's own lemmas
   `Set.IsAPOfLength.eq` / `Set.IsAPOfLength.card`, FC/Combinatorics/AP/
   Basic.lean:143-146 — zero Mathlib name risk on the unpacking):
   `isAPOfLengthFree_three/four/five` reduce `IsAPOfLengthFree` over the
   official definition to three/four/five-term AP-freeness scans.

3. **THE BEHREND-FIBER STONES** — the banked witness ladder of
   `receipts142b_audit.txt` (B2: all PASS, dual scanners + negative
   controls), now decide-certified over the official r:
   the ten k=3 fibers 6 ≤ r 3 216, 12 ≤ r 3 1296, 30 ≤ r 3 7776,
   90 ≤ r 3 46656, 6 ≤ r 3 1000, 24 ≤ r 3 10000, 12 ≤ r 3 2744,
   48 ≤ r 3 38416, 2 ≤ r 3 324, 10 ≤ r 3 1024 (the layer×sphere fibers of
   BEHREND_PROOF.md / BEHREND_GEN.md at base B = 2m, digit vectors in
   [0,m)^d keyed by (digit-sum, digit-square-sum)), plus the k=4 and k=5
   ladders on the decide-budget fibers (B2-LADDER receipts: the same fibers
   are 4-AP- and 5-AP-free).

4. **THE ARSENAL BRIDGE** (BOSS's law): the base-4 digit reader
   `noQuatTwoS` (structural twin of the Arsenal Cantor reader
   `noTernaryTwo`, Arsenal/CardinalWorlds.lean:41, whose decide-compatible
   structural form is `noTernaryTwoStruct`, Arsenal/CardinalWorlds.lean:51,
   with the equivalence law `noTernaryTwo_eq_struct`,
   Arsenal/CardinalWorlds.lean:58 — all read before cite): the m=2 fiber
   w1024 is base-4 {0,1}-digit-clean (decide), and it is DISJOINT from the
   Arsenal Cantor family (decide, via the Arsenal reader itself). The
   ternary digit trichotomy is driven by
   `ErdosTernary2.lt_three_cases` (Arsenal/ErdosTernary2/Basic.lean:16,
   read before cite) in `ternary_cantor_digit01`.

HONEST SCOPE: these are explicit finite lower bounds (witness stones) over
the official r_k(N) — the exact small-N anchors of the banked all-k
Behrend-gen asymptotic envelope (r_k(N) ≥ N·exp(−C_k√(ln N)),
C_k = 2√((k+1)ln 2)+1, in-package BEHREND_GEN.md W79-142E). The asymptotic
formula itself (the official open core) is NOT claimed — see
OFFICIAL_POSITION_W82.md for the complete two-sided ledger.

Witness data + every Bool scan mirrored and pre-verified in python by
`engine142b_stones_mirror.py` (27/27 green, negative controls included) —
no `by decide` below reaches CI unverified.
-/

set_option maxHeartbeats 16000000
set_option maxRecDepth 262144

namespace DM142B

/-- The OFFICIAL r_k(N) — verbatim the definition
`Set.IsAPOfLengthFree.maxCard` (FC/Combinatorics/AP/Basic.lean:223), the
same abbrev `DM142_Official.lean` declares as `Erdos142.r`. -/
noncomputable abbrev r : ℕ → ℕ → ℕ := Set.IsAPOfLengthFree.maxCard

/-! ## §0 House Bool machinery (the green-kernel idiom: zero core-name
dependence in the scanners; S060/Erdos142.lean pattern) -/

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
        · exact h a (by simp)
        · intro x hx
          exact h x (by simp [hx])

/-- List membership as Bool (house; extraction lemma below). -/
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
        constructor
        · intro _
          exact Or.inl rfl
        · intro _
          have h2 : (decide (b = b) || memL b t) = true := by
            rw [decide_eq_true rfl]
          exact h2
      · constructor
        · intro h
          have hd : decide (x = b) = false := by simp [hxb]
          have h2 : (decide (x = b) || memL x t) = true := h
          rw [hd] at h2
          refine Or.inr (ih.1 h2)
        · intro hm
          have hd : decide (x = b) = false := by simp [hxb]
          rcases List.mem_cons.1 hm with hxb' | hx'
          · exact absurd hxb' hxb
          · have h2 : (decide (x = b) || memL x t) = true := by
              rw [hd, ih.2 hx']
            exact h2

/-- `true && x = true`-style conjunction eliminator (three conjuncts). -/
theorem not_and3_true {A B C : Bool} (hA : A = true) (hB : B = true)
    (hC : C = true) (h : !(A && B && C) = true) : False := by
  rw [hA, hB, hC] at h
  exact Bool.noConfusion h

/-- Four conjuncts. -/
theorem not_and4_true {A B C D : Bool} (hA : A = true) (hB : B = true)
    (hC : C = true) (hD : D = true) (h : !(A && B && C && D) = true) : False := by
  rw [hA, hB, hC, hD] at h
  exact Bool.noConfusion h

/-- The ℕ-smul identity (one house name over the smul lemma; the official
def's set-builder writes `a + n • d` for ℕ acting on ℕ). -/
theorem nsmul_nat (i d : ℕ) : i • d = i * d := by simp

/-- Cast: `i < k` lifts to `(i : ℕ∞) < (k : ℕ∞)` (the official set-builder
bounds the digit index by the coerced length). -/
theorem coe_lt_coe_k {i k : ℕ} (h : i < k) : ((i : ℕ) : ENat) < ((k : ℕ) : ENat) :=
  ENat.natCast_lt_natCast.2 h

/-! ## §1 The sSup-membership transfer (from the maxCard definition) -/

/-- **THE TRANSFER.** A Finset witness `S ⊆ Finset.Icc 1 N` that is
`IsAPOfLengthFree k` (the official predicate) provides the lower bound
`S.card ≤ maxCard k N`: `S.card` is a member of the sSup'd set in the
definition of `Set.IsAPOfLengthFree.maxCard`
(FC/Combinatorics/AP/Basic.lean:223), and that set is bounded above by
`(Finset.Icc 1 N).card` (`Finset.card_mono`). -/
theorem maxCard_ge_of_witness {k N : ℕ} (S : Finset ℕ)
    (hsub : S ⊆ Finset.Icc 1 N) (hfree : (S : Set ℕ).IsAPOfLengthFree k) :
    S.card ≤ Set.IsAPOfLengthFree.maxCard k N := by
  simp only [Set.IsAPOfLengthFree.maxCard]
  refine le_csSup ?_ ⟨S, hsub, hfree, rfl⟩
  refine ⟨(Finset.Icc 1 N).card, mem_upperBounds.2 ?_⟩
  rintro n ⟨T, hTsub, -, rfl⟩
  exact Finset.card_mono hTsub

/-! ## §2 The scan checkers (Bool, kernel-decidable) -/

/-- k=3 scan: no pair `x < z` in `W` with `x + z` even and midpoint
`(x + z) / 2` back in `W` (a 3-AP `a, a+d, a+2d` is exactly such a pair
with `x = a`, `z = a + 2d`). -/
def midFree3 (W : List Nat) : Bool :=
  allT (fun x => allT (fun z =>
    !(decide (x < z) && decide ((x + z) % 2 = 0) && memL ((x + z) / 2) W)) W) W

/-- k=4 scan: no quadruple with the two consecutive-midpoint equations and
distinct endpoints. -/
def k4Free (W : List Nat) : Bool :=
  allT (fun w => allT (fun x => allT (fun y => allT (fun z =>
    !(decide (2 * x = w + y) && decide (2 * y = x + z) && decide (w ≠ z))
      W) W) W) W

/-- k=5 scan: no quintuple with the three consecutive-midpoint equations
and distinct endpoints. -/
def k5Free (W : List Nat) : Bool :=
  allT (fun u => allT (fun p => allT (fun q => allT (fun v => allT (fun s =>
    !(decide (2 * p = u + q) && decide (2 * q = p + v) &&
      decide (2 * v = q + s) && decide (u ≠ s)) W) W) W) W) W

/-! ## §3 The official-def bridges -/

/-- The difference of a length-`k` AP through the official predicate is
nonzero (k ≥ 2): with `d = 0` every element of the progression set equals
`a`, so its cardinality is ≤ 1 < k. The progression's shape is taken from
the FC file's own `Set.IsAPOfLength.eq` (FC/Combinatorics/AP/Basic.lean:145),
abstracted over the set to keep the bridge cast-clean. -/
theorem apDiff_ne_zero {k : ℕ} (hk : 2 ≤ k) {t : Set ℕ} {a d : ℕ} {u : Set ℕ}
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

/-- Membership bridge: an element of a subset `T` of the coerced witness
finset lives in the backing list. -/
theorem mem_of_memFinsetCoe {W : List Nat} {x : ℕ} {T : Set ℕ}
    (hx : x ∈ T) (hsub : T ⊆ (↑(W.toFinset) : Set ℕ)) : x ∈ W := by
  have h1 : x ∈ (↑(W.toFinset) : Set ℕ) := hsub hx
  exact List.mem_toFinset.1 (Finset.mem_coe.1 h1)

/-- **THE k=3 BRIDGE.** If the midpoint scan over the list `W` is clean
(no `x < z` in `W` with `x + z` even and the midpoint back in `W`), then
the coerced finset is `IsAPOfLengthFree 3` over the official definition. -/
theorem isAPOfLengthFree_three {W : List Nat} (hmid : midFree3 W = true) :
    (↑(W.toFinset) : Set ℕ).IsAPOfLengthFree ((3 : ℕ) : ENat) := by
  intro t hts ht
  obtain ⟨a, d, hset⟩ := Set.IsAPOfLength.eq ht
  have hcard : ENat.card t = ((3 : ℕ) : ENat) := ht.card
  have hd : d ≠ 0 := by
    refine apDiff_ne_zero (by omega) hset hcard ?_
    intro y hy
    rw [hset] at hy
    obtain ⟨n, -, hn⟩ := hy
    exact ⟨n, by rw [hn, nsmul_nat]⟩
  have hmem : ∀ i : ℕ, i < 3 → a + i * d ∈ t := by
    intro i hi
    rw [hset]
    exact ⟨i, coe_lt_coe_k hi, by rw [nsmul_nat]⟩
  have e0 : a ∈ W := mem_of_memFinsetCoe (hmem 0 (by omega)) hts
  have e1 : a + d ∈ W := mem_of_memFinsetCoe (hmem 1 (by omega)) hts
  have e2 : a + 2 * d ∈ W := mem_of_memFinsetCoe (hmem 2 (by omega)) hts
  have hscan : ∀ x z m : ℕ, x ∈ W → z ∈ W → x < z → (x + z) % 2 = 0 →
      (x + z) / 2 = m → m ∈ W → False := by
    intro x z m hx hz hlt heven hdiv hm
    have hx' := allT_true_iff.1 hmid x hx
    have hz' := allT_true_iff.1 hx' z hz
    refine not_and3_true (decide_eq_true hlt) (decide_eq_true heven) ?_ hz'
    rw [hdiv]
    exact memL_true_iff _ _ |>.2 hm
  exact (hscan a (a + 2 * d) (a + d) e0 e2 (by omega) (by omega) (by omega) e1).elim

/-- **THE k=4 BRIDGE.** No quadruple `w x y z ∈ W` with `2x = w + y`,
`2y = x + z`, `w ≠ z` (the two-consecutive-midpoints form: a 4-AP
`a, a+d, a+2d, a+3d` is exactly such a quadruple) ⇒ the official
`IsAPOfLengthFree 4`. -/
theorem isAPOfLengthFree_four {W : List Nat} (h4 : k4Free W = true) :
    (↑(W.toFinset) : Set ℕ).IsAPOfLengthFree ((4 : ℕ) : ENat) := by
  intro t hts ht
  obtain ⟨a, d, hset⟩ := Set.IsAPOfLength.eq ht
  have hcard : ENat.card t = ((4 : ℕ) : ENat) := ht.card
  have hd : d ≠ 0 := by
    refine apDiff_ne_zero (by omega) hset hcard ?_
    intro y hy
    rw [hset] at hy
    obtain ⟨n, -, hn⟩ := hy
    exact ⟨n, by rw [hn, nsmul_nat]⟩
  have hmem : ∀ i : ℕ, i < 4 → a + i * d ∈ t := by
    intro i hi
    rw [hset]
    exact ⟨i, coe_lt_coe_k hi, by rw [nsmul_nat]⟩
  have e0 : a ∈ W := mem_of_memFinsetCoe (hmem 0 (by omega)) hts
  have e1 : a + d ∈ W := mem_of_memFinsetCoe (hmem 1 (by omega)) hts
  have e2 : a + 2 * d ∈ W := mem_of_memFinsetCoe (hmem 2 (by omega)) hts
  have e3 : a + 3 * d ∈ W := mem_of_memFinsetCoe (hmem 3 (by omega)) hts
  have hscan : ∀ w x y z : ℕ, w ∈ W → x ∈ W → y ∈ W → z ∈ W →
      2 * x = w + y → 2 * y = x + z → w ≠ z → False := by
    intro w x y z hw hx hy hz h1 h2 hne
    have hw' := allT_true_iff.1 h4 w hw
    have hx' := allT_true_iff.1 hw' x hx
    have hy' := allT_true_iff.1 hx' y hy
    have hz' := allT_true_iff.1 hy' z hz
    exact not_and3_true (decide_eq_true h1) (decide_eq_true h2)
      (decide_eq_true hne) hz'
  exact (hscan a (a + d) (a + 2 * d) (a + 3 * d) e0 e1 e2 e3
    (by omega) (by omega) (by omega)).elim

/-- **THE k=5 BRIDGE.** No quintuple `u p q r s ∈ W` with the three
consecutive-midpoint equations and `u ≠ s` ⇒ the official
`IsAPOfLengthFree 5`. -/
theorem isAPOfLengthFree_five {W : List Nat} (h5 : k5Free W = true) :
    (↑(W.toFinset) : Set ℕ).IsAPOfLengthFree ((5 : ℕ) : ENat) := by
  intro t hts ht
  obtain ⟨a, d, hset⟩ := Set.IsAPOfLength.eq ht
  have hcard : ENat.card t = ((5 : ℕ) : ENat) := ht.card
  have hd : d ≠ 0 := by
    refine apDiff_ne_zero (by omega) hset hcard ?_
    intro y hy
    rw [hset] at hy
    obtain ⟨n, -, hn⟩ := hy
    exact ⟨n, by rw [hn, nsmul_nat]⟩
  have hmem : ∀ i : ℕ, i < 5 → a + i * d ∈ t := by
    intro i hi
    rw [hset]
    exact ⟨i, coe_lt_coe_k hi, by rw [nsmul_nat]⟩
  have e0 : a ∈ W := mem_of_memFinsetCoe (hmem 0 (by omega)) hts
  have e1 : a + d ∈ W := mem_of_memFinsetCoe (hmem 1 (by omega)) hts
  have e2 : a + 2 * d ∈ W := mem_of_memFinsetCoe (hmem 2 (by omega)) hts
  have e3 : a + 3 * d ∈ W := mem_of_memFinsetCoe (hmem 3 (by omega)) hts
  have e4 : a + 4 * d ∈ W := mem_of_memFinsetCoe (hmem 4 (by omega)) hts
  have hscan : ∀ u p q v s : ℕ, u ∈ W → p ∈ W → q ∈ W → v ∈ W → s ∈ W →
      2 * p = u + q → 2 * q = p + v → 2 * v = q + s → u ≠ s → False := by
    intro u p q v s hu hp hq hv hs h1 h2 h3 hne
    have hu' := allT_true_iff.1 h5 u hu
    have hp' := allT_true_iff.1 hu' p hp
    have hq' := allT_true_iff.1 hp' q hq
    have hv' := allT_true_iff.1 hq' v hv
    have hs' := allT_true_iff.1 hv' s hs
    exact not_and4_true (decide_eq_true h1) (decide_eq_true h2)
      (decide_eq_true h3) (decide_eq_true hne) hs'
  exact (hscan a (a + d) (a + 2 * d) (a + 3 * d) (a + 4 * d) e0 e1 e2 e3 e4
    (by omega) (by omega) (by omega) (by omega)).elim

/-! ## §4 Range, monotone-chain and Nodup machinery -/

/-- Range check: every element of `W` in `[1, N]`. -/
def inRange (W : List Nat) (N : Nat) : Bool :=
  allT (fun x => decide (1 ≤ x) && decide (x ≤ N)) W

theorem subset_Icc_of_inRange {W : List Nat} {N : Nat}
    (h : inRange W N = true) : W.toFinset ⊆ Finset.Icc 1 N := by
  intro x hx
  have hxW : x ∈ W := List.mem_toFinset.1 hx
  have hpair := allT_true_iff.1 h x hxW
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hpair
  exact Finset.mem_Icc.2 ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩

/-- Strictly-increasing check (first component of the Nodup derivation). -/
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

/-! ## §5 The stone builders -/

theorem stone3 {N m : ℕ} (W : List Nat)
    (hrange : inRange W N = true) (hchain : chainLt W = true)
    (hmid : midFree3 W = true) (hlen : W.length = m) :
    m ≤ Set.IsAPOfLengthFree.maxCard 3 N := by
  have h := maxCard_ge_of_witness W.toFinset (subset_Icc_of_inRange hrange)
    (isAPOfLengthFree_three hmid)
  rwa [List.toFinset_card_of_nodup (nodup_of_chainLt W hchain), hlen] at h

theorem stone4 {N m : ℕ} (W : List Nat)
    (hrange : inRange W N = true) (hchain : chainLt W = true)
    (h4 : k4Free W = true) (hlen : W.length = m) :
    m ≤ Set.IsAPOfLengthFree.maxCard 4 N := by
  have h := maxCard_ge_of_witness W.toFinset (subset_Icc_of_inRange hrange)
    (isAPOfLengthFree_four h4)
  rwa [List.toFinset_card_of_nodup (nodup_of_chainLt W hchain), hlen] at h

theorem stone5 {N m : ℕ} (W : List Nat)
    (hrange : inRange W N = true) (hchain : chainLt W = true)
    (h5 : k5Free W = true) (hlen : W.length = m) :
    m ≤ Set.IsAPOfLengthFree.maxCard 5 N := by
  have h := maxCard_ge_of_witness W.toFinset (subset_Icc_of_inRange hrange)
    (isAPOfLengthFree_five h5)
  rwa [List.toFinset_card_of_nodup (nodup_of_chainLt W hchain), hlen] at h

/-! ## §6 The Behrend-fiber witnesses and the stones

The banked ladder (receipts142b_audit.txt B2, all PASS with the
difference-set scanner AND the midpoint scanner, plus B2-LADDER: the same
fibers are 4-AP- and 5-AP-free): the layer×sphere fiber at base B = 2m,
digit vectors `v ∈ [0,m)^d` keyed by `(Σvᵢ, Σvᵢ²)`, encoded as
`Σ vᵢ·Bⁱ` (BEHREND_PROOF.md §6, engine142b_audit.py behrend_fiber_b). -/

/-- The (d, m) = (3, 3) fiber: base B = 6, N = B^d = 216, |S| = 6. -/
def w216 : List Nat := [8, 13, 38, 48, 73, 78]

/-- The (d, m) = (4, 3) fiber: B = 6, N = 1296, |S| = 12. -/
def w1296 : List Nat := [8, 13, 38, 48, 73, 78, 218, 228, 288, 433, 438, 468]

/-- The (d, m) = (5, 3) fiber: B = 6, N = 7776, |S| = 30. -/
def w7776 : List Nat := [44, 49, 79, 224, 229, 254, 264, 289, 294, 439, 469,
  474, 1304, 1309, 1334, 1344, 1369, 1374, 1514, 1524, 1584, 1729, 1734,
  1764, 2599, 2629, 2634, 2809, 2814, 2844]

/-- The (d, m) = (6, 3) fiber: B = 6, N = 46656, |S| = 90. -/
def w46656 : List Nat := [266, 296, 301, 476, 481, 511, 1346, 1376, 1381,
  1526, 1586, 1596, 1736, 1741, 1766, 1776, 1801, 1806, 2636, 2641, 2671,
  2816, 2821, 2846, 2856, 2881, 2886, 3031, 3061, 3066, 7826, 7856, 7861,
  8006, 8066, 8076, 8216, 8221, 8246, 8256, 8281, 8286, 9086, 9146, 9156,
  9506, 9516, 9576, 10376, 10381, 10406, 10416, 10441, 10446, 10586, 10596,
  10656, 10801, 10806, 10836, 15596, 15601, 15631, 15776, 15781, 15806,
  15816, 15841, 15846, 15991, 16021, 16026, 16856, 16861, 16886, 16896,
  16921, 16926, 17066, 17076, 17136, 17281, 17286, 17316, 18151, 18181,
  18186, 18361, 18366, 18396]

/-- The (d, m) = (3, 5) fiber: B = 10, N = 1000, |S| = 6. -/
def w1000 : List Nat := [12, 21, 102, 120, 201, 210]

/-- The (d, m) = (4, 5) fiber: B = 10, N = 10000, |S| = 24. -/
def w10000 : List Nat := [123, 132, 213, 231, 312, 321, 1023, 1032, 1203,
  1230, 1302, 1320, 2013, 2031, 2103, 2130, 2301, 2310, 3012, 3021, 3102,
  3120, 3201, 3210]

/-- The (d, m) = (3, 7) fiber: B = 14, N = 2744, |S| = 12. -/
def w2744 : List Nat := [61, 74, 230, 282, 412, 477, 789, 854, 984, 1036,
  1192, 1205]

/-- The (d, m) = (4, 7) fiber: B = 14, N = 38416, |S| = 48. -/
def w38416 : List Nat := [649, 662, 831, 857, 1026, 1039, 3184, 3223, 3366,
  3418, 3951, 3964, 5732, 5771, 6096, 6161, 6681, 6707, 8293, 8306, 8462,
  8514, 8644, 8709, 9021, 9086, 9216, 9268, 9424, 9437, 11023, 11049, 11569,
  11634, 11959, 11998, 13766, 13779, 14312, 14364, 14507, 14546, 16691,
  16704, 16873, 16899, 17068, 17081]

/-- The (d, m) = (2, 9) fiber: B = 18, N = 324, |S| = 2. -/
def w324 : List Nat := [1, 18]

/-- The (d, m) = (5, 2) fiber: B = 4, N = 1024, |S| = 10 — the base-4
weight-2 {0,1}-digit family (the Cantor-sibling; §7). -/
def w1024 : List Nat := [5, 17, 20, 65, 68, 80, 257, 260, 272, 320]

/-! ### The k=3 stones (the full ten-fiber banked ladder) -/

theorem r3_216_ge : 6 ≤ r 3 216 :=
  stone3 w216 (by decide) (by decide) (by decide) rfl

theorem r3_1296_ge : 12 ≤ r 3 1296 :=
  stone3 w1296 (by decide) (by decide) (by decide) rfl

theorem r3_7776_ge : 30 ≤ r 3 7776 :=
  stone3 w7776 (by decide) (by decide) (by decide) rfl

theorem r3_46656_ge : 90 ≤ r 3 46656 :=
  stone3 w46656 (by decide) (by decide) (by decide) rfl

theorem r3_1000_ge : 6 ≤ r 3 1000 :=
  stone3 w1000 (by decide) (by decide) (by decide) rfl

theorem r3_10000_ge : 24 ≤ r 3 10000 :=
  stone3 w10000 (by decide) (by decide) (by decide) rfl

theorem r3_2744_ge : 12 ≤ r 3 2744 :=
  stone3 w2744 (by decide) (by decide) (by decide) rfl

theorem r3_38416_ge : 48 ≤ r 3 38416 :=
  stone3 w38416 (by decide) (by decide) (by decide) rfl

theorem r3_324_ge : 2 ≤ r 3 324 :=
  stone3 w324 (by decide) (by decide) (by decide) rfl

theorem r3_1024_ge : 10 ≤ r 3 1024 :=
  stone3 w1024 (by decide) (by decide) (by decide) rfl

/-! ### The k=4 stones (the B2-LADDER receipts; the 24+-element fibers are
outside the decide budget for the 4-fold nested scan — named honestly in
the worklog, not claimed) -/

theorem r4_216_ge : 6 ≤ r 4 216 :=
  stone4 w216 (by decide) (by decide) (by decide) rfl

theorem r4_324_ge : 2 ≤ r 4 324 :=
  stone4 w324 (by decide) (by decide) (by decide) rfl

theorem r4_1024_ge : 10 ≤ r 4 1024 :=
  stone4 w1024 (by decide) (by decide) (by decide) rfl

theorem r4_1000_ge : 6 ≤ r 4 1000 :=
  stone4 w1000 (by decide) (by decide) (by decide) rfl

theorem r4_1296_ge : 12 ≤ r 4 1296 :=
  stone4 w1296 (by decide) (by decide) (by decide) rfl

theorem r4_2744_ge : 12 ≤ r 4 2744 :=
  stone4 w2744 (by decide) (by decide) (by decide) rfl

/-! ### The k=5 stones (the two smallest fibers only) -/

theorem r5_216_ge : 6 ≤ r 5 216 :=
  stone5 w216 (by decide) (by decide) (by decide) rfl

theorem r5_324_ge : 2 ≤ r 5 324 :=
  stone5 w324 (by decide) (by decide) (by decide) rfl

theorem r5_1000_ge : 6 ≤ r 5 1000 :=
  stone5 w1000 (by decide) (by decide) (by decide) rfl

/-! ### Headline stones in official-definition form (no abbrev) -/

theorem r3_216_ge_official : 6 ≤ Set.IsAPOfLengthFree.maxCard 3 216 := r3_216_ge

theorem r3_7776_ge_official : 30 ≤ Set.IsAPOfLengthFree.maxCard 3 7776 :=
  r3_7776_ge

theorem r3_46656_ge_official : 90 ≤ Set.IsAPOfLengthFree.maxCard 3 46656 :=
  r3_46656_ge

/-! ## §7 The arsenal bridge (BOSS's law: ≥2 laws cited by file:line,
read before cite; both genuinely used below)

* `noTernaryTwo` — Arsenal/CardinalWorlds.lean:41 — the Cantor verdict
  reader (ternary expansion avoids the digit 2), structural recursion
  `if n = 0 then true else if n % 3 = 2 then false else recurse (n / 3)`.
* `noTernaryTwoStruct` — Arsenal/CardinalWorlds.lean:51 — its
  decide-compatible structural twin (fuel-indexed), with the equivalence
  law `noTernaryTwo_eq_struct` at CardinalWorlds.lean:58 (n + 1 ≤ k).
* `ErdosTernary2.lt_three_cases` — Arsenal/ErdosTernary2/Basic.lean:16 —
  every n < 3 is 0, 1 or 2 (the ternary digit trichotomy). -/

/-- The base-4 digit reader — the m=2 sibling of the Arsenal Cantor reader
`noTernaryTwo` (CardinalWorlds.lean:41): same structural recursion at base
4, digit test `2 ≤ n % 4` (base-4 digits avoid 2 and 3). Fuel-indexed like
`noTernaryTwoStruct` (CardinalWorlds.lean:51) for kernel decidability. -/
def noQuatTwoS : Nat → Nat → Bool
  | _, 0 => true
  | n, k + 1 => if n = 0 then true
                else if 2 ≤ n % 4 then false
                else noQuatTwoS (n / 4) k

/-- The (5, 2) fiber w1024 is base-4 {0,1}-digit-clean: the m=2 Behrend
fiber IS the weight-2 base-4 {0,1}-digit family (decide, fuel x + 1). -/
theorem w1024_quat_clean : allT (fun x => noQuatTwoS x (x + 1)) w1024 = true := by
  decide

/-- The first base-4 digit law: a nonzero clean number has digit < 2. -/
theorem first_quat_digit_lt (x : ℕ) (hx : x ≠ 0)
    (h : noQuatTwoS x (x + 1) = true) : x % 4 < 2 := by
  have h1 : (if x = 0 then true else if 2 ≤ x % 4 then false
      else noQuatTwoS (x / 4) x) = true := h
  rw [if_neg hx] at h1
  by_contra hge
  have hge' : 2 ≤ x % 4 := by omega
  rw [if_pos hge'] at h1
  exact Bool.noConfusion h1

/-- The m=2 fiber family is DISJOINT from the Arsenal Cantor family: every
w1024 element fails the Arsenal reader `noTernaryTwoStruct`
(CardinalWorlds.lean:51) — the digit-fiber construction is strictly richer
than the Cantor {0,1}-ternary family (10 elements in [1, 1024] vs the
Cantor family's 2^5 = 32). Decided on the Arsenal's own reader. -/
theorem w1024_not_cantor :
    allT (fun x => !(noTernaryTwoStruct x (x + 1))) w1024 = true := by
  decide

/-- The Arsenal reader's first ternary digit is never 2 (nonzero case). -/
theorem ternary_first_digit (x : ℕ) (hx : x ≠ 0)
    (h : noTernaryTwoStruct x (x + 1) = true) : x % 3 ≠ 2 := by
  intro h2
  have h1 : (if x = 0 then true else if x % 3 = 2 then false
      else noTernaryTwoStruct (x / 3) x) = true := h
  rw [if_neg hx, if_pos h2] at h1
  exact Bool.noConfusion h1

/-- **The Arsenal trichotomy law applied** (ErdosTernary2/Basic.lean:16):
a nonzero Cantor-clean number has ternary digit 0 or 1 — the digit-window
law underlying the Cantor reader's 3-AP-freeness, via
`ErdosTernary2.lt_three_cases` on `x % 3 < 3`. -/
theorem ternary_cantor_digit01 (x : ℕ) (hx : x ≠ 0)
    (h : noTernaryTwoStruct x (x + 1) = true) : x % 3 = 0 ∨ x % 3 = 1 := by
  rcases ErdosTernary2.lt_three_cases (x % 3)
      (Nat.mod_lt x (by decide : 0 < 3)) with h0 | h1 | h2
  · exact Or.inl h0
  · exact Or.inr h1
  · exact absurd h2 (ternary_first_digit x hx h)

/-! ## §8 The board -/

/-- The kernel board: the transfer + the three headline ladders (k=3 full,
k=4/k=5 decide-budget fibers) over the official r. -/
theorem dm142b_board :
    6 ≤ r 3 216 ∧ 12 ≤ r 3 1296 ∧ 30 ≤ r 3 7776 ∧ 90 ≤ r 3 46656 ∧
    6 ≤ r 3 1000 ∧ 24 ≤ r 3 10000 ∧ 12 ≤ r 3 2744 ∧ 48 ≤ r 3 38416 ∧
    2 ≤ r 3 324 ∧ 10 ≤ r 3 1024 ∧ 6 ≤ r 4 216 ∧ 2 ≤ r 4 324 ∧
    10 ≤ r 4 1024 ∧ 6 ≤ r 4 1000 ∧ 12 ≤ r 4 1296 ∧ 12 ≤ r 4 2744 ∧
    6 ≤ r 5 216 ∧ 2 ≤ r 5 324 ∧ 6 ≤ r 5 1000 :=
  ⟨r3_216_ge, r3_1296_ge, r3_7776_ge, r3_46656_ge, r3_1000_ge, r3_10000_ge,
   r3_2744_ge, r3_38416_ge, r3_324_ge, r3_1024_ge, r4_216_ge, r4_324_ge,
   r4_1024_ge, r4_1000_ge, r4_1296_ge, r4_2744_ge, r5_216_ge, r5_324_ge,
   r5_1000_ge⟩

#print axioms DM142B.maxCard_ge_of_witness
#print axioms DM142B.isAPOfLengthFree_three
#print axioms DM142B.r3_216_ge
#print axioms DM142B.r3_7776_ge
#print axioms DM142B.r3_46656_ge
#print axioms DM142B.dm142b_board
#print axioms DM142B.w1024_not_cantor
#print axioms DM142B.ternary_cantor_digit01

#eval "DM142B_LOWER_GREEN"

end DM142B
