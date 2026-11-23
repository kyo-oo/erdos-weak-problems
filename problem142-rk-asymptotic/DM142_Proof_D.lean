import Mathlib
import FC.Combinatorics.AP.Basic
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds

/-! # DM142_Proof_D — THEOREM V-GEN: THE HOMOTHETIC AMPLIFICATION (W85-142D)

BOSS's W85 order: the named continuation of the DM #142 lanes — V-GEN
kernel'd, complete proof, CI the only verdict. Over the OFFICIAL
definition (FC/Combinatorics/AP/Basic.lean, byte-identical to
google-deepmind/formal-conjectures @ 2207c54d):

    noncomputable abbrev r : ℕ → ℕ → ℕ := Set.IsAPOfLengthFree.maxCard

this kernel proves THEOREM V-GEN in the all-integer form (no division
after D0 := ⌊N/(4m(m−1))⌋):

    theorem v_gen (k m N : ℕ) (hk : 3 ≤ k) (hm : 2 ≤ m) (hN : 16*m*m ≤ N) :
        2*m*(r k N) ≤ (2*(r k m)+1)*N

The proof (UPPER_STACK.md THEOREM V-GEN + LEMMA AFF-K, derived W80-142U
event 3, engine-validated 56/56 — engine142uppergen.py, VGEN-band exhaustive
at 5 scales, VGEN-dblcount exact on planted AP-free sets at (3,9,1296) and
(4,8,1024)):

§1 AFF-K (the copy cap): a homothetic copy c(a,d) = {a+jd : j < m} hosts
   at most r_k(m) points of any officially k-AP-free set — via the index
   transfer: an official index-k-AP (a', d') inside T+1 (the shifted index
   set) maps forward to the official k-AP (a + (a'−1)d, d'·d) inside S.
§2–§3 The incidence double count (all integer): the band carries ≥ m·D0
   distinct valid copies per point; the copy family has ≤ D0·N members,
   each hosting ≤ r_k(m) points (AFF-K); cancel D0 ≥ 1.
§4 The assembly: |S| ≤ |bandS| + 2(m−1)D0; 2m|S| ≤ 2·r_k(m)·N +
   4m(m−1)D0 ≤ 2·r_k(m)·N + N.
§5 The sup transfer (the DM142C u_gen_zero idiom, verbatim).

House machinery (§0) follows the CI-green DM142_Proof_A/C, attributed.
Zero sorry, zero native_decide; `#print axioms` on every headline. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 262144

namespace DM142D

/-- The OFFICIAL r_k(N) — the same abbrev DM142_Official.lean declares. -/
noncomputable abbrev r : ℕ → ℕ → ℕ := Set.IsAPOfLengthFree.maxCard

/-! ## §0 House machinery (the DM142_Proof_A/C idiom, attributed) -/

/-- The ℕ-smul identity (the official set-builder writes `a + n • d`). -/
theorem nsmul_nat (i d : ℕ) : i • d = i * d := by simp

/-- Finset subset → coerced-set subset (via mem_coe, the green idiom). -/
theorem coe_sub {S T : Finset ℕ} (h : S ⊆ T) : (↑S : Set ℕ) ⊆ (↑T : Set ℕ) := by
  intro z hz
  exact Finset.mem_coe.2 (h (Finset.mem_coe.1 hz))

/-- AP-freeness passes to subsets (official definition, one line). -/
theorem apFree_subset {s t : Set ℕ} {k : ℕ∞} (hs : s.IsAPOfLengthFree k)
    (hst : t ⊆ s) : t.IsAPOfLengthFree k := by
  intro u hut hu
  exact hs u (hut.trans hst) hu

/-- The sSup-membership transfer (from the maxCard definition alone;
DM142_Proof_A.lean §0 / DM142_Proof_C.lean §0, copied verbatim with
attribution). -/
theorem maxCard_ge_of_witness {k N : ℕ} (S : Finset ℕ)
    (hsub : S ⊆ Finset.Icc 1 N) (hfree : (S : Set ℕ).IsAPOfLengthFree k) :
    S.card ≤ Set.IsAPOfLengthFree.maxCard k N := by
  simp only [Set.IsAPOfLengthFree.maxCard]
  refine le_csSup ?_ ⟨S, hsub, hfree, rfl⟩
  refine ⟨(Finset.Icc 1 N).card, mem_upperBounds.2 ?_⟩
  rintro n ⟨T, hTsub, -, rfl⟩
  exact Finset.card_mono hTsub

/-- The DIY sum-const (zero API risk): `∑ _ ∈ Q, c = Q.card * c`. -/
theorem sum_const_nat (Q : Finset ℕ) (c : ℕ) :
    (Q.sum fun _ => c) = Q.card * c := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp
  | insert a Q ha ih =>
      rw [Finset.sum_insert ha, ih, Finset.card_insert_of_notMem ha]
      omega

/-! ## §1 AFF-K: THE COPY CAP -/

/-- **LEMMA AFF-K (the homothetic copy cap).** For k ≥ 2, d ≥ 1, m ≥ 1:
the index set `T := {j < m : a + j*d ∈ S}` of any officially k-AP-free
Finset `S` has `|T| ≤ r k m`. The route: the shifted index set `T+1` is
itself officially k-AP-free (an official k-AP `(a', d')` in `T+1` maps
forward — through `x ↦ a + (x−1)*d` — to the official k-AP
`(a + (a'−1)*d, d'·d)` inside `S`), then the green witness transfer
`maxCard_ge_of_witness`. -/
theorem aff_k (k m a d : ℕ) (hk : 2 ≤ k) (hd : 1 ≤ d) (S : Finset ℕ)
    (hfree : (↑S : Set ℕ).IsAPOfLengthFree ((k : ℕ) : ENat)) :
    ((Finset.range m).filter (fun j => a + j * d ∈ S)).card ≤
      Set.IsAPOfLengthFree.maxCard k m := by
  classical
  set T : Finset ℕ := (Finset.range m).filter (fun j => a + j * d ∈ S) with hT
  set T' : Finset ℕ := T.image (fun j => j + 1) with hT'
  -- T' ⊆ [1, m]
  have hT'sub : T' ⊆ Finset.Icc 1 m := by
    intro y hy
    obtain ⟨j, hj, hje⟩ := Finset.mem_image.1 hy
    have hjm : j < m := (Finset.mem_filter.1 hj).1
    rw [← hje]
    simp only [Finset.mem_Icc]
    omega
  -- T+1 is officially k-AP-free (the forward index transfer)
  have hT'free : (↑T' : Set ℕ).IsAPOfLengthFree ((k : ℕ) : ENat) := by
    intro u husub hap
    obtain ⟨a', d', hcardw⟩ := hap
    have hcard : ENat.card u = ((k : ℕ) : ENat) := hcardw.1
    have hset : u = {a' + n • d' | (n : ℕ) (_ : n < ((k : ℕ) : ENat))} :=
      hcardw.2
    -- d' ≠ 0 (else u is a singleton, card 1 ≠ k ≥ 2)
    have hd' : 1 ≤ d' := by
      by_contra hd'0
      push_neg at hd'0
      have hd'eq : d' = 0 := by omega
      have hsingle : u ⊆ ({a'} : Set ℕ) := by
        intro x hx
        have hxu : x ∈ {a' + n • d' | (n : ℕ) (_ : n < ((k : ℕ) : ENat))} := by
          rw [← hset]; exact hx
        obtain ⟨-, -, hneq⟩ := hxu
        simp only [Set.mem_singleton_iff]
        rw [← hneq, nsmul_nat, hd'eq, Nat.mul_zero, Nat.add_zero]
      have hle : u.encard ≤ ({a'} : Set ℕ).encard :=
        Set.encard_le_encard hsingle
      rw [Set.encard_singleton] at hle
      have hcard' : u.encard = ((k : ℕ) : ENat) := hcard
      have hbad : ((k : ℕ) : ENat) ≤ ((1 : ℕ) : ENat) := by
        rw [← hcard']; exact hle
      have hbad' : k ≤ 1 := by exact_mod_cast hbad
      omega
    -- a' ≥ 1 (a' is an element of u ⊆ T+1 ⊆ [1, m])
    have ha' : 1 ≤ a' := by
      have ha'mem : a' ∈ u := by
        have h1 : a' ∈ {a' + n • d' | (n : ℕ) (_ : n < ((k : ℕ) : ENat))} := by
          refine ⟨0, by exact_mod_cast (by omega : (0 : ℕ) < k), ?_⟩
          rw [nsmul_nat, Nat.zero_mul, Nat.add_zero]
        rw [hset]; exact h1
      have ha'T'fin : a' ∈ T' := Finset.mem_coe.1 (husub ha'mem)
      obtain ⟨j, -, hje⟩ := Finset.mem_image.1 ha'T'fin
      omega
    -- the image AP inside S: first term A, difference D
    set A : ℕ := a + (a' - 1) * d with hA
    set D : ℕ := d' * d with hD
    set W : Finset ℕ :=
      (Finset.range k).image (fun i => a + (a' + i * d' - 1) * d) with hW
    -- W ⊆ S (the element chain: a'+i*d' ∈ u ⊆ T+1 gives the index in T)
    have hWsub : (↑W : Set ℕ) ⊆ (↑S : Set ℕ) := by
      intro y hy
      have hyW : y ∈ (Finset.range k).image (fun i => a + (a' + i * d' - 1) * d) :=
        Finset.mem_coe.1 hy
      obtain ⟨i, hi, hie⟩ := Finset.mem_image.1 hyW
      have hik : i < k := hi
      have hxu : a' + i * d' ∈ u := by
        have h1 : a' + i * d' ∈
            {a' + n • d' | (n : ℕ) (_ : n < ((k : ℕ) : ENat))} := by
          refine ⟨i, by exact_mod_cast hik, ?_⟩
          rw [nsmul_nat]
        rw [hset]; exact h1
      have hxT'fin : a' + i * d' ∈ T' := Finset.mem_coe.1 (husub hxu)
      obtain ⟨j, hj, hje⟩ := Finset.mem_image.1 hxT'fin
      have hSj : a + j * d ∈ S := (Finset.mem_filter.1 hj).2
      have hyj : y = a + j * d := by
        rw [← hie]
        have h1 : a' + i * d' - 1 = j := by omega
        omega
      rw [hyj]
      exact Finset.mem_coe.2 hSj
    -- W is an official k-AP with first term A and difference D
    have hWap : Set.IsAPOfLength (↑W : Set ℕ) ((k : ℕ) : ENat) := by
      refine ⟨A, D, ?_, ?_⟩
      · -- encard ↑W = k
        have hcardW : W.card = k := by
          rw [hW]
          refine Finset.card_image_of_injOn (fun i hi i' _ heq => ?_)
          have h1 : (a' + i * d' - 1) * d = (a' + i' * d' - 1) * d :=
            Nat.add_right_cancel heq
          have h2 : a' + i * d' - 1 = a' + i' * d' - 1 :=
            Nat.eq_of_mul_eq_mul_right hd h1
          have h3 : i * d' = i' * d' := by omega
          exact Nat.eq_of_mul_eq_mul_right hd' h3
        rw [Set.encard_coe_eq_coe_finsetCard, hcardW]
      · -- ↑W = {A + n•D | n < k}
        ext y
        constructor
        · rintro ⟨i, hi, hie⟩
          refine ⟨i, by exact_mod_cast hi, ?_⟩
          rw [nsmul_nat, ← hie]
          have h1 : a' + i * d' - 1 = (a' - 1) + i * d' := by omega
          rw [h1]
          ring
        · rintro ⟨n, hn, hneq⟩
          have hnk : n < k := by exact_mod_cast hn
          refine ⟨n, hnk, ?_⟩
          rw [nsmul_nat] at hneq
          have h1 : a' + n * d' - 1 = (a' - 1) + n * d' := by omega
          rw [h1] at hneq ⊢
          rw [← hneq]
          ring
    exact hfree ↑W hWsub hWap
  -- the green witness transfer
  have h1 := maxCard_ge_of_witness T' hT'sub hT'free
  have h2 : T'.card = T.card := by
    rw [hT']
    exact Finset.card_image_of_injOn (fun _ _ _ _ h => by omega)
  rw [h2] at h1
  exact h1

/-! ## §2–§4 THE DOUBLE COUNT AND THE ASSEMBLY -/

/-- **The witness bound.** For k ≥ 3, m ≥ 2, N ≥ 16m²: every officially
k-AP-free Finset `S ⊆ [1,N]` satisfies `2*m*S.card ≤ (2*(r k m)+1)*N`.
The homothetic double count: the band carries ≥ m·D0 distinct valid
copies per point (D0 = ⌊N/(4m(m−1))⌋ ≥ 1); the copy family has ≤ D0·N
members, each hosting ≤ r_k(m) points (AFF-K); the fringe carries
≤ 2(m−1)D0 points with 4m(m−1)D0 ≤ N. All-integer assembly. -/
theorem v_gen_witness (k m N : ℕ) (hk : 3 ≤ k) (hm : 2 ≤ m)
    (hN : 16 * m * m ≤ N) (S : Finset ℕ)
    (hSsub : S ⊆ Finset.Icc 1 N)
    (hSfree : (↑S : Set ℕ).IsAPOfLengthFree ((k : ℕ) : ENat)) :
    2 * m * S.card ≤ (2 * (r k m) + 1) * N := by
  classical
  -- the S-membership bounds (x ≥ 1 for every x ∈ S)
  have hxmem : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N := by
    intro x hx
    have hxI : x ∈ Finset.Icc 1 N := hSsub hx
    have := Finset.mem_Icc.1 hxI
    omega
  set D0 : ℕ := N / (4 * m * (m - 1)) with hD0def
  -- (F1) 4*m*(m-1) ≤ N
  have hF1 : 4 * m * (m - 1) ≤ N := by
    calc 4 * m * (m - 1) ≤ 4 * m * m := Nat.mul_le_mul_left _ (by omega)
      _ = 4 * (m * m) := by ring
      _ ≤ 16 * (m * m) := by
          calc 4 * (m * m) = (m * m) * 4 := Nat.mul_comm _ _
            _ ≤ (m * m) * 16 := Nat.mul_le_mul_left _ (by omega)
            _ = 16 * (m * m) := Nat.mul_comm _ _
      _ = 16 * m * m := by ring
      _ ≤ N := hN
  have hD0pos : 0 < 4 * m * (m - 1) :=
    Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))
  -- (F2) D0 ≥ 1
  have hD0ge1 : 1 ≤ D0 := Nat.div_pos hF1 hD0pos
  -- (F3) 4*m*(m-1)*D0 ≤ N
  have hF3 : 4 * m * (m - 1) * D0 ≤ N := Nat.mul_div_le N (4 * m * (m - 1))
  -- (F4) (m-1)*D0 ≤ N (the fringe intervals fit)
  have hF4 : (m - 1) * D0 ≤ N := by
    have h1 : (m - 1) * D0 ≤ (4 * m) * ((m - 1) * D0) :=
      Nat.mul_le_mul_left ((m - 1) * D0) (by omega)
    have h2 : (4 * m) * ((m - 1) * D0) = 4 * m * (m - 1) * D0 := by ring
    omega
  -- The band points of S
  set bandS : Finset ℕ := S.filter
    (fun x => (m - 1) * D0 ≤ x - 1 ∧ (m - 1) * D0 ≤ N - x) with hbandS
  -- The copy-index Finset Q := {(d, a) : 1 ≤ d ≤ D0, 1 ≤ a ≤ N, a+(m-1)d ≤ N}
  set Q : Finset ℕ :=
    ((Finset.Icc 1 D0).product (Finset.Ico 1 (N + 1))).filter
      (fun q => q.2 + (m - 1) * q.1 ≤ N) with hQ
  -- The incidence Finset P := {(x, (d, j)) : x ∈ S, 1 ≤ d ≤ D0, j < m,
  -- j*d ≤ x-1, x+(m-1-j)*d ≤ N}
  set P : Finset ℕ :=
    (S.product ((Finset.Icc 1 D0).product (Finset.Ico 0 m))).filter
      (fun p => p.2.2 * p.2.1 ≤ p.1 - 1 ∧ p.1 + (m - 1 - p.2.2) * p.2.1 ≤ N)
    with hP
  -- the shape facts for p ∈ P
  have hPfacts : ∀ p ∈ P, p.1 ∈ S ∧ 1 ≤ p.2.1 ∧ p.2.1 ≤ D0 ∧ p.2.2 < m ∧
      p.2.2 * p.2.1 ≤ p.1 - 1 ∧ p.1 + (m - 1 - p.2.2) * p.2.1 ≤ N ∧ 1 ≤ p.1 := by
    intro p hp
    have hpP := (Finset.mem_filter.1 hp).1
    have hp1 : p.1 ∈ S := (Finset.mem_product.1 hpP).1
    have hp2 := (Finset.mem_product.1 hpP).2
    have hp2a : p.2.1 ∈ Finset.Icc 1 D0 := (Finset.mem_product.1 hp2).1
    have hp2b : p.2.2 ∈ Finset.Ico 0 m := (Finset.mem_product.1 hp2).2
    have hval := (Finset.mem_filter.1 hp).2
    obtain ⟨hv1, hv2⟩ := hval
    have ha := Finset.mem_Icc.1 hp2a
    have hb := Finset.mem_Ico.1 hp2b
    have hx := hxmem p.1 hp1
    exact ⟨hp1, ha.1, ha.2, hb, hv1, hv2, hx.1⟩
  -- |Q| ≤ D0 * N
  have hQcard : Q.card ≤ D0 * N := by
    have hQsub : Q ⊆ (Finset.Icc 1 D0).product (Finset.Ico 1 (N + 1)) :=
      Finset.filter_subset _ _
    have h1 := Finset.card_mono hQsub
    rw [Finset.card_product] at h1
    have h2 : (Finset.Icc 1 D0).card = D0 := by rw [Nat.card_Icc]; omega
    have h3 : (Finset.Ico 1 (N + 1)).card = N := by rw [Nat.card_Ico]; omega
    omega
  -- the copy index of p ∈ P lands in Q
  have hmemQ : ∀ p ∈ P, (p.2.1, p.1 - p.2.2 * p.2.1) ∈ Q := by
    intro p hp
    obtain ⟨hpS, hd1, hdD0, hjm, hv1, hv2, hx1⟩ := hPfacts p hp
    have hage1 : 1 ≤ p.1 - p.2.2 * p.2.1 := by omega
    have haval : p.1 - p.2.2 * p.2.1 + (m - 1) * p.2.1 ≤ N := by
      have h1 : (m - 1 - p.2.2) * p.2.1 + p.2.2 * p.2.1 = (m - 1) * p.2.1 := by
        rw [← Nat.mul_add, Nat.add_sub_cancel' (by omega)]
      have h2 : p.1 ≤ N := by
        have := hxmem p.1 hpS
        omega
      omega
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨
      Finset.mem_Icc.2 ⟨hd1, hdD0⟩, ?_⟩, ?_⟩
    · simp only [Finset.mem_Ico]
      omega
    · omega
  -- LOWER: |bandS| * (D0 * m) ≤ |P|
  have hlower : bandS.card * (D0 * m) ≤ P.card := by
    have hsub : bandS.product ((Finset.Icc 1 D0).product (Finset.Ico 0 m)) ⊆ P := by
      intro p hp
      have hp1 : p.1 ∈ bandS := (Finset.mem_product.1 hp).1
      have hp2 : p.2 ∈ (Finset.Icc 1 D0).product (Finset.Ico 0 m) :=
        (Finset.mem_product.1 hp).2
      have hp2a : p.2.1 ∈ Finset.Icc 1 D0 := (Finset.mem_product.1 hp2).1
      have hp2b : p.2.2 ∈ Finset.Ico 0 m := (Finset.mem_product.1 hp2).2
      have ha := Finset.mem_Icc.1 hp2a
      have hb := Finset.mem_Ico.1 hp2b
      have hpS : p.1 ∈ S := (Finset.mem_filter.1 hp1).1
      have hband := (Finset.mem_filter.1 hp1).2
      obtain ⟨hb1, hb2⟩ := hband
      have hval1 : p.2.2 * p.2.1 ≤ p.1 - 1 := by
        have h1 : p.2.2 * p.2.1 ≤ (m - 1) * D0 :=
          Nat.mul_le_mul (by omega) (by omega)
        omega
      have hval2 : p.1 + (m - 1 - p.2.2) * p.2.1 ≤ N := by
        have h1 : (m - 1 - p.2.2) * p.2.1 ≤ (m - 1) * D0 :=
          Nat.mul_le_mul (by omega) (by omega)
        have h2 : p.1 ≤ N := by
          have := hxmem p.1 hpS
          omega
        omega
      exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hpS, hp2⟩,
        ⟨hval1, hval2⟩⟩
    have h1 := Finset.card_mono hsub
    rw [Finset.card_product, Finset.card_product,
      Finset.card_product] at h1
    have h2 : (Finset.Icc 1 D0).card = D0 := by rw [Nat.card_Icc]; omega
    have h3 : (Finset.Ico 0 m).card = m := by rw [Nat.card_Ico]; omega
    omega
  -- UPPER: |P| ≤ (r k m) * Q.card
  have hupper : P.card ≤ (r k m) * Q.card := by
    -- the cover: P = ⋃_{q ∈ Q} (the fiber at q)
    have hcover : P = Q.bUnion
        (fun q => P.filter (fun p => (p.2.1, p.1 - p.2.2 * p.2.1) = q)) := by
      ext p
      constructor
      · intro hp
        have hq := hmemQ p hp
        exact Finset.mem_bUnion.2 ⟨(p.2.1, p.1 - p.2.2 * p.2.1), hq,
          Finset.mem_filter.2 ⟨hp, rfl⟩⟩
      · intro hb
        obtain ⟨q, -, hpf⟩ := Finset.mem_bUnion.1 hb
        exact (Finset.mem_filter.1 hpf).1
    -- each fiber ≤ r k m (AFF-K at the fiber's copy, via the j-injection)
    have hfib : ∀ q ∈ Q,
        (P.filter (fun p => (p.2.1, p.1 - p.2.2 * p.2.1) = q)).card ≤ r k m := by
      intro q hq
      have hqP := (Finset.mem_filter.1 hq).1
      have hq1 := Finset.mem_Icc.1 (Finset.mem_product.1 hqP).1
      have hqval : q.2 + (m - 1) * q.1 ≤ N := (Finset.mem_filter.1 hq).2
      have hdq1 : 1 ≤ q.1 := hq1.1
      -- the index Finset of this copy, capped by AFF-K
      have hTqcap : ((Finset.range m).filter (fun j => q.2 + j * q.1 ∈ S)).card
          ≤ r k m := aff_k k m q.2 q.1 (by omega) hdq1 S hSfree
      -- the fiber facts: p.2.2 < m and p.1 = q.2 + p.2.2 * q.1
      have hfacts : ∀ p ∈ P.filter
          (fun p => (p.2.1, p.1 - p.2.2 * p.2.1) = q),
          p.2.2 < m ∧ p.1 = q.2 + p.2.2 * q.1 := by
        intro p hp
        have hpP : p ∈ P := (Finset.mem_filter.1 hp).1
        have hio : (p.2.1, p.1 - p.2.2 * p.2.1) = q := (Finset.mem_filter.1 hp).2
        obtain ⟨hpS, -, -, hjm, hv1, -, hx1⟩ := hPfacts p hpP
        have h1 : p.2.1 = q.1 := congrArg Prod.fst hio
        have h2 : p.1 - p.2.2 * p.2.1 = q.2 := congrArg Prod.snd hio
        rw [h1] at hv1
        have h3 : p.1 = q.2 + p.2.2 * q.1 := by omega
        exact ⟨hjm, h3⟩
      -- the fiber's j-image ⊆ Tq
      have himg : (P.filter
          (fun p => (p.2.1, p.1 - p.2.2 * p.2.1) = q)).image (fun p => p.2.2)
          ⊆ (Finset.range m).filter (fun j => q.2 + j * q.1 ∈ S) := by
        intro j hjm
        obtain ⟨p, hp, hje⟩ := Finset.mem_image.1 hjm
        have hje' : p.2.2 = j := hje
        obtain ⟨hjm', hxeq⟩ := hfacts p hp
        have hpP : p ∈ P := (Finset.mem_filter.1 hp).1
        have hpS : p.1 ∈ S := (hPfacts p hpP).1
        refine Finset.mem_filter.2 ⟨hjm', ?_⟩
        rw [← hje', hxeq] at hpS
        exact hpS
      -- the j-map is injective on the fiber
      have hcard : (P.filter
          (fun p => (p.2.1, p.1 - p.2.2 * p.2.1) = q)).card
          = (P.filter (fun p => (p.2.1, p.1 - p.2.2 * p.2.1) = q)).image
              (fun p => p.2.2)).card :=
        Finset.card_image_of_injOn (fun p hp p' hp' hje => by
          have hje' : p.2.2 = p'.2.2 := hje
          obtain ⟨hjm, hxeq⟩ := hfacts p (Finset.mem_coe.2 hp)
          obtain ⟨hjm', hxeq'⟩ := hfacts p' (Finset.mem_coe.2 hp')
          have h1 : p.2.1 = q.1 :=
            congrArg Prod.fst ((Finset.mem_filter.1 (Finset.mem_coe.2 hp)).2)
          have h1' : p'.2.1 = q.1 :=
            congrArg Prod.fst ((Finset.mem_filter.1 (Finset.mem_coe.2 hp')).2)
          rw [hje'] at hxeq'
          have hxe : p.1 = p'.1 := by omega
          have hde : p.2.1 = p'.2.1 := by omega
          exact Prod.ext hxe (Prod.ext hde hje'))
      rw [hcard]
      exact le_trans (Finset.card_mono himg) hTqcap
    -- assemble: |P| ≤ Σ fibers ≤ Σ (r k m) = Q.card * (r k m)
    have hsum : P.card ≤ ∑ q ∈ Q,
        (P.filter (fun p => (p.2.1, p.1 - p.2.2 * p.2.1) = q)).card := by
      rw [← hcover]
      exact Finset.card_bUnion_le _ _
    have hle : ∑ q ∈ Q,
        (P.filter (fun p => (p.2.1, p.1 - p.2.2 * p.2.1) = q)).card ≤
        ∑ _ ∈ Q, (r k m) :=
      Finset.sum_le_sum (fun q hq => hfib q hq)
    have hconst : (∑ _ ∈ Q, (r k m)) = Q.card * (r k m) :=
      sum_const_nat Q (r k m)
    have hcomm : (r k m) * Q.card = Q.card * (r k m) := Nat.mul_comm _ _
    omega
  -- THE CANCELLATION: |bandS| * m ≤ (r k m) * N
  have hcancel : bandS.card * m ≤ (r k m) * N := by
    have h1 : bandS.card * (D0 * m) ≤ (r k m) * (D0 * N) := le_trans hlower hupper
    by_contra hcon
    push_neg at hcon
    have h2 : (r k m) * N < bandS.card * m := hcon
    have h3 : ((r k m) * N) * D0 < (bandS.card * m) * D0 :=
      Nat.mul_lt_mul_of_pos_right h2 hD0ge1
    have h4 : (bandS.card * m) * D0 ≤ ((r k m) * N) * D0 := by
      have e1 : bandS.card * (D0 * m) = (bandS.card * m) * D0 := by ring
      have e2 : (r k m) * (D0 * N) = ((r k m) * N) * D0 := by ring
      rw [e1, e2] at h1
      exact h1
    omega
  -- THE FRINGE: |S| ≤ |bandS| + 2*(m-1)*D0
  have hfringe : S.card ≤ bandS.card + 2 * ((m - 1) * D0) := by
    have hcoverS : S = bandS ∪ S.filter (fun x => ¬ ((m - 1) * D0 ≤ x - 1 ∧
        (m - 1) * D0 ≤ N - x)) := by
      ext x
      constructor
      · intro hx
        by_cases hb : (m - 1) * D0 ≤ x - 1 ∧ (m - 1) * D0 ≤ N - x
        · exact Finset.mem_union.2 (Or.inl (Finset.mem_filter.2 ⟨hx, hb⟩))
        · exact Finset.mem_union.2 (Or.inr (Finset.mem_filter.2 ⟨hx, hb⟩))
      · intro hu
        rcases Finset.mem_union.1 hu with h | h
        · exact (Finset.mem_filter.1 h).1
        · exact (Finset.mem_filter.1 h).1
    -- the off-band points lie in two intervals of length (m-1)*D0
    have hfringesub : S.filter (fun x => ¬ ((m - 1) * D0 ≤ x - 1 ∧
        (m - 1) * D0 ≤ N - x)) ⊆
        (Finset.Icc 1 ((m - 1) * D0)) ∪ (Finset.Icc (N - (m - 1) * D0 + 1) N) := by
      intro x hx
      have hxS : x ∈ S := (Finset.mem_filter.1 hx).1
      have hbad := (Finset.mem_filter.1 hx).2
      have hxN := hxmem x hxS
      push_neg at hbad
      rcases hbad with h | h
      · exact Finset.mem_union.2
          (Or.inl (Finset.mem_Icc.2 ⟨hxN.1, by omega⟩))
      · exact Finset.mem_union.2
          (Or.inr (Finset.mem_Icc.2 ⟨by omega, hxN.2⟩))
    have hcard1 : (Finset.Icc 1 ((m - 1) * D0)).card = (m - 1) * D0 := by
      rw [Nat.card_Icc]; omega
    have hcard2 : (Finset.Icc (N - (m - 1) * D0 + 1) N).card
        = (m - 1) * D0 := by
      rw [Nat.card_Icc]; omega
    rw [hcoverS]
    have h1 := Finset.card_union_le bandS
      (S.filter (fun x => ¬ ((m - 1) * D0 ≤ x - 1 ∧ (m - 1) * D0 ≤ N - x)))
    have h2 : (S.filter (fun x => ¬ ((m - 1) * D0 ≤ x - 1 ∧
        (m - 1) * D0 ≤ N - x))).card ≤
        ((Finset.Icc 1 ((m - 1) * D0)) ∪ (Finset.Icc (N - (m - 1) * D0 + 1) N)).card :=
      Finset.card_mono hfringesub
    have h3 := Finset.card_union_le (Finset.Icc 1 ((m - 1) * D0))
      (Finset.Icc (N - (m - 1) * D0 + 1) N)
    omega
  -- THE FINAL ASSEMBLY (all integer)
  have hfinal : 2 * m * S.card ≤ (2 * (r k m) + 1) * N := by
    have e1 : (2 * (r k m) + 1) * N = 2 * ((r k m) * N) + N := by ring
    have h1 : 2 * m * S.card ≤ 2 * m * (bandS.card + 2 * ((m - 1) * D0)) :=
      Nat.mul_le_mul_left (2 * m) hfringe
    have e2 : 2 * m * (bandS.card + 2 * ((m - 1) * D0))
        = 2 * (bandS.card * m) + 4 * m * ((m - 1) * D0) := by ring
    have h2 : 2 * (bandS.card * m) ≤ 2 * ((r k m) * N) :=
      Nat.mul_le_mul_left 2 hcancel
    have h3 : 4 * m * ((m - 1) * D0) ≤ N := by
      have e3 : 4 * m * ((m - 1) * D0) = 4 * m * (m - 1) * D0 := by ring
      rw [e3]
      exact hF3
    omega
  exact hfinal

/-! ## §5 THE SUP TRANSFER: THE HEADLINE -/

/-- **THEOREM V-GEN (the homothetic amplification, ALL k, SHARP constant —
the all-integer form).** For every k ≥ 3, m ≥ 2, N ≥ 16m²:
`2*m*(r k N) ≤ (2*(r k m)+1)*N` over the official
`Set.IsAPOfLengthFree.maxCard`. The band/copy double count of
`v_gen_witness` transferred through the csSup (the DM142C u_gen_zero
idiom): every witness card n satisfies 2*m*n ≤ B, so the sup ≤ B/(2m),
and 2*m*(B/(2m)) ≤ B. Derived UPPER_STACK.md THEOREM V-GEN, engine-
validated 56/56 (VGEN-band exhaustive at 5 scales, VGEN-dblcount exact at
(3,9,1296) and (4,8,1024)). -/
theorem v_gen (k m N : ℕ) (hk : 3 ≤ k) (hm : 2 ≤ m) (hN : 16 * m * m ≤ N) :
    2 * m * (r k N) ≤ (2 * (r k m) + 1) * N := by
  have hNpos : 1 ≤ N := by
    have h1 : 16 * (2 * 2) ≤ 16 * (m * m) :=
      Nat.mul_le_mul_left 16 (Nat.mul_le_mul (by omega) (by omega))
    have h2 : 16 * (2 * 2) = 64 := by norm_num
    omega
  have hstep : Set.IsAPOfLengthFree.maxCard k N ≤
      (2 * (r k m) + 1) * N / (2 * m) := by
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
        rw [← hy1]
        simp
      have hle : t.encard ≤ ({1} : Set ℕ).encard := Set.encard_le_encard hsub
      rw [Set.encard_singleton] at hle
      have hcardt' : t.encard = ((k : ℕ) : ENat) := hcardt
      have hbad : ((k : ℕ) : ENat) ≤ ((1 : ℕ) : ENat) := by
        rw [← hcardt']; exact hle
      have hbad' : k ≤ 1 := by exact_mod_cast hbad
      omega
    · rintro n ⟨S, hSsub, hSfree, rfl⟩
      have h2 := v_gen_witness k m N hk hm hN S hSsub hSfree
      exact (Nat.le_div_iff_mul_le (2 * m) (by omega)).2
        (by rw [Nat.mul_comm n (2 * m)]; exact h2)
  have h1 : 2 * m * (Set.IsAPOfLengthFree.maxCard k N) ≤
      2 * m * ((2 * (r k m) + 1) * N / (2 * m)) :=
    Nat.mul_le_mul_left (2 * m) hstep
  have h2 : 2 * m * ((2 * (r k m) + 1) * N / (2 * m)) ≤
      (2 * (r k m) + 1) * N :=
    Nat.mul_div_le ((2 * (r k m) + 1) * N) (2 * m)
  exact le_trans h1 h2

/-- **THE BOARD.** The concrete instantiation k = 3, m = 8, N ≥ 1024:
`16 * (r 3 N) ≤ (2 * (r 3 8) + 1) * N`. -/
theorem v_gen_board (N : ℕ) (hN : 1024 ≤ N) :
    16 * (r 3 N) ≤ (2 * (r 3 8) + 1) * N := by
  have h1 : 16 * 8 * 8 ≤ N := by
    have h : 16 * 8 * 8 = 1024 := by norm_num
    omega
  have h2 := v_gen 3 8 N (by omega) (by omega) h1
  have e : (2 : ℕ) * 8 = 16 := by norm_num
  rw [e] at h2
  exact h2

end DM142D

#print axioms DM142D.aff_k
#print axioms DM142D.v_gen_witness
#print axioms DM142D.v_gen
#print axioms DM142D.v_gen_board

#eval "DM142D_VGEN_GREEN"
