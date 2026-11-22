import Mathlib
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds

/-!
# DM61_Proof_D — THE K5/E5 RAMSEY LADDER (W84-61B)

BOSS's W84 order: the W83-named continuations of the 61DM closure ledger,
executed. This kernel kills **K5** and **E5 = K̄5** over the OFFICIAL
predicate `IsErdosHajnalLowerBound` (verbatim from
google-deepmind/formal-conjectures @ 2207c54d, vendored in
DM61_Official.lean / DM61_Proof_A.lean):

    K5  = (⊤ : SimpleGraph (Fin 5))   — the 5-clique
    E5  = (⊥ : SimpleGraph (Fin 5))   — its complement, by transfer

**THEOREM K5** (K5_PROOF.md §3, engine-validated): every K5-free graph G
on n vertices satisfies α(G) ≥ w+1 where w is the integer fifth root of
n (w⁵ ≤ n < (w+1)⁵), for every n ≥ 1024; consequently the official
Erdős–Hajnal lower bound at **c = 1/5**:

    ∃ c > 0, IsErdosHajnalLowerBound (⊤ : SimpleGraph (Fin 5)) (fun n => (n:ℝ)^c)

**The instrument** (K5_PROOF.md §1–§2, Lemma REC + the tower): the
Erdős–Szekeres Ramsey ladder, built here as a custom module (BOSS's
authorization; Mathlib at this pin carries no finite binomial Ramsey
bound of this shape):

    ramsey_ladder : 2 ≤ r → 2 ≤ s → choose (r+s-2) (r-1) ≤ card β →
      (∃ K, r ≤ K.card ∧ IsClique K) ∨ (∃ I, s ≤ I.card ∧ IsIndepSet I)

by plain induction on r+s: peel a vertex v, split into N(v) and its
complement, Pascal's identity `choose_succ_succ'` paying the two
recursive bounds, the clique/independent transfers through
`G.comap Subtype.val`, and the v-extension on both sides.
The tower instantiation r = 5 gives R(5, t) ≤ C(t+3, 4) (K5_PROOF §2).

**The arithmetic spine** (all ℕ, zero real analysis on the count side):
w⁵ ≤ n < (w+1)⁵ (the integer fifth root as a Finset search); for
n ≥ 1024 = 2¹⁰ one has w ≥ 4, so (w+4)⁴ ≤ (3w)⁴ = 81w⁴ ≤ 24w⁵ ≤ 24n,
and the falling-factorial bound 24·C(w+4,4) ≤ (w+4)⁴ (the P2/P3/P4
ladder below) gives **C(w+4, 4) ≤ n** — the ladder's hypothesis.

**The finisher** (the green rpow template, DM61_Proof_A §4): from
n ≤ (w+1)⁵, `(n:ℝ)^(1/5) ≤ (w+1:ℝ)` via `Real.rpow_le_rpow` +
`rpow_natCast` + the REVERSED `rpow_mul`; then `w+1 ≤ indepNum` by
`IsIndepSet.card_le_indepNum` and the cast.

**E5** by the official-level complement transfer (green §5, attributed)
plus `(⊤ : SimpleGraph (Fin 5))ᶜ = ⊥`.

## ARSENAL BRIDGE (read-before-cite; both genuinely used below)
- `two_pow_pos` [Arsenal/CardinalWorlds.lean:420] — `0 < 2^j` — the
  threshold 1024 = 2¹⁰ positivity gate (`arsenal_threshold_K5`).
- `two_pow_ge2` [Arsenal/CardinalWorlds.lean:431] — `2 ≤ 2^j` (`j ≥ 1`)
  — the threshold's second component (4 = 2² ≤ 2¹⁰). Root namespace,
  read at their lines.

## HOUSE ATTRIBUTION
§0's official predicate, §8's complement transfer, and the finisher
template are the green kernel DM61_Proof_A.lean (W82-61A, CI-green on
run 45036892102), reused with attribution. The ladder, the integer fifth
root, the P2/P3/P4 falling-factorial bounds, the K5 packaging, and the
E5 instantiation are this lane's own.

## LAWS OF THE HOUSE
Zero sorry, zero native_decide; `#print axioms` on every headline (the
standard three only); CI (`kernel-dm-w84`, step 61DM-D) is the only Lean
verdict. Never compiled locally — GitHub Actions only.
-/
set_option maxHeartbeats 4000000
set_option maxRecDepth 131072

open scoped Classical
open Filter

namespace Erdos61D

/-! ## §0 THE OFFICIAL PREDICATE (verbatim from DM61_Official.lean) -/

/-- The official predicate, byte-identical to the DeepMind formal-conjectures
definition (`IsErdosHajnalLowerBound`, ErdosProblems/61.lean @ 2207c54d). -/
def IsErdosHajnalLowerBound {α : Type*} [Fintype α] [DecidableEq α]
  (H : SimpleGraph α) (f : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
    (¬∃ g : α ↪ Fin n, H = G.comap g) → G.indepNum ≥ f n ∨ G.cliqueNum ≥ f n

/-! ## §1 INTEGER POWER FLOORS (core-only) -/

/-- `1 ≤ m → 1 ≤ m ^ k` (core `Nat.mul_le_mul` induction; zero API risk). -/
theorem one_le_pow (m k : ℕ) (hm : 1 ≤ m) : 1 ≤ m ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Nat.pow_succ]
      have h := Nat.mul_le_mul ih hm
      simpa using h

/-- `1 ≤ m → m ≤ m ^ 5` (the root5 floor bookkeeping). -/
theorem le_pow5 (m : ℕ) (hm : 1 ≤ m) : m ≤ m ^ 5 := by
  have h1 : 1 ≤ m ^ 4 := one_le_pow m 4 hm
  have h2 : m ^ 5 = m ^ 4 * m := Nat.pow_succ m 4
  have h3 : 1 * m ≤ m ^ 4 * m := Nat.mul_le_mul h1 (le_refl m)
  rw [h2]
  simpa using h3

/-- Base-monomiality of powers (core `Nat.mul_le_mul` induction). -/
theorem pow_le_pow_of_le {a b : ℕ} (h : a ≤ b) : ∀ k : ℕ, a ^ k ≤ b ^ k
  | 0 => by norm_num
  | k + 1 => by
      rw [Nat.pow_succ, Nat.pow_succ]
      exact Nat.mul_le_mul (pow_le_pow_of_le h k) h

/-- `2 ^ 2 ≤ 2 ^ 10` (the threshold's second gate, core-only). -/
theorem four_le_1024 : (4:ℕ) ≤ 1024 := by
  calc (4:ℕ) = (2:ℕ) ^ 2 := by norm_num
    _ = (2:ℕ) ^ 2 * 1 := by ring
    _ ≤ (2:ℕ) ^ 2 * 2 ^ 8 := Nat.mul_le_mul_left _ (one_le_pow 2 8 (by norm_num))
    _ = (2:ℕ) ^ 10 := by rw [← Nat.pow_add]
    _ = 1024 := by norm_num

/-! ## §2 THE FALLING-FACTORIAL LADDER (P2/P3/P4, all ℕ) -/

/-- **P2.** `2 * C(m,2) ≤ m²` for `m ≥ 2`. -/
theorem two_mul_choose_two_le (m : ℕ) (hm : 2 ≤ m) : 2 * Nat.choose m 2 ≤ m ^ 2 := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm2 : 2 ≤ m
      · have hrec : Nat.choose (m + 1) 2 = Nat.choose m 1 + Nat.choose m 2 :=
          Nat.choose_succ_succ' m 1
        have h1 : Nat.choose m 1 = m := Nat.choose_one_right m
        have e2 : (m + 1) ^ 2 = m ^ 2 + 2 * m + 1 := by ring
        have hih := ih hm2
        omega
      · by_cases h2' : m + 1 = 2
        · rw [h2']; decide
        · have hsmall : Nat.choose (m + 1) 2 = 0 :=
            Nat.choose_eq_zero_of_lt (by omega)
          rw [hsmall]
          omega

/-- **P3.** `6 * C(m,3) ≤ m³` for `m ≥ 3`. -/
theorem six_mul_choose_three_le (m : ℕ) (hm : 3 ≤ m) : 6 * Nat.choose m 3 ≤ m ^ 3 := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm3 : 3 ≤ m
      · have hrec : Nat.choose (m + 1) 3 = Nat.choose m 2 + Nat.choose m 3 :=
          Nat.choose_succ_succ' m 2
        have e3 : (m + 1) ^ 3 = m ^ 3 + 3 * m ^ 2 + 3 * m + 1 := by ring
        have hP2 := two_mul_choose_two_le m (by omega)
        have hih := ih hm3
        have hsplit : 6 * (Nat.choose m 2 + Nat.choose m 3)
            = 6 * Nat.choose m 2 + 6 * Nat.choose m 3 := by ring
        omega
      · by_cases h3' : m + 1 = 3
        · rw [h3']; decide
        · have hsmall : Nat.choose (m + 1) 3 = 0 :=
            Nat.choose_eq_zero_of_lt (by omega)
          rw [hsmall]
          omega

/-- **P4.** `24 * C(m,4) ≤ m⁴` for `m ≥ 4` — the falling-factorial bound of
the K5 count side (K5_PROOF.md §3: C(t+3,4) = t(t+1)(t+2)(t+3)/24). -/
theorem four_and_twenty_choose_four_le (m : ℕ) (hm : 4 ≤ m) :
    24 * Nat.choose m 4 ≤ m ^ 4 := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm4 : 4 ≤ m
      · have hrec : Nat.choose (m + 1) 4 = Nat.choose m 3 + Nat.choose m 4 :=
          Nat.choose_succ_succ' m 3
        have e4 : (m + 1) ^ 4 = m ^ 4 + 4 * m ^ 3 + 6 * m ^ 2 + 4 * m + 1 := by ring
        have hP3 := six_mul_choose_three_le m (by omega)
        have hih := ih hm4
        have hsplit : 24 * (Nat.choose m 3 + Nat.choose m 4)
            = 24 * Nat.choose m 3 + 24 * Nat.choose m 4 := by ring
        omega
      · by_cases h4' : m + 1 = 4
        · rw [h4']; decide
        · have hsmall : Nat.choose (m + 1) 4 = 0 :=
            Nat.choose_eq_zero_of_lt (by omega)
          rw [hsmall]
          omega

/-! ## §3 THE INTEGER FIFTH ROOT (the Finset search) -/

/-- The integer fifth root: the greatest `t ≤ n` with `t⁵ ≤ n`. -/
def root5 (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun t => t ^ 5 ≤ n)).max'
    ⟨0, Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.zero_lt_succ n), by simp⟩⟩

theorem root5_pow_le (n : ℕ) : root5 n ^ 5 ≤ n := by
  have h : root5 n ∈ (Finset.range (n + 1)).filter (fun t => t ^ 5 ≤ n) :=
    Finset.max'_mem _ _
  simp only [Finset.mem_filter] at h
  exact h.2

theorem root5_lt_succ_pow (n : ℕ) : n < (root5 n + 1) ^ 5 := by
  by_contra hcon
  have hle : (root5 n + 1) ^ 5 ≤ n := by omega
  have hge : 1 ≤ root5 n + 1 := by omega
  have hsmall : root5 n + 1 ≤ n :=
    le_trans (le_pow5 (root5 n + 1) hge) hle
  have hmem : root5 n + 1 ∈
      (Finset.range (n + 1)).filter (fun t => t ^ 5 ≤ n) :=
    Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hle⟩
  have hmax : root5 n + 1 ≤ root5 n := Finset.le_max' _ _ hmem
  omega

/-! ## §4 THE RAMSEY LADDER (custom module; Lemma REC + Pascal) -/

section Ladder

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The 2-clique witness: an edge. -/
theorem two_clique {G : SimpleGraph α} {a b : α} (hab : G.Adj a b) :
    ∃ K : Finset α, K.card = 2 ∧ G.IsClique (↑K : Set α) := by
  refine ⟨{a, b}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [G.ne_of_adj hab] : a ∉ ({b} : Finset α)),
      Finset.card_singleton]
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with hxa | hxa <;> rcases hy with hyb | hyb
    · exact absurd (hxa.trans hyb.symm) hxy
    · rw [hxa, hyb]; exact hab
    · rw [hxa, hyb]; exact G.adj_symm hab
    · exact absurd (hxa.trans hyb.symm) hxy

/-- The edgeless graph is all-independent. -/
theorem all_indep_of_no_edge {G : SimpleGraph α}
    (hno : ∀ a b : α, ¬ G.Adj a b) :
    ∃ I : Finset α, I.card = Fintype.card α ∧ G.IsIndepSet (↑I : Set α) := by
  refine ⟨Finset.univ, Finset.card_univ, ?_⟩
  intro a _ b _ _
  exact hno a b

/-- A clique in the induced graph on `A`, extended by `v` (v adjacent to
all of `A`), is a clique in `G`. -/
theorem clique_extend (G : SimpleGraph α) (v : α) (A : Finset α)
    (hvA : ∀ w ∈ A, G.Adj v w) {K : Finset {x // x ∈ A}}
    (hK : (G.comap (Subtype.val : {x // x ∈ A} → α)).IsClique
      (↑K : Set {x // x ∈ A})) :
    G.IsClique (↑(insert v (K.image Subtype.val)) : Set α) ∧
    (insert v (K.image Subtype.val)).card = K.card + 1 := by
  have hvnot : v ∉ K.image Subtype.val := by
    intro hmem
    obtain ⟨x, hx1, hx2⟩ := Finset.mem_image.1 hmem
    have hadj : G.Adj v (Subtype.val x) := hvA x.1 x.2
    rw [hx2] at hadj
    exact G.irrefl hadj
  refine ⟨?_, by rw [Finset.card_insert_of_notMem hvnot, Finset.card_image_of_injOn
    (fun _ _ _ _ h => Subtype.ext h)]⟩
  intro a ha b hb hab
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
  rcases ha with ha1 | ha' <;> rcases hb with hb1 | hb'
  · exact absurd (ha1.trans hb1.symm) hab
  · rw [Finset.mem_image] at hb'
    obtain ⟨x, hx1, hx2⟩ := hb'
    have hadj : G.Adj v (Subtype.val x) := hvA x.1 x.2
    rw [hx2] at hadj
    rw [ha1]
    exact hadj
  · rw [Finset.mem_image] at ha'
    obtain ⟨x, hx1, hx2⟩ := ha'
    have hadj : G.Adj (Subtype.val x) v := G.adj_symm (hvA x.1 x.2)
    rw [hx2] at hadj
    rw [hb1]
    exact hadj
  · rw [Finset.mem_image] at ha' hb'
    obtain ⟨x, hx1, hx2⟩ := ha'
    obtain ⟨y, hy1, hy2⟩ := hb'
    have hxy : x ≠ y := by
      intro heq
      exact hab (by rw [← hx2, ← hy2, heq])
    have hcl := hK (Finset.mem_coe.2 hx1) (Finset.mem_coe.2 hy1) hxy
    rw [← hx2, ← hy2]
    exact hcl

/-- An independent set in the induced graph on `B`, extended by `v` (v
non-adjacent to all of `B`), is independent in `G`. -/
theorem indep_extend (G : SimpleGraph α) (v : α) (B : Finset α)
    (hvnotB : v ∉ B) (hvB : ∀ w ∈ B, ¬ G.Adj v w) {I : Finset {x // x ∈ B}}
    (hI : (G.comap (Subtype.val : {x // x ∈ B} → α)).IsIndepSet
      (↑I : Set {x // x ∈ B})) :
    G.IsIndepSet (↑(insert v (I.image Subtype.val)) : Set α) ∧
    (insert v (I.image Subtype.val)).card = I.card + 1 := by
  have hvnot : v ∉ I.image Subtype.val := by
    intro hmem
    obtain ⟨x, hx1, hx2⟩ := Finset.mem_image.1 hmem
    have hvin : v ∈ B := by
      rw [← hx2]
      exact x.2
    exact hvnotB hvin
  refine ⟨?_, by rw [Finset.card_insert_of_notMem hvnot, Finset.card_image_of_injOn
    (fun _ _ _ _ h => Subtype.ext h)]⟩
  intro a ha b hb hab
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
  rcases ha with ha1 | ha' <;> rcases hb with hb1 | hb'
  · exact absurd (ha1.trans hb1.symm) hab
  · rw [Finset.mem_image] at hb'
    obtain ⟨x, hx1, hx2⟩ := hb'
    have hnadj : ¬ G.Adj v (Subtype.val x) := hvB x.1 x.2
    rw [hx2] at hnadj
    rw [ha1]
    exact hnadj
  · rw [Finset.mem_image] at ha'
    obtain ⟨x, hx1, hx2⟩ := ha'
    have hnadj : ¬ G.Adj (Subtype.val x) v :=
      fun hadj => hvB x.1 x.2 (G.adj_symm hadj)
    rw [hx2] at hnadj
    rw [hb1]
    exact hnadj
  · rw [Finset.mem_image] at ha' hb'
    obtain ⟨x, hx1, hx2⟩ := ha'
    obtain ⟨y, hy1, hy2⟩ := hb'
    have hxy : x ≠ y := by
      intro heq
      exact hab (by rw [← hx2, ← hy2, heq])
    have hind := hI (Finset.mem_coe.2 hx1) (Finset.mem_coe.2 hy1) hxy
    rw [← hx2, ← hy2]
    exact hind

/-- A clique in an induced subgraph (via `comap Subtype.val`) is a clique. -/
theorem clique_image (G : SimpleGraph α) (A : Finset α)
    {K : Finset {x // x ∈ A}}
    (hK : (G.comap (Subtype.val : {x // x ∈ A} → α)).IsClique
      (↑K : Set {x // x ∈ A})) :
    G.IsClique (↑(K.image Subtype.val) : Set α) ∧
    (K.image Subtype.val).card = K.card := by
  refine ⟨?_, Finset.card_image_of_injOn (fun _ _ _ _ h => Subtype.ext h)⟩
  rintro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_image] at ha hb
  obtain ⟨x, hx1, hx2⟩ := ha
  obtain ⟨y, hy1, hy2⟩ := hb
  have hxy : x ≠ y := by
    intro heq
    exact hab (by rw [← hx2, ← hy2, heq])
  have hcl := hK (Finset.mem_coe.2 hx1) (Finset.mem_coe.2 hy1) hxy
  rw [← hx2, ← hy2]
  exact hcl

/-- An independent set in an induced subgraph is independent. -/
theorem indep_image (G : SimpleGraph α) (A : Finset α)
    {I : Finset {x // x ∈ A}}
    (hI : (G.comap (Subtype.val : {x // x ∈ A} → α)).IsIndepSet
      (↑I : Set {x // x ∈ A})) :
    G.IsIndepSet (↑(I.image Subtype.val) : Set α) ∧
    (I.image Subtype.val).card = I.card := by
  refine ⟨?_, Finset.card_image_of_injOn (fun _ _ _ _ h => Subtype.ext h)⟩
  rintro a ha b hb hab
  simp only [Finset.mem_coe, Finset.mem_image] at ha hb
  obtain ⟨x, hx1, hx2⟩ := ha
  obtain ⟨y, hy1, hy2⟩ := hb
  have hxy : x ≠ y := by
    intro heq
    exact hab (by rw [← hx2, ← hy2, heq])
  have hind := hI (Finset.mem_coe.2 hx1) (Finset.mem_coe.2 hy1) hxy
  rw [← hx2, ← hy2]
  exact hind

/-- **THE RAMSEY LADDER (Lemma REC + the tower, K5_PROOF.md §1–§2).**
For `r, s ≥ 2`: any graph on at least `C(r+s-2, r-1)` vertices carries a
clique of size `≥ r` or an independent set of size `≥ s`. Plain induction
on `r + s`; the peel splits at a vertex, Pascal (`choose_succ_succ'`)
pays both sides. -/
theorem ramsey_ladder :
    ∀ (N r s : ℕ), r + s = N → 2 ≤ r → 2 ≤ s →
      ∀ (β : Type) [Fintype β] [DecidableEq β] (G : SimpleGraph β),
        Nat.choose (r + s - 2) (r - 1) ≤ Fintype.card β →
        (∃ K : Finset β, r ≤ K.card ∧ G.IsClique (↑K : Set β)) ∨
        (∃ I : Finset β, s ≤ I.card ∧ G.IsIndepSet (↑I : Set β)) := by
  intro N
  induction N with
  | zero => intro r s hrs hr hs _ _ _ _; omega
  | succ N ih =>
      intro r s hrs hr hs β _ _ G hcard
      by_cases hr2 : r = 2
      · -- BASE r = 2: an edge is a 2-clique; edgeless is all-independent
        subst hr2
        have hchoose : Nat.choose s 1 = s := Nat.choose_one_right s
        rw [show 2 + s - 2 = s by omega, show 2 - 1 = 1 by omega, hchoose] at hcard
        by_cases hedge : ∃ a b : β, G.Adj a b
        · obtain ⟨a, b, hab⟩ := hedge
          obtain ⟨K, hKc, hK⟩ := two_clique hab
          exact Or.inl ⟨K, by omega, hK⟩
        · push_neg at hedge
          obtain ⟨I, hIc, hI⟩ := all_indep_of_no_edge hedge
          exact Or.inr ⟨I, by omega, hI⟩
      by_cases hs2 : s = 2
      · -- BASE s = 2 (dual): a non-edge is a 2-independent-set
        subst hs2
        rw [show r + 2 - 2 = r by omega] at hcard
        have hchoose : Nat.choose r (r - 1) = r := by
          obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
          rw [show r' + 1 - 1 = r' by omega]
          exact Nat.choose_succ_self_right r'
        rw [hchoose] at hcard
        by_cases hpair : ∃ a b : β, a ≠ b ∧ ¬ G.Adj a b
        · obtain ⟨a, b, hab, hnadj⟩ := hpair
          refine Or.inr ⟨{a, b}, ?_, ?_⟩
          · rw [Finset.card_insert_of_notMem (by simp [hab] : a ∉ ({b} : Finset β)),
              Finset.card_singleton]
          · intro x hx y hy hxy
            simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
            rcases hx with hxa | hxa <;> rcases hy with hyb | hyb
            · exact absurd (hxa.trans hyb.symm) hxy
            · rw [hxa, hyb]; exact hnadj
            · rw [hxa, hyb]; exact fun hadj => hnadj (G.adj_symm hadj)
            · exact absurd (hxa.trans hyb.symm) hxy
        · push_neg at hpair
          -- complete graph: univ is a clique of full size
          refine Or.inl ⟨Finset.univ, ?_, ?_⟩
          · rw [Finset.card_univ]; exact hcard
          · intro a _ b _ hab
            exact hpair a b hab
      -- PEEL: r, s ≥ 3
      obtain ⟨R, rfl⟩ : ∃ R, r = R + 2 := ⟨r - 2, by omega⟩
      obtain ⟨S, rfl⟩ : ∃ S, s = S + 2 := ⟨s - 2, by omega⟩
      -- Pascal: C(R+S+2, R+1) = C(R+S+1, R) + C(R+S+1, R+1)
      have hpascal : Nat.choose (R + S + 2) (R + 1)
          = Nat.choose (R + S + 1) R + Nat.choose (R + S + 1) (R + 1) := by
        have h := Nat.choose_succ_succ' (R + S + 1) R
        rw [show (R + S + 1) + 1 = R + S + 2 by omega] at h
        exact h
      -- the vertex (β nonempty: card ≥ C ≥ 1)
      have hcardpos : 0 < Fintype.card β :=
        Nat.lt_of_lt_of_le (Nat.choose_pos (by omega)) hcard
      obtain ⟨v⟩ : Nonempty β := Fintype.card_pos_iff.mp hcardpos
      -- the split: |A| + |B| + 1 = card β
      have hvA : v ∉ G.neighborFinset v := fun hmem =>
        G.irrefl ((G.mem_neighborFinset v v).mp hmem)
      have hcardSplit : (G.neighborFinset v).card +
          ((Finset.univ : Finset β) \ (insert v (G.neighborFinset v))).card + 1
          = Fintype.card β := by
        have h1 : (insert v (G.neighborFinset v) : Finset β).card
            = (G.neighborFinset v).card + 1 :=
          Finset.card_insert_of_notMem hvA
        have h2 : ((Finset.univ : Finset β) \ (insert v (G.neighborFinset v))).card
            + (insert v (G.neighborFinset v)).card = (Finset.univ : Finset β).card :=
          Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)
        rw [Finset.card_univ] at h2
        omega
      by_cases hAbig : Nat.choose (R + S + 1) R ≤ (G.neighborFinset v).card
      · -- A-side: recurse on N(v) with (R+1, S+2); extend the clique by v
        have hsub : Nat.choose ((R + 1) + (S + 2) - 2) ((R + 1) - 1) ≤
            Fintype.card {x // x ∈ G.neighborFinset v} := by
          rw [Fintype.card_coe]
          rw [show (R + 1) + (S + 2) - 2 = R + S + 1 by omega]
          rw [show (R + 1) - 1 = R by omega]
          exact hAbig
        obtain hIH := ih (R + 1) (S + 2) (by omega) (by omega)
          (by omega) {x // x ∈ G.neighborFinset v}
          (G.comap (Subtype.val : {x // x ∈ G.neighborFinset v} → β)) hsub
        rcases hIH with ⟨K, hKc, hK⟩ | ⟨I, hIc, hI⟩
        · obtain ⟨hcl, hcard'⟩ := clique_extend G v (G.neighborFinset v)
            (fun w hw => (G.mem_neighborFinset v w).mp hw) hK
          exact Or.inl ⟨insert v (K.image Subtype.val), by omega, hcl⟩
        · obtain ⟨hind, hcard''⟩ := indep_image G (G.neighborFinset v) hI
          exact Or.inr ⟨I.image Subtype.val, by omega, hind⟩
      · -- B-side: |B| ≥ C(R+S+1, R+1); recurse with (R+2, S+1); extend by v
        have hBbig : Nat.choose (R + S + 1) (R + 1)
            ≤ ((Finset.univ : Finset β) \ (insert v (G.neighborFinset v))).card := by
          rw [show (R + 2) + (S + 2) - 2 = R + S + 2 by omega,
              show (R + 2) - 1 = R + 1 by omega] at hcard
          omega
        have hsub : Nat.choose ((R + 2) + (S + 1) - 2) ((R + 2) - 1) ≤
            Fintype.card {x // x ∈
              ((Finset.univ : Finset β) \ (insert v (G.neighborFinset v)))} := by
          rw [Fintype.card_coe]
          rw [show (R + 2) + (S + 1) - 2 = R + S + 1 by omega]
          rw [show (R + 2) - 1 = R + 1 by omega]
          exact hBbig
        obtain hIH := ih (R + 2) (S + 1) (by omega) (by omega)
          (by omega) {x // x ∈
            ((Finset.univ : Finset β) \ (insert v (G.neighborFinset v)))}
          (G.comap (Subtype.val : {x // x ∈
            ((Finset.univ : Finset β) \ (insert v (G.neighborFinset v)))} → β)) hsub
        rcases hIH with ⟨K, hKc, hK⟩ | ⟨I, hIc, hI⟩
        · obtain ⟨hcl, hcard'⟩ := clique_image G
            ((Finset.univ : Finset β) \ (insert v (G.neighborFinset v))) hK
          exact Or.inl ⟨K.image Subtype.val, by omega, hcl⟩
        · have hvnotinB : v ∉ ((Finset.univ : Finset β) \ (insert v (G.neighborFinset v))) := by
            intro hmem
            exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_insert.2 (Or.inl rfl))
          obtain ⟨hind, hcard''⟩ := indep_extend G v
            ((Finset.univ : Finset β) \ (insert v (G.neighborFinset v)))
            hvnotinB
            (fun w hw => by
              have h1 := Finset.mem_sdiff.mp hw
              refine fun hadj => h1.2 (Finset.mem_insert.2
                (Or.inr ((G.mem_neighborFinset v w).mpr hadj)))) hI
          exact Or.inr ⟨insert v (I.image Subtype.val), by omega, hind⟩

end Ladder

/-! ## §5 THE K5-FREE BRIDGE (no induced K5 copy ↔ no 5-clique) -/

/-- Any pairwise-adjacent family carries the complete-graph copy (green
DM61_Proof_A `top_comap_of_pairwise`, reused with attribution). -/
theorem top_comap_of_pairwise {n k : ℕ} {G : SimpleGraph (Fin n)} (f : Fin k ↪ Fin n)
    (hadj : ∀ i j : Fin k, i ≠ j → G.Adj (f i) (f j)) :
    (⊤ : SimpleGraph (Fin k)) = G.comap f := by
  ext i j
  simp only [SimpleGraph.comap_adj, SimpleGraph.top_adj]
  constructor
  · intro hne; exact hadj i j hne
  · intro hadj'
    intro heq
    subst heq
    exact G.irrefl hadj'

/-- Shrink to an exact-cardinality subset (the in-kernel replacement for
`Finset.exists_smaller_set`, absent from Mathlib v4.33.0-rc2 — the custom
module BOSS authorized). -/
theorem exists_subset_card_le {α : Type} [DecidableEq α] :
    ∀ (S : Finset α) (m : ℕ), m ≤ S.card → ∃ T : Finset α, T ⊆ S ∧ T.card = m := by
  intro S
  refine Finset.induction_on S ?_ ?_
  · intro m hm
    refine ⟨∅, Finset.empty_subset _, ?_⟩
    have h0 : (∅ : Finset α).card = 0 := Finset.card_empty
    omega
  · intro a S haS ih m hm
    rw [Finset.card_insert_of_notMem haS] at hm
    by_cases h : m ≤ S.card
    · obtain ⟨T, hTsub, hTcard⟩ := ih m h
      refine ⟨T, fun x hx => Finset.mem_insert.2 (Or.inr (hTsub hx)), hTcard⟩
    · obtain ⟨T, hTsub, hTcard⟩ := ih S.card (le_refl _)
      refine ⟨insert a T, fun x hx =>
        Finset.mem_insert.2 ((Finset.mem_insert.1 hx).imp id hTsub), ?_⟩
      rw [Finset.card_insert_of_notMem (fun hc => haS (hTsub hc)), hTcard]
      omega

/-- **The bridge.** A clique of size ≥ 5 in an induced-K5-free graph is
impossible: a 5-subset carries the complete-graph copy. -/
theorem no_five_clique_of_no_induced {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : ¬∃ g : Fin 5 ↪ Fin n, (⊤ : SimpleGraph (Fin 5)) = G.comap g)
    (K : Finset (Fin n)) (hK : G.IsClique (↑K : Set (Fin n)))
    (hK5 : 5 ≤ K.card) : False := by
  obtain ⟨T, hTsub, hTcard⟩ : ∃ T : Finset (Fin n), T ⊆ K ∧ T.card = 5 :=
    exists_subset_card_le K 5 (by omega)
  have hTclique : G.IsClique (↑T : Set (Fin n)) :=
    fun a ha b hb hab => hK (hTsub ha) (hTsub hb) hab
  set e := Finset.orderIsoOfFin T hTcard with he
  have hadj : ∀ i j : Fin 5, i ≠ j → G.Adj (e i : Fin n) (e j : Fin n) := by
    intro i j hij
    have hmem_i : (e i : Fin n) ∈ T := Subtype.coe_prop (e i)
    have hmem_j : (e j : Fin n) ∈ T := Subtype.coe_prop (e j)
    have hne : (e i : Fin n) ≠ (e j : Fin n) := by
      intro heq
      exact hij (e.injective (Subtype.ext heq))
    exact hTclique (by simp [hmem_i]) (by simp [hmem_j]) hne
  have hcoeinj : Function.Injective (fun i : Fin 5 => (e i : Fin n)) := by
    intro i j hij
    apply e.injective
    exact Subtype.ext hij
  exact hG ⟨⟨fun i => (e i : Fin n), hcoeinj⟩, top_comap_of_pairwise _ hadj⟩

/-! ## §6 THE ARITHMETIC SPINE (all ℕ) + THE ARSENAL BRIDGE -/

/-- The Arsenal dyadic threshold at j = 10: `0 < 1024` (`two_pow_pos`
[CardinalWorlds.lean:420], read at its line — the green
`arsenal_threshold` pattern; the 4 ≤ 1024 gate is `four_le_1024`). -/
theorem arsenal_threshold_K5 : (0:ℕ) < 1024 := by
  have h1 : (0:ℕ) < 2^10 := two_pow_pos 10
  have e : (2:ℕ)^10 = 1024 := by norm_num
  rw [e] at h1
  exact h1

/-- **The count side.** For every `n ≥ 1024`, with `w = root5 n`:
`C(w+4, 4) ≤ n` — the ladder's hypothesis, by the pure-ℕ spine:
`(w+4)⁴ ≤ (3w)⁴ = 81w⁴ ≤ 24w⁵ ≤ 24n` and `24·C(w+4,4) ≤ (w+4)⁴`. -/
theorem choose_le_of_ge_1024 {n : ℕ} (hn : 1024 ≤ n) :
    Nat.choose (root5 n + 4) 4 ≤ n := by
  have hw5 : root5 n ^ 5 ≤ n := root5_pow_le n
  have hwlt : n < (root5 n + 1) ^ 5 := root5_lt_succ_pow n
  -- w ≥ 4 (else n < (w+1)^5 ≤ 4^5 = 1024)
  have hw4 : 4 ≤ root5 n := by
    by_contra hcon
    have hlt : (root5 n + 1) ^ 5 ≤ 4 ^ 5 := pow_le_pow_of_le (by omega) 5
    have h1024 : (4:ℕ) ^ 5 = 1024 := by norm_num
    omega
  -- the spine
  have h1 : root5 n + 4 ≤ 3 * root5 n := by omega
  have h2 : (root5 n + 4) ^ 4 ≤ (3 * root5 n) ^ 4 := pow_le_pow_of_le h1 4
  have h3 : (3 * root5 n) ^ 4 = 81 * (root5 n) ^ 4 := by
    rw [mul_pow]
    norm_num
  have h4 : 81 * (root5 n) ^ 4 ≤ 24 * (root5 n) ^ 5 := by
    have h81 : (81:ℕ) ≤ 24 * root5 n := by omega
    have hle : (root5 n) ^ 4 * 81 ≤ (root5 n) ^ 4 * (24 * root5 n) :=
      Nat.mul_le_mul_left _ h81
    have hrr : (root5 n) ^ 4 * (24 * root5 n) = 24 * (root5 n) ^ 5 := by ring
    calc 81 * (root5 n) ^ 4 = (root5 n) ^ 4 * 81 := by ring
      _ ≤ (root5 n) ^ 4 * (24 * root5 n) := hle
      _ = 24 * (root5 n) ^ 5 := hrr
  rw [← h3] at h4
  have h5 : 24 * (root5 n) ^ 5 ≤ 24 * n := Nat.mul_le_mul_left _ hw5
  have hP4 := four_and_twenty_choose_four_le (root5 n + 4) (by omega)
  have hfin : 24 * Nat.choose (root5 n + 4) 4 ≤ 24 * n :=
    le_trans hP4 (le_trans h2 (le_trans h4 h5))
  exact Nat.le_of_mul_le_mul_left hfin (by norm_num)

/-! ## §7 THE REAL FINISHER (the green rpow template) -/

/-- **The bound side.** For `n ≥ 1`: `(n:ℝ)^(1/5) ≤ (root5 n + 1 : ℝ)`,
from `n ≤ (root5 n + 1)⁵`, via `Real.rpow_le_rpow` + `rpow_natCast` +
the REVERSED `rpow_mul` (DM61_Proof_A's `rpow_quarter_le_sqrt`
template, reused with attribution). -/
theorem rpow_fifth_le_root5_succ (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ ((1:ℝ) / 5) ≤ ((root5 n + 1 : ℕ) : ℝ) := by
  have hwlt : n < (root5 n + 1) ^ 5 := root5_lt_succ_pow n
  have hbase : (n : ℝ) ≤ (((root5 n + 1 : ℕ) ^ 5 : ℕ) : ℝ) :=
    by exact_mod_cast (le_of_lt hwlt)
  have hstep1 : (n : ℝ) ^ ((1:ℝ)/5)
      ≤ (((root5 n + 1 : ℕ) ^ 5 : ℕ) : ℝ) ^ ((1:ℝ)/5) :=
    Real.rpow_le_rpow (by positivity) hbase (by positivity)
  have hcast : (((root5 n + 1 : ℕ) ^ 5 : ℕ) : ℝ)
      = ((root5 n + 1 : ℕ) : ℝ) ^ ((5:ℕ):ℝ) := by
    rw [Nat.cast_pow, Real.rpow_natCast]
  have hstep2 : (((root5 n + 1 : ℕ) : ℝ) ^ ((5:ℕ):ℝ)) ^ ((1:ℝ)/5)
      = ((root5 n + 1 : ℕ) : ℝ) ^ ((((5:ℕ):ℝ) * ((1:ℝ)/5))) :=
    (Real.rpow_mul (by positivity) ((5:ℕ):ℝ) ((1:ℝ)/5)).symm
  have h3 : (((5:ℕ):ℝ) * ((1:ℝ)/5)) = 1 := by ring
  rw [hcast] at hstep1
  rw [hstep2, h3, Real.rpow_one] at hstep1
  exact hstep1

/-! ## §8 THE HEADLINES -/

/-- **THEOREM K5 (official form).** The official Erdős–Hajnal lower bound
for H = K5 at c = 1/5 (K5_PROOF.md §3–§4; the threshold n ≥ 1024 rides
the eventually-filter). -/
theorem eh_K5 : IsErdosHajnalLowerBound (⊤ : SimpleGraph (Fin 5))
    (fun n => (n : ℝ) ^ ((1:ℝ)/5)) := by
  rw [IsErdosHajnalLowerBound, Filter.eventually_atTop]
  refine ⟨1024, ?_⟩
  intro n hn G hG
  -- w ≥ 1 (n ≥ 1024 forces root5 n ≥ 1, else n < (0+1)^5 = 1)
  have hr5pos : 1 ≤ root5 n := by
    rcases Nat.eq_zero_or_pos (root5 n) with h0 | hpos
    · exfalso
      have hw := root5_lt_succ_pow n
      rw [h0] at hw
      norm_num at hw
      omega
    · exact hpos
  -- the ladder at (5, w+1): C(w+4,4) ≤ card (Fin n)
  have hcount : Nat.choose (root5 n + 4) 4 ≤ Fintype.card (Fin n) := by
    have h := choose_le_of_ge_1024 hn
    have he : Fintype.card (Fin n) = n := by simp
    rw [he]
    exact h
  have hlad := ramsey_ladder (5 + (root5 n + 1)) 5 (root5 n + 1) (by omega)
    (by omega) (by omega) (Fin n) G (by
      rw [show 5 + (root5 n + 1) - 2 = root5 n + 4 by omega]
      rw [show 5 - 1 = 4 by omega]
      exact hcount)
  rcases hlad with ⟨K, hKc, hK⟩ | ⟨I, hIc, hI⟩
  · -- a 5+-clique is an induced K5 copy: contradiction
    exact (no_five_clique_of_no_induced hG K hK hKc).elim
  · -- the independent set of size ≥ w+1 finishes
    have hindep := SimpleGraph.IsIndepSet.card_le_indepNum (t := I) (tc := hI)
    have hrpow := rpow_fifth_le_root5_succ n (by omega)
    exact Or.inl (le_trans hrpow (Nat.cast_le.2 (le_trans hIc hindep)))

/-- The official-level complement transfer (green DM61_Proof_A §5,
reused with attribution). -/
theorem isEH_compl {α : Type*} [Fintype α] [DecidableEq α] {H : SimpleGraph α}
    {f : ℕ → ℝ} (h : IsErdosHajnalLowerBound H f) :
    IsErdosHajnalLowerBound Hᶜ f := by
  rw [IsErdosHajnalLowerBound] at h ⊢
  rw [Filter.eventually_atTop] at h ⊢
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro n hn G hG
  by_contra hcon
  push_neg at hcon
  have hGc : ¬∃ g : α ↪ Fin n, H = (Gᶜ).comap g := by
    rintro ⟨g, hg⟩
    refine hG ⟨g, ?_⟩
    have hcoe : ((Gᶜ).comap g)ᶜ = G.comap g := by
      ext x y
      by_cases hxy : x = y
      · subst hxy
        exact iff_of_false (by simp [SimpleGraph.compl_adj, SimpleGraph.comap_adj]) G.irrefl
      · simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj]
        have hginj : g x ≠ g y := fun heq => hxy (g.injective heq)
        constructor
        · rintro ⟨_, hne⟩
          by_contra hna
          exact hne ⟨hginj, hna⟩
        · intro hadj
          exact ⟨hxy, fun hp => hp.2 hadj⟩
    have h1 : Hᶜ = ((Gᶜ).comap g)ᶜ := by rw [hg]
    rw [hcoe] at h1
    exact h1
  have happ := hN n hn Gᶜ hGc
  rw [SimpleGraph.indepNum_compl] at happ
  have hcl : Gᶜ.cliqueNum = G.indepNum := by
    have h := SimpleGraph.indepNum_compl (G := Gᶜ)
    rw [compl_compl] at h
    exact h.symm
  rw [hcl] at happ
  rcases happ with h' | h'
  · linarith
  · linarith

/-- **E5 = K̄5** by the complement transfer + `(⊤ : SimpleGraph (Fin 5))ᶜ = ⊥`. -/
theorem eh_E5 : IsErdosHajnalLowerBound (⊥ : SimpleGraph (Fin 5))
    (fun n => (n : ℝ) ^ ((1:ℝ)/5)) := by
  have hcoe : (⊥ : SimpleGraph (Fin 5)) = (⊤ : SimpleGraph (Fin 5))ᶜ := by
    ext a b; simp
  rw [hcoe]
  exact isEH_compl eh_K5

/-! ## §9 THE BOARD -/

/-- **THE K5/E5 FAMILY THEOREM.** Both members of the 5-vertex world's
first pair (K5, E5 = K̄5) satisfy the official Erdős–Hajnal statement at
`c = 1/5`, over the official predicate (verbatim DeepMind @ 2207c54d). -/
theorem erdos_61_k5_e5 : ∃ c > (0:ℝ),
    IsErdosHajnalLowerBound (⊤ : SimpleGraph (Fin 5)) (fun n => (n : ℝ) ^ c) ∧
    IsErdosHajnalLowerBound (⊥ : SimpleGraph (Fin 5)) (fun n => (n : ℝ) ^ c) :=
  ⟨(1:ℝ)/5, by positivity, eh_K5, eh_E5⟩

#print axioms Erdos61D.ramsey_ladder
#print axioms Erdos61D.choose_le_of_ge_1024
#print axioms Erdos61D.rpow_fifth_le_root5_succ
#print axioms Erdos61D.eh_K5
#print axioms Erdos61D.eh_E5
#print axioms Erdos61D.erdos_61_k5_e5
#print axioms Erdos61D.arsenal_threshold_K5
#print axioms Erdos61D.four_and_twenty_choose_four_le

#eval "DM61D_K5_GREEN"

end Erdos61D
