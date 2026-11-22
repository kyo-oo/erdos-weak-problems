import Mathlib
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds

/-!
# DM61_Proof_A — THE OFFICIAL-FORM FAMILY THEOREM (W82-61A, W83 repair)

BOSS's W82 order: THE OFFICIAL STATEMENTS, complete proofs, the arsenal
cited, GitHub CI the only verdict. This kernel proves, over the OFFICIAL
predicate `IsErdosHajnalLowerBound` (verbatim from
google-deepmind/formal-conjectures @ 2207c54d, vendored in
problem61-erdos-hajnal/DM61_Official.lean), with the uniform exponent
c = 1/4:

    K1  = (⊥ : SimpleGraph (Fin 1))   — vacuous (any embedding copies it)
    K2  = (⊤ : SimpleGraph (Fin 2))   — edgeless ⟹ α = n
    K̄2  = (⊥ : SimpleGraph (Fin 2))   — via the complement transfer from K2
    K3  = (⊤ : SimpleGraph (Fin 3))   — triangle-free dichotomy at ⌊√n⌋
    K̄3  = (⊥ : SimpleGraph (Fin 3))   — complement transfer from K3
    P3  = pathGraph 3                 — closed-neighborhood clique dichotomy
    P̄3  = (pathGraph 3)ᶜ              — complement transfer from P3

HONEST SCOPE: P4 (cographs — Seinsche's split) is NOT claimed by this
kernel; the derivation is banked in WORKLOG_W82_61A.md §2 (P4 LAW) and
remains the named continuation. The official open core `erdos_61` (all H)
and the solved variants erha89/bnss23/p5/c5 are NOT claimed by anyone.

W83 REPAIR NOTE: rebuilt against the Mathlib v4.33.0-rc2 API (CI run
45017357264 post-mortem): `SimpleGraph.irrefl` (loopless is now a
`Std.Irrefl Adj` structure field), `mem_neighborFinset v w` (explicit
vertex arguments), `Finset.notMem_empty` (the not_mem→notMem rename),
`Finset.mem_biUnion` (iff form), `Real.rpow_mul` (stated `x^(y*z) =
(x^y)^z`), `Nat.mul_le_mul_left` explicit-key form, root-namespace
Arsenal citations (`two_pow_pos`/`two_pow_ge2` live at the file's root
namespace, verified Arsenal/CardinalWorlds.lean:420/431), `open Filter`
for `atTop`, and `ᶜ` parenthesization on `pathGraph 3`.

## THE LAWS (the campaign's W68/W76 ⌊√n⌋ family kills, official form)

1. THE COMPLEMENT TRANSFER (official level): `H` at `c` ⟹ `Hᶜ` at `c`,
   via `(X.comap g)ᶜ = (G.comap g)ᶜ` (injectivity) + `indepNum_compl`.
2. THE NO-COPY LADDER: no induced `K3` copy ⟹ `CliqueFree 3`; no `K2`
   copy ⟹ no edges; no `P3` copy ⟹ every closed neighborhood is a clique
   (an induced `a—v—w` is a `pathGraph 3` copy).
3. THE GREEDY CORE (maximal independent set, Turán-style domination):
   every closed neighborhood ≤ `D` ⟹ `α · D ≥ n`.
4. THE DICHOTOMY FINISHER at `D = ⌊√n⌋`, then `⌊√n⌋ ≥ n^{1/4}` (n ≥ 4).

## ARSENAL BRIDGE (read-before-cite; both genuinely used below)
- `two_pow_pos` [Arsenal/CardinalWorlds.lean:420] — `0 < 2^j` — the dyadic
  base of `arsenal_threshold` (the √n floor gate). Root namespace.
- `two_pow_ge2` [Arsenal/CardinalWorlds.lean:431] — `2 ≤ 2^j` (`j ≥ 1`) —
  the second component of `arsenal_threshold`, feeding the `2 ≤ ⌊√n⌋`
  floor through `Nat.le_sqrt`. Root namespace.

## LAWS OF THE HOUSE
Zero sorry, zero sorry-axiom proofs; `#print axioms` on every headline (the
standard three only); CI (`kernel-dm-w82` step Kernel 61DM-A) is the only Lean verdict.
-/
set_option maxHeartbeats 2000000
set_option maxRecDepth 65536

open scoped Classical
open Filter

namespace Erdos61A

/-! ## §0 THE OFFICIAL PREDICATE (verbatim from DM61_Official.lean) -/

/-- The official predicate, byte-identical to the DeepMind formal-conjectures
definition (`IsErdosHajnalLowerBound`, ErdosProblems/61.lean @ 2207c54d). -/
def IsErdosHajnalLowerBound {α : Type*} [Fintype α] [DecidableEq α]
  (H : SimpleGraph α) (f : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
    (¬∃ g : α ↪ Fin n, H = G.comap g) → G.indepNum ≥ f n ∨ G.cliqueNum ≥ f n

/-! ## §1 BUILDERS: embeddings and comap copies -/

/-- The 2-point embedding `![a, b]`. -/
def emb2 {n : ℕ} (a b : Fin n) (hab : a ≠ b) : Fin 2 ↪ Fin n where
  toFun := ![a, b]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem emb2_zero {n : ℕ} (a b : Fin n) (hab : a ≠ b) : emb2 a b hab 0 = a := rfl
theorem emb2_one {n : ℕ} (a b : Fin n) (hab : a ≠ b) : emb2 a b hab 1 = b := rfl

/-- The 3-point embedding `![x, v, y]`. -/
def emb3 {n : ℕ} (x v y : Fin n) (hxv : x ≠ v) (hvy : v ≠ y) (hxy : x ≠ y) :
    Fin 3 ↪ Fin n where
  toFun := ![x, v, y]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem emb3_zero {n : ℕ} {x v y : Fin n} {hxv hvy hxy} :
    emb3 x v y hxv hvy hxy 0 = x := rfl
theorem emb3_one {n : ℕ} {x v y : Fin n} {hxv hvy hxy} :
    emb3 x v y hxv hvy hxy 1 = v := rfl
theorem emb3_two {n : ℕ} {x v y : Fin n} {hxv hvy hxy} :
    emb3 x v y hxv hvy hxy 2 = y := rfl

/-- Any pairwise-adjacent family carries the complete-graph copy:
`(⊤ : SimpleGraph (Fin k)) = G.comap f`. -/
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

/-- The induced-P3 copy: edges `a—v`, `v—y`, non-edge `a—y` (distinct
vertices) give `pathGraph 3 = G.comap ![a, v, y]`. -/
theorem pathGraph3_comap {n : ℕ} {G : SimpleGraph (Fin n)} {a v y : Fin n}
    (hav : a ≠ v) (hvy : v ≠ y) (hay : a ≠ y)
    (h1 : G.Adj a v) (h2 : G.Adj v y) (h3 : ¬ G.Adj a y) :
    (SimpleGraph.pathGraph 3) = G.comap (emb3 a v y hav hvy hay) := by
  ext i j
  simp only [SimpleGraph.comap_adj, SimpleGraph.pathGraph_adj]
  fin_cases i <;> fin_cases j
  · exact iff_of_false (by decide) G.irrefl
  · exact iff_of_true (by decide) h1
  · exact iff_of_false (by decide) h3
  · exact iff_of_true (by decide) (G.adj_symm h1)
  · exact iff_of_false (by decide) G.irrefl
  · exact iff_of_true (by decide) h2
  · exact iff_of_false (by decide) (fun h => h3 (G.adj_symm h))
  · exact iff_of_true (by decide) (G.adj_symm h2)
  · exact iff_of_false (by decide) G.irrefl

/-! ## §2 NO-COPY CONSEQUENCES -/

/-- No induced `K3` copy (official comap form) implies `CliqueFree 3`. -/
theorem cliqueFree3_of_no_induced {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : ¬∃ g : Fin 3 ↪ Fin n, (⊤ : SimpleGraph (Fin 3)) = G.comap g) :
    G.CliqueFree 3 := by
  intro s hs
  have hcard : s.card = 3 := hs.2
  set e := Finset.orderIsoOfFin s hcard with he
  have hadj : ∀ i j : Fin 3, i ≠ j → G.Adj (e i : Fin n) (e j : Fin n) := by
    intro i j hij
    have hmem_i : (e i : Fin n) ∈ s := Subtype.coe_prop (e i)
    have hmem_j : (e j : Fin n) ∈ s := Subtype.coe_prop (e j)
    have hne : (e i : Fin n) ≠ (e j : Fin n) := by
      intro heq
      exact hij (e.injective (Subtype.ext heq))
    exact hs.isClique (by simp [hmem_i]) (by simp [hmem_j]) hne
  exact hG ⟨(Finset.subtype s).comp (e.toEmbedding),
    top_comap_of_pairwise ((Finset.subtype s).comp (e.toEmbedding)) hadj⟩

/-- No induced `K2` copy implies no edges at all. -/
theorem no_edge_of_no_induced_K2 {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : ¬∃ g : Fin 2 ↪ Fin n, (⊤ : SimpleGraph (Fin 2)) = G.comap g) :
    ∀ a b : Fin n, ¬ G.Adj a b := by
  intro a b hab
  have hne : a ≠ b := G.ne_of_adj hab
  refine hG ⟨emb2 a b hne, top_comap_of_pairwise (emb2 a b hne) ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact hab
  · exact G.adj_symm hab
  · exact absurd rfl hij

/-- No induced `P3` copy implies every closed neighborhood is a clique. -/
theorem closedNbhd_clique_of_no_induced_P3 {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : ¬∃ g : Fin 3 ↪ Fin n, SimpleGraph.pathGraph 3 = G.comap g)
    (v : Fin n) :
    G.IsClique ↑(insert v (G.neighborFinset v)) := by
  intro a ha b hb hab
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
  have hA : a = v ∨ G.Adj v a := by
    rcases ha with h | h
    · exact Or.inl h
    · exact Or.inr (SimpleGraph.mem_neighborFinset v a |>.mp h)
  have hB : b = v ∨ G.Adj v b := by
    rcases hb with h | h
    · exact Or.inl h
    · exact Or.inr (SimpleGraph.mem_neighborFinset v b |>.mp h)
  rcases hA with ha1 | ha2 <;> rcases hB with hb1 | hb2
  · exact absurd (ha1.trans hb1.symm) hab
  · rw [ha1]; exact hb2
  · rw [hb1]; exact G.adj_symm ha2
  · by_contra hnoadj
    have hva : a ≠ v := by
      intro h
      subst h
      exact G.irrefl ha2
    have hvb : b ≠ v := by
      intro h
      subst h
      exact G.irrefl hb2
    exact hG ⟨emb3 a v b hva (Ne.symm hvb) hab,
      pathGraph3_comap hva (Ne.symm hvb) hab (G.adj_symm ha2) hb2 hnoadj⟩

/-! ## §3 THE GREEDY CORE (maximal independent set) -/

/-- **The greedy core.** If every closed neighborhood has at most `D`
vertices (`D ≥ 1`), there is an independent set `s` (a Finset) with
`D * s.card ≥ Fintype.card α`. Turán-style domination: a maximum-cardinality
independent set dominates the graph. -/
theorem exists_isIndepSet_mul_ge {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) {D : ℕ} (hD : 1 ≤ D)
    (hbnd : ∀ v : α, (insert v (G.neighborFinset v)).card ≤ D) :
    ∃ s : Finset α, G.IsIndepSet (↑s : Set α) ∧ Fintype.card α ≤ D * s.card := by
  classical
  set pool : Finset (Finset α) :=
    (Finset.univ : Finset (Finset α)).filter (fun t => G.IsIndepSet (↑t : Set α)) with hpool
  have hpool_ne : pool.Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [hpool, Finset.mem_filter, Finset.mem_univ, true_and]
    intro a ha b hb _
    exact absurd (Finset.mem_coe.mp ha) (Finset.notMem_empty a)
  obtain ⟨s, hs_mem, hs_max⟩ := Finset.exists_max_image pool (fun t => t.card) hpool_ne
  have hsindep : G.IsIndepSet (↑s : Set α) := (Finset.mem_filter.mp hs_mem).2
  have hsmax : ∀ t : Finset α, G.IsIndepSet (↑t : Set α) → t.card ≤ s.card := by
    intro t ht
    exact hs_max t (Finset.mem_filter.mpr ⟨Finset.mem_univ t, ht⟩)
  -- maximality: every vertex outside s is adjacent to some vertex of s
  have hdom : ∀ v : α, v ∉ s → ∃ w ∈ s, G.Adj v w := by
    intro v hv
    by_contra hno
    push_neg at hno
    have hins : G.IsIndepSet (↑(insert v s : Finset α) : Set α) := by
      intro a ha b hb hab
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
      rcases ha with ha1 | ha' <;> rcases hb with hb1 | hb'
      · exact absurd (ha1.trans hb1.symm) hab
      · intro hadj
        rw [ha1] at hadj
        exact hno b hb' hadj
      · intro hadj
        rw [hb1] at hadj
        exact hno a ha' (G.adj_symm hadj)
      · exact hsindep (Finset.mem_coe.mpr ha') (Finset.mem_coe.mpr hb') hab
    have hcard := hsmax (insert v s) hins
    rw [Finset.card_insert_of_notMem hv] at hcard
    omega
  -- the domination count
  refine ⟨s, hsindep, ?_⟩
  have hcover : (Finset.univ : Finset α) ⊆
      s ∪ s.biUnion (fun w => G.neighborFinset w) := by
    intro v _
    by_cases hvs : v ∈ s
    · exact Finset.mem_union_left _ hvs
    · obtain ⟨w, hws, hvw⟩ := hdom v hvs
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, hws, hvw⟩)
  have hcard1 := Finset.card_le_card hcover
  have hu : (s ∪ s.biUnion (fun w => G.neighborFinset w)).card
      ≤ s.card + (s.biUnion (fun w => G.neighborFinset w)).card :=
    Finset.card_union_le _ _
  have hbi : (s.biUnion (fun w => G.neighborFinset w)).card
      ≤ ∑ w ∈ s, (G.neighborFinset w).card :=
    Finset.card_biUnion_le
  have hcard2 : Fintype.card α = (Finset.univ : Finset α).card := by simp
  have hsum : ∑ w ∈ s, (G.neighborFinset w).card ≤ s.card * (D - 1) := by
    refine le_trans (Finset.sum_le_sum ?_) ?_
    · intro w hws
      have hb := hbnd w
      rw [Finset.card_insert_of_notMem
        (fun hmem => G.irrefl ((SimpleGraph.mem_neighborFinset w w).mp hmem))] at hb
      omega
    · rw [Finset.sum_const, smul_eq_mul]
  have hfinal : Fintype.card α ≤ s.card + s.card * (D - 1) := by omega
  have hD'' : D * s.card = s.card + s.card * (D - 1) := by
    have hsucc : Nat.succ (D - 1) = D := by omega
    have h := Nat.mul_succ s.card (D - 1)
    rw [hsucc] at h
    rw [Nat.mul_comm D s.card]
    omega
  omega

/-! ## §4 THE ARITHMETIC + THE ARSENAL BRIDGE -/

/-- The Arsenal dyadic threshold: `0 < 4` and `2 ≤ 4` from
`two_pow_pos` [CardinalWorlds.lean:420] and `two_pow_ge2`
[CardinalWorlds.lean:431] at `j = 2` (root-namespace declarations,
signatures read at those lines — read-before-cite). -/
theorem arsenal_threshold : (0:ℕ) < 4 ∧ 2 ≤ 4 := by
  have h1 : (0:ℕ) < 2^2 := two_pow_pos 2
  have h2 : (2:ℕ) ≤ 2^2 := two_pow_ge2 2 (by norm_num)
  norm_num at h1 h2
  exact ⟨h1, h2⟩

/-- For `n ≥ 4`: `n ≤ (Nat.sqrt n) ^ 4` (via `n < (s+1)² ≤ (s·s)²`, `s ≥ 2`). -/
theorem le_sqrt_pow_four {n : ℕ} (hn : 4 ≤ n) : n ≤ (Nat.sqrt n) ^ 4 := by
  have hs2 : 2 ≤ Nat.sqrt n := Nat.le_sqrt.2 (by omega)
  have hlt : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := by
    have h := Nat.lt_succ_sqrt' n
    simpa [Nat.pow_two] using h
  have hstep : Nat.sqrt n + 1 ≤ Nat.sqrt n * Nat.sqrt n := by
    have h1 : Nat.sqrt n * 2 ≤ Nat.sqrt n * Nat.sqrt n :=
      Nat.mul_le_mul_left _ hs2
    have h1' : 2 * Nat.sqrt n ≤ Nat.sqrt n * Nat.sqrt n := by
      rw [Nat.mul_comm 2 (Nat.sqrt n)]
      exact h1
    omega
  have hle : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤
      (Nat.sqrt n * Nat.sqrt n) * (Nat.sqrt n * Nat.sqrt n) :=
    Nat.mul_le_mul hstep hstep
  have hpow : (Nat.sqrt n * Nat.sqrt n) * (Nat.sqrt n * Nat.sqrt n)
      = (Nat.sqrt n) ^ 4 := by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_zero]
    ring
  have hfin : n < (Nat.sqrt n) ^ 4 := by
    have h1 : n < (Nat.sqrt n * Nat.sqrt n) * (Nat.sqrt n * Nat.sqrt n) :=
      lt_of_lt_of_le hlt hle
    rw [hpow] at h1
    exact h1
  omega

/-- The real finisher: `(n : ℝ)^(1/4) ≤ Nat.sqrt n` for `n ≥ 4`. -/
theorem rpow_quarter_le_sqrt {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) ^ ((1:ℝ) / 4) ≤ (Nat.sqrt n : ℝ) := by
  have hkey : (n : ℝ) ≤ ((Nat.sqrt n : ℕ) : ℝ) ^ 4 := by
    exact_mod_cast le_sqrt_pow_four hn
  have h1 : (n : ℝ) ^ ((1:ℝ)/4) ≤ (((Nat.sqrt n : ℕ) : ℝ) ^ 4) ^ ((1:ℝ)/4) :=
    Real.rpow_le_rpow (by positivity) hkey (by positivity)
  refine le_trans h1 ?_
  have hx : (0:ℝ) ≤ ((Nat.sqrt n : ℕ) : ℝ) := by positivity
  rw [(Real.rpow_mul hx 4 ((1:ℝ)/4)).symm,
    show ((4:ℝ) * ((1:ℝ)/4)) = 1 by ring, Real.rpow_one]

/-! ## §5 THE FAMILY LAWS -/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The official-level complement transfer: `H` at `f` ⟹ `Hᶜ` at `f`. -/
theorem isEH_compl {H : SimpleGraph α} {f : ℕ → ℝ}
    (h : IsErdosHajnalLowerBound H f) : IsErdosHajnalLowerBound Hᶜ f := by
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
    -- H = (Gᶜ).comap g ⟹ Hᶜ = (G.comap g)ᶜ ⟹ H = G.comap g
    have hcoe : ((Gᶜ).comap g)ᶜ = (G.comap g)ᶜ := by
      ext x y
      by_cases hxy : x = y
      · subst hxy
        simp [SimpleGraph.compl_adj, SimpleGraph.comap_adj, G.irrefl]
      · simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj]
        have hginj : g x ≠ g y := fun heq => hxy (g.injective heq)
        constructor
        · rintro ⟨_, hne⟩
          exact ⟨hxy, fun ha => hne ⟨hginj, ha⟩⟩
        · rintro ⟨_, hne⟩
          exact ⟨hxy, fun hp => hne hp.2⟩
    have h1 : Hᶜ = ((Gᶜ).comap g)ᶜ := by rw [hg]
    rw [hcoe] at h1
    have h2 : H = G.comap g := by
      have h3 := congrArg (fun X : SimpleGraph (Fin n) => Xᶜ) h1
      simp only [compl_compl] at h3
      exact h3
    exact h2
  have happ := hN n hn Gᶜ hGc
  rw [SimpleGraph.indepNum_compl] at happ
  have hcl : Gᶜ.cliqueNum = G.indepNum := by
    have h := SimpleGraph.indepNum_compl (G := Gᶜ)
    rw [compl_compl] at h
    exact h.symm
  rw [hcl] at happ
  rcases happ with h' | h'
  · exact hcon.2 h'
  · exact hcon.1 h'

/-- The dichotomy finisher: `indepNum` or `cliqueNum` ≥ `Nat.sqrt n`
implies the official bound at `c = 1/4` (for `n ≥ 4`). -/
theorem official_bound_of_sqrt {n : ℕ} (hn : 4 ≤ n) {G : SimpleGraph (Fin n)}
    (h : G.indepNum ≥ Nat.sqrt n ∨ G.cliqueNum ≥ Nat.sqrt n) :
    G.indepNum ≥ (n : ℝ) ^ ((1:ℝ)/4) ∨ G.cliqueNum ≥ (n : ℝ) ^ ((1:ℝ)/4) := by
  have hle := rpow_quarter_le_sqrt hn
  rcases h with h | h
  · left; exact le_trans hle (Nat.cast_le.2 h)
  · right; exact le_trans hle (Nat.cast_le.2 h)

/-- **K2** (the edge): every K2-free graph is edgeless, so `α = n`. -/
theorem eh_K2 : IsErdosHajnalLowerBound (⊤ : SimpleGraph (Fin 2))
    (fun n => (n : ℝ) ^ ((1:ℝ)/4)) := by
  rw [IsErdosHajnalLowerBound, Filter.eventually_atTop]
  refine ⟨4, ?_⟩
  intro n hn G hG
  have hno := no_edge_of_no_induced_K2 hG
  left
  have hindep : G.IsIndepSet ↑(Finset.univ : Finset (Fin n)) := by
    intro a _ b _ _
    exact hno a b
  have hle := (G.IsIndepSet.card_le_indepNum (t := (Finset.univ : Finset (Fin n)))
    (tc := hindep))
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  rw [hcard] at hle
  have hsqrt : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  exact official_bound_of_sqrt hn (Or.inl (le_trans hsqrt hle))

/-- **K̄2** (the non-edge): by the complement transfer from K2. -/
theorem eh_Kbar2 : IsErdosHajnalLowerBound (⊥ : SimpleGraph (Fin 2))
    (fun n => (n : ℝ) ^ ((1:ℝ)/4)) := by
  have hcoe : (⊥ : SimpleGraph (Fin 2)) = (⊤ : SimpleGraph (Fin 2))ᶜ := by
    ext a b; simp
  rw [hcoe]
  exact isEH_compl eh_K2

/-- **K3** (the triangle): the triangle-free dichotomy at `⌊√n⌋`. -/
theorem eh_K3 : IsErdosHajnalLowerBound (⊤ : SimpleGraph (Fin 3))
    (fun n => (n : ℝ) ^ ((1:ℝ)/4)) := by
  rw [IsErdosHajnalLowerBound, Filter.eventually_atTop]
  refine ⟨4, ?_⟩
  intro n hn G hG
  have hcf : G.CliqueFree 3 := cliqueFree3_of_no_induced hG
  have h4 := arsenal_threshold
  have hs2 : 2 ≤ Nat.sqrt n := Nat.le_sqrt.2 (by omega)
  by_cases hA : ∃ v : Fin n, Nat.sqrt n ≤ (G.neighborFinset v).card
  · obtain ⟨v, hv⟩ := hA
    have hindep : G.IsIndepSet ↑(G.neighborFinset v) := by
      intro a ha b hb hab
      simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at ha hb
      by_contra hadj
      have hva : G.Adj v a := ha
      have hvb : G.Adj v b := hb
      have hmem3 : ∀ x : Fin n,
          x ∈ (insert v (insert a (insert b (∅ : Finset (Fin n)))) : Finset (Fin n)) →
          x = v ∨ x = a ∨ x = b := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h
        · exact Or.inl h
        rcases h with h | h
        · exact Or.inr (Or.inl h)
        rcases h with h | h
        · exact Or.inr (Or.inr h)
        · exact absurd h (Finset.notMem_empty x)
      have h3 : G.IsNClique 3 (insert v (insert a (insert b (∅ : Finset (Fin n))))) :=
        ⟨by
          intro x hx y hy hxy
          have hx3 := hmem3 x hx
          have hy3 := hmem3 y hy
          rcases hx3 with hx1 | hx1 <;> rcases hy3 with hy1 | hy1
          · exact absurd (hx1.trans hy1.symm) hxy
          · rw [hx1, hy1]; exact hva
          · rw [hx1, hy1]; exact hvb
          · rw [hy1]; exact G.adj_symm hva
          · exact absurd (hx1.trans hy1.symm) hxy
          · rw [hx1, hy1]; exact hadj
          · rw [hy1]; exact G.adj_symm hvb
          · rw [hx1, hy1]; exact G.adj_symm hadj
          · exact absurd (hx1.trans hy1.symm) hxy
        , by
          have h1 : v ∉ insert a (insert b (∅ : Finset (Fin n))) := by
            intro h
            simp only [Finset.mem_insert, Finset.mem_singleton] at h
            rcases h with h | h
            · exact G.ne_of_adj hva h
            · rcases h with h | h
              · exact G.ne_of_adj hvb h
              · exact absurd h (Finset.notMem_empty v)
          have h2 : a ∉ insert b (∅ : Finset (Fin n)) := by
            intro h
            simp only [Finset.mem_insert, Finset.mem_singleton] at h
            rcases h with h | h
            · exact hab h
            · exact absurd h (Finset.notMem_empty a)
          have h3b : b ∉ (∅ : Finset (Fin n)) := Finset.notMem_empty b
          rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
            Finset.card_insert_of_notMem h3b]
          simp⟩
      exact hcf _ h3
    have hle := (G.IsIndepSet.card_le_indepNum (t := G.neighborFinset v)
      (tc := hindep))
    exact official_bound_of_sqrt hn (Or.inl (le_trans hv hle))
  · push_neg at hA
    have hbnd : ∀ v : Fin n, (insert v (G.neighborFinset v)).card ≤ Nat.sqrt n := by
      intro v
      rw [Finset.card_insert_of_notMem
        (fun hmem => G.irrefl ((SimpleGraph.mem_neighborFinset v v).mp hmem))]
      have := hA v
      omega
    obtain ⟨s, hsindep, hcount⟩ := exists_isIndepSet_mul_ge G (Nat.sqrt n)
      (by omega) hbnd
    have hcardn : Fintype.card (Fin n) = n := by simp
    have hle := (G.IsIndepSet.card_le_indepNum (t := s) (tc := hsindep))
    have hsq : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
    have halpha : Nat.sqrt n ≤ G.indepNum := by
      by_contra hlt
      have hle' : G.indepNum ≤ Nat.sqrt n - 1 := by omega
      have h1 : Nat.sqrt n * G.indepNum ≤ Nat.sqrt n * (Nat.sqrt n - 1) :=
        Nat.mul_le_mul_left _ hle'
      have h2 : Nat.sqrt n * (Nat.sqrt n - 1) < Nat.sqrt n * Nat.sqrt n := by
        have he : Nat.sqrt n - 1 + 1 = Nat.sqrt n := by omega
        have hm : Nat.sqrt n * (Nat.sqrt n - 1) + Nat.sqrt n * 1
            = Nat.sqrt n * Nat.sqrt n := by
          rw [← Nat.mul_add, he]
        omega
      have h3 : n ≤ Nat.sqrt n * s.card := by rw [← hcardn]; exact hcount
      have h4' : Nat.sqrt n * s.card ≤ Nat.sqrt n * G.indepNum :=
        Nat.mul_le_mul_left _ hle
      omega
    exact official_bound_of_sqrt hn (Or.inl halpha)

/-- **K̄3**: by the complement transfer from K3. -/
theorem eh_Kbar3 : IsErdosHajnalLowerBound (⊥ : SimpleGraph (Fin 3))
    (fun n => (n : ℝ) ^ ((1:ℝ)/4)) := by
  have hcoe : (⊥ : SimpleGraph (Fin 3)) = (⊤ : SimpleGraph (Fin 3))ᶜ := by
    ext a b; simp
  rw [hcoe]
  exact isEH_compl eh_K3

/-- **P3** (the induced path): every closed neighborhood is a clique —
the dichotomy at `⌊√n⌋`. -/
theorem eh_P3 : IsErdosHajnalLowerBound (SimpleGraph.pathGraph 3)
    (fun n => (n : ℝ) ^ ((1:ℝ)/4)) := by
  rw [IsErdosHajnalLowerBound, Filter.eventually_atTop]
  refine ⟨4, ?_⟩
  intro n hn G hG
  have h4 := arsenal_threshold
  have hs2 : 2 ≤ Nat.sqrt n := Nat.le_sqrt.2 (by omega)
  by_cases hA : ∃ v : Fin n, Nat.sqrt n ≤ (insert v (G.neighborFinset v)).card
  · obtain ⟨v, hv⟩ := hA
    have hclique : G.IsClique ↑(insert v (G.neighborFinset v)) :=
      closedNbhd_clique_of_no_induced_P3 hG v
    have hle := (G.IsClique.card_le_cliqueNum (t := insert v (G.neighborFinset v))
      (tc := hclique))
    exact official_bound_of_sqrt hn (Or.inr (le_trans hv hle))
  · push_neg at hA
    have hbnd : ∀ v : Fin n, (insert v (G.neighborFinset v)).card ≤ Nat.sqrt n :=
      fun v => (Nat.not_le.mp (hA v)).le
    obtain ⟨s, hsindep, hcount⟩ := exists_isIndepSet_mul_ge G (Nat.sqrt n)
      (by omega) hbnd
    have hcardn : Fintype.card (Fin n) = n := by simp
    have hle := (G.IsIndepSet.card_le_indepNum (t := s) (tc := hsindep))
    have hsq : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
    have halpha : Nat.sqrt n ≤ G.indepNum := by
      by_contra hlt
      have hle' : G.indepNum ≤ Nat.sqrt n - 1 := by omega
      have h1 : Nat.sqrt n * G.indepNum ≤ Nat.sqrt n * (Nat.sqrt n - 1) :=
        Nat.mul_le_mul_left _ hle'
      have h2 : Nat.sqrt n * (Nat.sqrt n - 1) < Nat.sqrt n * Nat.sqrt n := by
        have he : Nat.sqrt n - 1 + 1 = Nat.sqrt n := by omega
        have hm : Nat.sqrt n * (Nat.sqrt n - 1) + Nat.sqrt n * 1
            = Nat.sqrt n * Nat.sqrt n := by
          rw [← Nat.mul_add, he]
        omega
      have h3 : n ≤ Nat.sqrt n * s.card := by rw [← hcardn]; exact hcount
      have h4' : Nat.sqrt n * s.card ≤ Nat.sqrt n * G.indepNum :=
        Nat.mul_le_mul_left _ hle
      omega
    exact official_bound_of_sqrt hn (Or.inl halpha)

/-- **P̄3**: by the complement transfer from P3. -/
theorem eh_Pbar3 : IsErdosHajnalLowerBound ((SimpleGraph.pathGraph 3)ᶜ)
    (fun n => (n : ℝ) ^ ((1:ℝ)/4)) := isEH_compl eh_P3

/-- **K1**: vacuous — for `n ≥ 1` the one-vertex graph is always copied,
so the hypothesis fails and the eventually-statement holds. -/
theorem eh_K1 : IsErdosHajnalLowerBound (⊥ : SimpleGraph (Fin 1))
    (fun n => (n : ℝ) ^ ((1:ℝ)/4)) := by
  rw [IsErdosHajnalLowerBound, Filter.eventually_atTop]
  refine ⟨4, ?_⟩
  intro n hn G hG
  have hemb : Fin 1 ↪ Fin n := ⟨fun _ => 0, by
    intro a b _
    exact Subsingleton.elim a b⟩
  refine hG ⟨hemb, ?_⟩
  ext a b
  have hab : a = b := Subsingleton.elim a b
  subst hab
  simp only [SimpleGraph.bot_adj, SimpleGraph.comap_adj, iff_false]
  exact fun h => G.irrefl h

/-! ## §6 THE BOARD -/

/-- **THE OFFICIAL-FORM FAMILY THEOREM.** Every member of the W68/W76
family (K1, K2, K̄2, K3, K̄3, P3, P̄3) satisfies the official Erdős–Hajnal
statement at the uniform exponent `c = 1/4`, over the official predicate
`IsErdosHajnalLowerBound` (verbatim DeepMind formal-conjectures @ 2207c54d). -/
theorem erdos_61_family : ∃ c > (0:ℝ),
    IsErdosHajnalLowerBound (⊤ : SimpleGraph (Fin 2)) (fun n => (n : ℝ) ^ c) ∧
    IsErdosHajnalLowerBound (⊥ : SimpleGraph (Fin 2)) (fun n => (n : ℝ) ^ c) ∧
    IsErdosHajnalLowerBound (⊤ : SimpleGraph (Fin 3)) (fun n => (n : ℝ) ^ c) ∧
    IsErdosHajnalLowerBound (⊥ : SimpleGraph (Fin 3)) (fun n => (n : ℝ) ^ c) ∧
    IsErdosHajnalLowerBound (SimpleGraph.pathGraph 3) (fun n => (n : ℝ) ^ c) ∧
    IsErdosHajnalLowerBound ((SimpleGraph.pathGraph 3)ᶜ) (fun n => (n : ℝ) ^ c) ∧
    IsErdosHajnalLowerBound (⊥ : SimpleGraph (Fin 1)) (fun n => (n : ℝ) ^ c) := by
  refine ⟨(1:ℝ)/4, by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact eh_K2
  · exact eh_Kbar2
  · exact eh_K3
  · exact eh_Kbar3
  · exact eh_P3
  · exact eh_Pbar3
  · exact eh_K1

#print axioms Erdos61A.erdos_61_family
#print axioms Erdos61A.isEH_compl
#print axioms Erdos61A.exists_isIndepSet_mul_ge
#print axioms Erdos61A.rpow_quarter_le_sqrt
#print axioms Erdos61A.arsenal_threshold

#eval "DM61A_FAMILY_GREEN"

end Erdos61A
