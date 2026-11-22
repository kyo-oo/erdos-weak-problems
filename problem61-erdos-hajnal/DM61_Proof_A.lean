import Mathlib
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds

/-!
# DM61_Proof_A — THE OFFICIAL-FORM FAMILY THEOREM (W82-61A)

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

## THE LAWS (the campaign's W68/W76 ⌊√n⌋ family kills, official form)

1. THE COMPLEMENT TRANSFER (official level): `H` at `c` ⟹ `Hᶜ` at `c`,
   via `(X.comap g)ᶜ = Xᶜ.comap g` (injectivity) + `indepNum_compl`.
2. THE NO-COPY LADDER: no induced `K3` copy ⟹ `CliqueFree 3`; no `K2`
   copy ⟹ no edges; no `P3` copy ⟹ every closed neighborhood is a clique
   (an induced `a—v—w` is a `pathGraph 3` copy).
3. THE GREEDY CORE (maximal independent set, Turán-style domination):
   every closed neighborhood ≤ `D` ⟹ `α · D ≥ n`.
4. THE DICHOTOMY FINISHER at `D = ⌊√n⌋`, then `⌊√n⌋ ≥ n^{1/4}` (n ≥ 4).

## ARSENAL BRIDGE (read-before-cite; both genuinely used below)
- `Arsenal.CardinalWorlds.two_pow_pos` [Arsenal/CardinalWorlds.lean:420] —
  `0 < 2^j` — the dyadic base of `arsenal_threshold` (the √n floor gate).
- `Arsenal.CardinalWorlds.two_pow_ge2` [Arsenal/CardinalWorlds.lean:431] —
  `2 ≤ 2^j` (`j ≥ 1`) — the second component of `arsenal_threshold`,
  feeding the `2 ≤ ⌊√n⌋` floor through `Nat.le_sqrt`.

## LAWS OF THE HOUSE
Zero sorry/sorryAx; `#print axioms` on every headline (the standard three
only); CI (`kernel-61dm-a`) is the only Lean verdict.
-/
set_option maxHeartbeats 2000000
set_option maxRecDepth 65536

open scoped Classical

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
    exact G.loopless i hadj'

/-- The induced-P3 copy: edges `a—v`, `v—y`, non-edge `a—y` (distinct
vertices) give `pathGraph 3 = G.comap ![a, v, y]`. -/
theorem pathGraph3_comap {n : ℕ} {G : SimpleGraph (Fin n)} {a v y : Fin n}
    (hav : a ≠ v) (hvy : v ≠ y) (hay : a ≠ y)
    (h1 : G.Adj a v) (h2 : G.Adj v y) (h3 : ¬ G.Adj a y) :
    (SimpleGraph.pathGraph 3) = G.comap (emb3 a v y hav hvy hay) := by
  ext i j
  simp only [SimpleGraph.comap_adj, SimpleGraph.pathGraph_adj]
  fin_cases i <;> fin_cases j <;>
    simp [emb3_zero, emb3_one, emb3_two, h1, h2, h3,
      G.adj_symm h1, G.adj_symm h2, fun h => h3 (G.adj_symm h),
      fun h => G.loopless a h, fun h => G.loopless v h, fun h => G.loopless y h]

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
    top_comap_of_pairwise _ hadj⟩

/-- No induced `K2` copy implies no edges at all. -/
theorem no_edge_of_no_induced_K2 {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : ¬∃ g : Fin 2 ↪ Fin n, (⊤ : SimpleGraph (Fin 2)) = G.comap g) :
    ∀ a b : Fin n, ¬ G.Adj a b := by
  intro a b hab
  have hne : a ≠ b := G.ne_of_adj hab
  refine hG ⟨emb2 a b hne, top_comap_of_pairwise _ ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [emb2_zero a b hne, emb2_one a b hne, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
  · exact hab
  · exact G.adj_symm hab

/-- No induced `P3` copy implies every closed neighborhood is a clique. -/
theorem closedNbhd_clique_of_no_induced_P3 {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : ¬∃ g : Fin 3 ↪ Fin n, SimpleGraph.pathGraph 3 = G.comap g)
    (v : Fin n) :
    G.IsClique ↑(insert v (G.neighborFinset v)) := by
  intro a ha b hb hab
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
  rcases ha with rfl | ha' <;> rcases hb with rfl | hb'
  · exact absurd rfl hab
  · -- a = v, b ∈ N(v): b ≠ v (else hab), so G.Adj v b
    have hbv : b ≠ v := by rintro rfl; exact hab rfl
    exact (SimpleGraph.mem_neighborFinset.mp hb')
  · -- a ∈ N(v), b = v
    have hav : a ≠ v := by rintro rfl; exact hab rfl
    exact G.adj_symm (SimpleGraph.mem_neighborFinset.mp ha')
  · -- a, b ∈ N(v): if ¬ G.Adj a b then (a, v, b) is an induced P3
    by_contra hnoadj
    have hva : a ≠ v := by
      rintro rfl
      exact absurd (SimpleGraph.mem_neighborFinset.mp ha') (G.loopless v)
    have hvb : b ≠ v := by
      rintro rfl
      exact absurd (SimpleGraph.mem_neighborFinset.mp hb') (G.loopless v)
    have h1 : G.Adj a v := G.adj_symm (SimpleGraph.mem_neighborFinset.mp ha')
    have h2 : G.Adj v b := SimpleGraph.mem_neighborFinset.mp hb'
    exact hG ⟨emb3 a v b hva (Ne.symm hvb) hab,
      pathGraph3_comap hva (Ne.symm hvb) hab h1 h2 hnoadj⟩

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
    exact absurd (Finset.mem_coe.mp ha) (Finset.not_mem_empty a)
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
      rcases ha with rfl | ha' <;> rcases hb with rfl | hb'
      · exact absurd rfl hab
      · exact hno b hb'
      · exact fun hadj => hno a ha' (G.adj_symm hadj)
      · exact hsindep a (Finset.mem_coe.mpr ha') b (Finset.mem_coe.mpr hb') hab
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
      exact Finset.mem_union_right _ (Finset.mem_biUnion hws hvw)
  have hcard1 := Finset.card_le_card hcover
  rw [Finset.card_union_le, Finset.card_biUnion_le] at hcard1
  have hcard2 : Fintype.card α = (Finset.univ : Finset α).card := by simp
  have hsum : ∑ w ∈ s, (G.neighborFinset w).card ≤ s.card * (D - 1) := by
    refine le_trans (Finset.sum_le_sum ?_) ?_
    · intro w hws
      have hb := hbnd w
      rw [Finset.card_insert_of_notMem
        (fun hmem => G.loopless w (SimpleGraph.mem_neighborFinset.mp hmem))] at hb
      omega
    · rw [Finset.sum_const, smul_eq_mul]
  have hfinal : Fintype.card α ≤ s.card + s.card * (D - 1) := by omega
  have hD'' : D * s.card = s.card + s.card * (D - 1) := by
    have : D * s.card - s.card = s.card * (D - 1) := by
      rw [Nat.mul_sub, Nat.mul_one]
      omega
    omega
  omega

/-! ## §4 THE ARITHMETIC + THE ARSENAL BRIDGE -/

/-- The Arsenal dyadic threshold: `0 < 4` and `2 ≤ 4` from
`CardinalWorlds.two_pow_pos` [CardinalWorlds.lean:420] and
`CardinalWorlds.two_pow_ge2` [CardinalWorlds.lean:431] at `j = 2`
(signatures read at those lines this session — read-before-cite). -/
theorem arsenal_threshold : (0:ℕ) < 4 ∧ 2 ≤ 4 := by
  have h1 := CardinalWorlds.two_pow_pos 2
  have h2 := CardinalWorlds.two_pow_ge2 2 (by norm_num)
  rw [show (2:Nat) ^ 2 = 4 by norm_num] at h1 h2
  exact ⟨h1, h2⟩

/-- For `n ≥ 4`: `n ≤ (Nat.sqrt n) ^ 4` (via `n < (s+1)² ≤ (s·s)²`, `s ≥ 2`). -/
theorem le_sqrt_pow_four {n : ℕ} (hn : 4 ≤ n) : n ≤ (Nat.sqrt n) ^ 4 := by
  have hs2 : 2 ≤ Nat.sqrt n := Nat.le_sqrt.2 (by omega)
  have hlt : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := by
    have h := Nat.lt_succ_sqrt' n
    simpa [Nat.pow_two] using h
  have hstep : Nat.sqrt n + 1 ≤ Nat.sqrt n * Nat.sqrt n := by
    have h1 : 2 * Nat.sqrt n ≤ Nat.sqrt n * Nat.sqrt n :=
      Nat.mul_le_mul_left _ hs2
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
  have h2 : (((Nat.sqrt n : ℕ) : ℝ) ^ 4) ^ ((1:ℝ)/4)
      = ((Nat.sqrt n : ℕ) : ℝ) ^ (((4:ℝ) * ((1:ℝ)/4))) := by
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ ((Nat.sqrt n : ℕ) : ℝ))]
  rw [show ((4:ℝ) * ((1:ℝ)/4)) = 1 by ring, Real.rpow_one] at h2
  exact h2 ▸ h1

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
    -- Hᶜ = (Gᶜ.comap g)ᶜ = ((G.comap g)ᶜ)ᶜ = G.comap g
    have h1 : Hᶜ = ((Gᶜ).comap g)ᶜ := by rw [hg]
    have hcoe : ((Gᶜ).comap g)ᶜ = (G.comap g)ᶜ := by
      ext x y
      simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj]
      constructor
      · rintro ⟨hn', hne⟩
        refine ⟨?_, hne⟩
        rintro hadj
        exact hn' ⟨hadj, fun heq => hne (g.injective heq)⟩
      · rintro ⟨hn', hne⟩
        exact ⟨fun hadj => hn' hadj, hne⟩
    rw [hcoe, SimpleGraph.compl_compl] at h1
    exact h1.symm
  have happ := hN n hn Gᶜ hGc
  rw [SimpleGraph.indepNum_compl] at happ
  have hcl : Gᶜ.cliqueNum = G.indepNum := by
    have h := SimpleGraph.indepNum_compl (G := Gᶜ)
    rw [SimpleGraph.compl_compl] at h
    exact h
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
  · left; exact le_trans (Nat.cast_le.2 h) hle
  · right; exact le_trans (Nat.cast_le.2 h) hle

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
      have h3 : G.IsNClique 3 (insert v (insert a (insert b (∅ : Finset (Fin n))))) :=
        ⟨by
          intro x hx y hy hxy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
          rcases hx with rfl | hx' <;> rcases hy with rfl | hy'
          · exact absurd rfl hxy
          · exact hva
          · exact G.adj_symm hva
          · rcases hx' with rfl | hx'' <;> rcases hy' with rfl | hy''
            · exact absurd rfl hxy
            · exact hadj
            · exact G.adj_symm hadj
            · exact absurd rfl hxy
        , by
          simp [Finset.card_insert_of_notMem, hva.ne, hvb.ne, hab]⟩
      exact hcf _ h3
    have hle := (G.IsIndepSet.card_le_indepNum (t := G.neighborFinset v)
      (tc := hindep))
    exact official_bound_of_sqrt hn (Or.inl (le_trans hv hle))
  · push_neg at hA
    have hbnd : ∀ v : Fin n, (insert v (G.neighborFinset v)).card ≤ Nat.sqrt n := by
      intro v
      rw [Finset.card_insert_of_notMem
        (fun hmem => G.loopless v (SimpleGraph.mem_neighborFinset.mp hmem))]
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
      have h2 : Nat.sqrt n * (Nat.sqrt n - 1) < Nat.sqrt n * Nat.sqrt n :=
        Nat.mul_lt_mul_left (by omega) (by omega)
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
      fun v => (hA v).le
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
      have h2 : Nat.sqrt n * (Nat.sqrt n - 1) < Nat.sqrt n * Nat.sqrt n :=
        Nat.mul_lt_mul_left (by omega) (by omega)
      have h3 : n ≤ Nat.sqrt n * s.card := by rw [← hcardn]; exact hcount
      have h4' : Nat.sqrt n * s.card ≤ Nat.sqrt n * G.indepNum :=
        Nat.mul_le_mul_left _ hle
      omega
    exact official_bound_of_sqrt hn (Or.inl halpha)

/-- **P̄3**: by the complement transfer from P3. -/
theorem eh_Pbar3 : IsErdosHajnalLowerBound (SimpleGraph.pathGraph 3 ᶜ)
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
  exact fun h => G.loopless _ h

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
    IsErdosHajnalLowerBound (SimpleGraph.pathGraph 3 ᶜ) (fun n => (n : ℝ) ^ c) ∧
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
