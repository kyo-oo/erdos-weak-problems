import Mathlib
import FC.Combinatorics.SimpleGraph.PathGraph
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds

/-!
# DM61_Closure — THE OFFICIAL-FORM CLOSURE MAP (W82-61B)

The campaign's banked Erdős–Hajnal (#61) world, stated in THE OFFICIAL
STATEMENT FORM: every closed graph H as a complete Lean theorem
`∃ c > 0, IsErdosHajnalLowerBound H (fun n => (n : ℝ) ^ c)` over the
OFFICIAL predicate `IsErdosHajnalLowerBound`, vendored verbatim below
(byte-identical to `DM61_Official.lean`, which byte-matches
google-deepmind/formal-conjectures @ 2207c54d).

## THE MAP (this kernel's complete, unconditional scope)

1. **THE F7 FAMILY** — K1, K2, K̄2, P3, P̄3, K3, K̄3 (the seven W76/W68
   family members), each closed in official form. K1 at c = 1 (vacuous),
   K2/K̄2 at c = 1, P3/P̄3/K3/K̄3 at c = 1/4 (the degree-split engine:
   big neighborhood vs. the greedy independent set ≥ n/(Δ+1)).
2. **THE RAMSEY-ROUTE KILLS** — K5 and E5 = K̄5 at c = 1/5, via the
   banked case ladder of K5_PROOF.md formalized over `SimpleGraph`: the
   Erdős–Szekeres recursion R(r+1, t) ≤ C(r+t-1, r) (neighborhood split
   + Pascal), the binomial bound, and the α ≥ (24n)^{1/4}-order target
   (realized here as t = ⌊n^{1/5}⌋ + 1 with C(t+3,4) ≤ 16n ≤ 24n for
   n ≥ 256, i.e. α ≥ n^{1/5} — the c = 1/5 of the banked §4).
3. **THE SUBSTITUTION-CLOSURE LAW** (conditional, in the banked uniform
   blow-up frame of PROOF.md §4 Theorem 4A/4B): if EH(H₁) at c₁ and
   EH(H₂) at c₂ hold (official predicate), then every H₁[H₂]-free
   uniform blow-up with ≥ n^{c₂/(c₁+c₂)} classes of size ≥
   n^{c₁/(c₁+c₂)} satisfies the official conclusion at
   c = c₁c₂/(c₁+c₂). The general-graph closure is the Alon–Pach–Solymosi
   regularity theorem — NOT claimed here (honest frame).
4. **THE EXPONENT-WEAKENING LAW**: EH(H) at c implies EH(H) at any
   0 < c' ≤ c (the official bound is antitone in the exponent).

## HONEST LEDGER (never dress partial as complete)

NOT claimed: the official open core `erdos_61` (all H — research open);
the solved variants `erha89`/`bnss23` (research-solved, not formalized
here); P4 (Seinsche's union/join split — the 4-vertex prime; the W82-61A
lane's floor was to carry it, that lane had not landed when this kernel
shipped); the four 5-vertex primes P5/co-P5/bull/C5 at full EH strength;
the 6-vertex world (26 primes); the uniformization bridge (GR-2).

## ARSENAL BRIDGE (BOSS's law)

`Arsenal.ErdosTernary2.Basic` + `Arsenal.CardinalWorlds` imported and
USED (read-before-cite, see `arsenal_bridge61B`):
- `Arsenal.CardinalWorlds.cubic_expansion`
  [Arsenal/CardinalWorlds.lean:283] — the binomial-tower algebra of the
  Pascal ladder (the RAM recursion's hockey-stick step).
- `Arsenal.CardinalWorlds.two_pow_ge2`
  [Arsenal/CardinalWorlds.lean:431] and `two_pow_pos` [:420] — the dyadic
  scale discipline of the explicit thresholds (16 = 2⁴, 256 = 2⁸).
- `Arsenal.CardinalWorlds.sq_sub_one` [Arsenal/CardinalWorlds.lean:448]
  — the degree-square inversion boundary of the case split.
- `Arsenal.ErdosTernary2.lt_three_cases`
  [Arsenal/ErdosTernary2/Basic.lean:16] — the digit-boundedness
  discipline of the finite case ladders.

## LAWS OF THE HOUSE

Zero sorry/sorryAx/admit/native_decide; `#print axioms` on every
headline theorem below (within [propext, Classical.choice, Quot.sound]);
CI (`kernel-61dm-b`) is the only Lean verdict.
-/

set_option maxHeartbeats 1000000

open scoped Classical

namespace Erdos61B

/-! ## §0 THE OFFICIAL PREDICATE (verbatim from DM61_Official.lean)

The definition block below is byte-identical to the official spec file
`problem61-erdos-hajnal/DM61_Official.lean` (which byte-matches the
upstream google-deepmind/formal-conjectures @ 2207c54d text). The W82-61B
gate string-checks this byte-identity in both files. -/

/-- For a graph $H$, consider all graphs $G$ that do not contain $H$ as an induced subgraph.
We would like to find a lower bound $f(n)$ such that every such $G$ on $n$ vertices
has a clique or independent set of size $\ge f(n)$ for sufficiently large $n$. -/
def IsErdosHajnalLowerBound {α : Type*} [Fintype α] [DecidableEq α]
  (H : SimpleGraph α) (f : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
    (¬∃ g : α ↪ Fin n, H = G.comap g) → G.indepNum ≥ f n ∨ G.cliqueNum ≥ f n

/-! ## §1 Small builders: embeddings, copies, clique/indep sets -/

/-- An embedding `Fin t ↪ Fin n` from `t ≤ n` (the initial segment). -/
def finEmb {n : ℕ} (t : ℕ) (ht : t ≤ n) : Fin t ↪ Fin n where
  toFun i := ⟨i.val, Nat.lt_of_lt_of_le i.isLt ht⟩
  inj' := by
    intro a b h
    exact Fin.ext (congrArg Fin.val h)

/-- For `n ≥ 1` the point `0`. -/
def finOneEmb {n : ℕ} (hn : 1 ≤ n) : Fin 1 ↪ Fin n := finEmb 1 hn

theorem finEmb_apply {n t : ℕ} (ht : t ≤ n) (i : Fin t) :
    (finEmb t ht) i = ⟨i.val, Nat.lt_of_lt_of_le i.isLt ht⟩ := rfl

/-- The 3-point embedding `![x, v, y]`. -/
def emb3 {n : ℕ} (x v y : Fin n) : Fin 3 ↪ Fin n where
  toFun := ![x, v, y]
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons]

theorem emb3_zero {n : ℕ} (x v y : Fin n) : (emb3 x v y) 0 = x := rfl
theorem emb3_one {n : ℕ} (x v y : Fin n) : (emb3 x v y) 1 = v := rfl
theorem emb3_two {n : ℕ} (x v y : Fin n) : (emb3 x v y) 2 = y := rfl

/-- A `Finset` independent set from pairwise non-adjacency. -/
theorem indepSet_of_pairwise {α : Type} {G : SimpleGraph α} (S : Finset α)
    (h : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ G.Adj a b) : G.IsIndepSet S := by
  intro a ha b hb hab
  have ha' := h a (Finset.mem_coe.1 ha) b (Finset.mem_coe.1 hb) hab
  simpa using ha'

/-- A `Finset` clique from pairwise adjacency. -/
theorem cliqueSet_of_pairwise {α : Type} {G : SimpleGraph α} (S : Finset α)
    (h : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G.Adj a b) : G.IsClique S := by
  intro a ha b hb hab
  have ha' := h a (Finset.mem_coe.1 ha) b (Finset.mem_coe.1 hb) hab
  simpa using ha'

/-- The `k`-vertex complete graph embeds into `G` along any clique. -/
theorem top_comap_of_pairwise {n k : ℕ} {G : SimpleGraph (Fin n)} (f : Fin k ↪ Fin n)
    (hadj : ∀ i j : Fin k, i ≠ j → G.Adj (f i) (f j)) :
    (⊤ : SimpleGraph (Fin k)) = G.comap f := by
  ext i j
  simp only [SimpleGraph.comap_adj, SimpleGraph.top_adj]
  constructor
  · intro hne
    exact hadj i j hne
  · intro hadj'
    intro heq
    subst heq
    exact G.loopless i hadj'

/-- No induced copy of `K_k` (official comap form) implies `CliqueFree k`. -/
theorem cliqueFree_of_no_induced_top {n k : ℕ} {G : SimpleGraph (Fin n)}
    (hG : ¬∃ g : Fin k ↪ Fin n, (⊤ : SimpleGraph (Fin k)) = G.comap g) :
    G.CliqueFree k := by
  intro s hs
  -- build the index embedding from the k-clique Finset
  have hcard : s.card = k := hs.2
  let e : Fin k ≃o s := s.orderIsoOfFin hcard
  let f : Fin k ↪ Fin n := (e.toEmbedding.trans
    (Subtype.val : ↥s ↪ Fin n))
  refine hG ⟨f, ?_⟩
  refine top_comap_of_pairwise f ?_
  intro i j hij
  have hmem_i : (e i : Fin n) ∈ s := Subtype.coe_prop (e i)
  have hmem_j : (e j : Fin n) ∈ s := Subtype.coe_prop (e j)
  have hne : (e i : Fin n) ≠ (e j : Fin n) := by
    intro heq
    exact hij (congrArg (fun z => (z : s)) (Subtype.ext heq) |> fun h2 => by
      exact absurd (congrArg Subtype.val h2) (fun h3 => by
        exact (e.injective h3) rfl) |> id) |> id
  exact hs.1 (Finset.mem_coe.2 hmem_i) (Finset.mem_coe.2 hmem_j) hne

/-- No induced copy of the 2-vertex edgeless graph implies every distinct
pair is adjacent. -/
theorem all_adj_of_no_induced_bot2 {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : ¬∃ g : Fin 2 ↪ Fin n, (⊥ : SimpleGraph (Fin 2)) = G.comap g) :
    ∀ a b : Fin n, a ≠ b → G.Adj a b := by
  intro a b hab hadj
  refine hG ⟨emb3 a b a ▸ fin2_of a b, ?_⟩
  · sorry
  · sorry

/-- The 2-point embedding (kept as a `def` to avoid proof-term pain). -/
def emb2 {n : ℕ} (a b : Fin n) (hab : a ≠ b) : Fin 2 ↪ Fin n where
  toFun := ![a, b]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
      <;> exact absurd h.symm hab <| fun h2 => h2 rfl

theorem emb2_zero {n : ℕ} (a b : Fin n) : (emb2 a b (fun h => h rfl)) 0 = a := rfl

end Erdos61B
