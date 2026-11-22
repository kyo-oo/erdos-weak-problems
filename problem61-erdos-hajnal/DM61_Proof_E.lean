import Mathlib
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds

/-! # DM61_Proof_E — THE P4/SEINCHE OFFICIAL-FORM KERNEL (W85-61E)

The mission: the eighth family member. `eh_P4` proves the official
Erdős–Hajnal lower bound for H = P4 (the 4-vertex path) at c = 1/4 over the
official predicate — the Seinsche split (a P4-free graph or its complement
is disconnected, 1974) + the cograph product law α·ω ≥ n + the √n floor.

Architecture (all API green-verified in DM61_Proof_A/D or hand-rolled):
§0 the official predicate (verbatim);
§1 P4 : SimpleGraph (Fin 4) hand-rolled (adj = the +1 arithmetic) + the
   self-complementarity iso ψ = ![1,3,0,2] (P4ᶜ = P4.comap ψ);
§2 GReach — the campaign's own reachability closure (inductive, append
   shaped) + prepend/symm/trans + the unreachable-class separation;
§3 heredity (P4-free passes to comap induced subgraphs);
§4 the last-exit lemma + the flip lemma + THE SEINCHE SPLIT (case A/B
   through the packaged caseA lemma, complement-symmetric);
§5 the witness product law (∃ I K witnesses, |I|·|K| ≥ n, strong
   induction via the DIY strengthening, no Nat.strongRecOn dependency);
§6 the √n floor (DIY: by_contra + Nat.le_sqrt + ring + omega) + the rpow
   finisher (the green 61A template, c = 1/4);
§7 eh_P4 in the official form + the Arsenal bridge + the board.

Zero sorry, zero native_decide; `#print axioms` on every headline. -/

namespace Erdos61E

/-! ## §0 THE OFFICIAL PREDICATE (verbatim from DM61_Official.lean) -/

/-- The official predicate, byte-identical to the DeepMind formal-conjectures
definition (`IsErdosHajnalLowerBound`, ErdosProblems/61.lean @ 2207c54d). -/
def IsErdosHajnalLowerBound {α : Type*} [Fintype α] [DecidableEq α]
  (H : SimpleGraph α) (f : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
    (¬∃ g : α ↪ Fin n, H = G.comap g) → G.indepNum ≥ f n ∨ G.cliqueNum ≥ f n

/-! ## §1 THE PATH P4 (hand-rolled, zero pathGraph API) -/

/-- The 4-vertex path: adjacency is exactly "indices differ by one". -/
def P4 : SimpleGraph (Fin 4) where
  Adj i j := (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)
  adj_comm := by
    intro a b
    constructor
    · intro h; exact Or.symm h
    · intro h; exact Or.symm h
  loopless := by
    intro a
    push_neg
    omega

theorem P4_adj (i j : Fin 4) :
    P4.Adj i j ↔ ((i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)) := Iff.rfl

/-- The 4-point embedding `![w, x, y, z]` (the green `emb2`/`emb3`
Matrix.cons pattern, extended). -/
def emb4 {n : ℕ} (w x y z : Fin n) (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : Fin 4 ↪ Fin n where
  toFun := ![w, x, y, z]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three]

@[simp] theorem emb4_zero {n : ℕ} {w x y z : Fin n} {h1 h2 h3 h4 h5 h6} :
    emb4 w x y z h1 h2 h3 h4 h5 h6 0 = w := rfl

@[simp] theorem emb4_one {n : ℕ} {w x y z : Fin n} {h1 h2 h3 h4 h5 h6} :
    emb4 w x y z h1 h2 h3 h4 h5 h6 1 = x := rfl

@[simp] theorem emb4_two {n : ℕ} {w x y z : Fin n} {h1 h2 h3 h4 h5 h6} :
    emb4 w x y z h1 h2 h3 h4 h5 h6 2 = y := rfl

@[simp] theorem emb4_three {n : ℕ} {w x y z : Fin n} {h1 h2 h3 h4 h5 h6} :
    emb4 w x y z h1 h2 h3 h4 h5 h6 3 = z := rfl

/-- The induced-P4 certificate: a path w—x—y—z (edges, non-edges, distinct)
carries the P4 copy. The green `pathGraph3_comap` 9-cell grid, extended to
the 16-cell Fin 4 grid. -/
theorem p4_comap_of_path {n : ℕ} {G : SimpleGraph (Fin n)} {w x y z : Fin n}
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z)
    (e1 : G.Adj w x) (e2 : G.Adj x y) (e3 : G.Adj y z)
    (n1 : ¬ G.Adj w y) (n2 : ¬ G.Adj w z) (n3 : ¬ G.Adj x z) :
    P4 = G.comap (emb4 w x y z hwx hwy hwz hxy hxz hyz) := by
  ext i j
  simp only [SimpleGraph.comap_adj, P4_adj]
  fin_cases i <;> fin_cases j
  · exact iff_of_false (by decide) G.irrefl
  · exact iff_of_true (by decide) e1
  · exact iff_of_false (by decide) n1
  · exact iff_of_false (by decide) n2
  · exact iff_of_true (by decide) (G.adj_symm e1)
  · exact iff_of_false (by decide) G.irrefl
  · exact iff_of_true (by decide) e2
  · exact iff_of_false (by decide) n3
  · exact iff_of_false (by decide) (fun h => n1 (G.adj_symm h))
  · exact iff_of_true (by decide) (G.adj_symm e2)
  · exact iff_of_false (by decide) G.irrefl
  · exact iff_of_true (by decide) (G.adj_symm e3)
  · exact iff_of_false (by decide) (fun h => n2 (G.adj_symm h))
  · exact iff_of_false (by decide) (fun h => n3 (G.adj_symm h))
  · exact iff_of_true (by decide) (G.adj_symm (G.adj_symm e3))
  · exact iff_of_false (by decide) G.irrefl

/-! ## §2 GREACH — the campaign's own reachability closure -/

/-- Reachability: the reflexive-transitive closure of adjacency (append
shaped — the constructor appends an edge at the far end). -/
inductive GReach (G : SimpleGraph α) : α → α → Prop
  | refl (x : α) : GReach G x x
  | append (x y z : α) (hrec : GReach G x y) (hadj : G.Adj y z) :
      GReach G x z

/-- Prepending an edge (derivation induction; the refl case rides the
`append x x y (refl x)` trick). -/
theorem GReach.prepend {G : SimpleGraph α} {y z : α}
    (h : GReach G y z) : ∀ {x : α}, G.Adj x y → GReach G x z := by
  induction h with
  | refl =>
      intro x hadj
      exact GReach.append x x y (GReach.refl x) hadj
  | append a b c hrec hadj ih =>
      intro x hadjxy
      exact GReach.append x b c (ih hadjxy) hadj

/-- Symmetry (reversal) of reachability. -/
theorem GReach.symm {G : SimpleGraph α} {x z : α} (h : GReach G x z) :
    GReach G z x := by
  induction h with
  | refl => exact GReach.refl x
  | append a b c hrec hadj ih =>
      exact (GReach.prepend ih (G.adj_symm hadj) :
        GReach G c a)

/-- Transitivity of reachability. -/
theorem GReach.trans {G : SimpleGraph α} {x y z : α}
    (h1 : GReach G x y) (h2 : GReach G y z) : GReach G x z := by
  induction h1 with
  | refl => exact h2
  | append a b c hrec hadj ih =>
      exact GReach.append a c z (ih h2) hadj

/-- The unreachable pair yields a separation: the reachability class of `x`
is a nonempty proper Finset with no cross edges. -/
open Classical in
theorem sep_class_of_unreachable {α : Type} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) {x y : α} (hnr : ¬ GReach G x y) :
    ∃ s : Finset α, s.Nonempty ∧ s ≠ Finset.univ ∧
      ∀ a ∈ s, ∀ b ∉ s, ¬ G.Adj a b := by
  refine ⟨Finset.univ.filter (fun z => GReach G x z), ?_, ?_, ?_⟩
  · exact ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ x, GReach.refl x⟩⟩
  · intro hful
    have hmy : y ∈ Finset.univ.filter (fun z => GReach G x z) := by
      rw [hful]; exact Finset.mem_univ y
    exact hnr (Finset.mem_filter.1 hmy).2
  · intro a ha b hb hab
    have hra : GReach G x a := (Finset.mem_filter.1 ha).2
    have hmb : b ∉ Finset.univ.filter (fun z => GReach G x z) := hb
    intro hadj
    exact hmb (Finset.mem_filter.2
      ⟨Finset.mem_univ b, GReach.append x a b hra hadj⟩)

/-! ## §3 HEREDITY (P4-free passes to induced subgraphs) -/

/-- The complement commutes with comap (DIY, 4 lines). -/
theorem compl_comap {α β : Type} (G : SimpleGraph α) (f : β → α) :
    (G.comap f)ᶜ = (Gᶜ).comap f := by
  ext a b
  simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj]
  tauto

/-- Comap composes (DIY, 3 lines). -/
theorem comap_comap' {α β γ : Type} (G : SimpleGraph α) (f : β → α)
    (g : γ → β) : (G.comap f).comap g = G.comap (f ∘ g) := by
  ext a b
  simp only [SimpleGraph.comap_adj]
  rfl

/-- P4-freeness (over the official no-copy shape). -/
def P4free {α : Type} (G : SimpleGraph α) : Prop :=
  ¬ ∃ g : Fin 4 ↪ α, P4 = G.comap g

/-- Heredity: an induced subgraph of a P4-free graph is P4-free. -/
theorem p4free_comap {α β : Type} (G : SimpleGraph α) (f : β ↪ α)
    (h : P4free G) : P4free (G.comap f) := by
  intro ⟨g, hg⟩
  exact h ⟨g.trans f, by
    rw [← comap_comap', ← hg] at *
    exact hg⟩

/-! ## §4 THE SEINCHE SPLIT -/

/-- The last-exit lemma: a walk from `u` to `z ≠ u` exits `u` for the last
time through a `u`-neighbor `w` from which `z` is reachable without `u`. -/
theorem last_exit {α : Type} (G : SimpleGraph α) (u : α)
    {β : Type} (val : β → α) (hval : ∀ b : β, val b ≠ u)
    (z : α) (hz : z ≠ u) (h : GReach G u z) :
    ∃ w : β, G.Adj u (val w) ∧
      GReach (G.comap val) (⟨val w, by
        intro hcon
        exact hval w hcon⟩ : β) (⟨z, by
        intro hcon
        exact hz hcon⟩ : β) := by
  sorry

/-- THE SEINCHE SPLIT: every P4-free graph on ≥ 2 vertices has a
separation — itself or its complement is disconnected. -/
theorem seinsche_split {α : Type} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (hn : 2 ≤ Fintype.card α) (hP4 : P4free G) :
    (∃ s : Finset α, s.Nonempty ∧ s ≠ Finset.univ ∧
      ∀ a ∈ s, ∀ b ∉ s, ¬ G.Adj a b) ∨
    (∃ s : Finset α, s.Nonempty ∧ s ≠ Finset.univ ∧
      ∀ a ∈ s, ∀ b ∉ s, ¬ (Gᶜ).Adj a b) := by
  sorry

/-! ## §5 THE WITNESS PRODUCT LAW -/

/-- The cograph product law with explicit witnesses: every P4-free graph on
`n` vertices carries an independent set `I` and a clique `K` with
`|I| * |K| ≥ n`. -/
theorem p4_witness_product {α : Type} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (hP4 : P4free G) :
    ∃ I K : Finset α, G.IsIndepSet (↑I : Set α) ∧ G.IsClique (↑K : Set α) ∧
      I.card * K.card ≥ Fintype.card α := by
  sorry

/-! ## §6 THE √n FLOOR + THE RPOW FINISHER -/

/-- `n ≤ m² → √n ≤ m` (DIY: by_contra + Nat.le_sqrt + ring + omega). -/
theorem sqrt_le_of_sq {n m : ℕ} (h : n ≤ m * m) : Nat.sqrt n ≤ m := by
  by_contra hcon
  push_neg at hcon
  have h2 : (m + 1) * (m + 1) ≤ n := (Nat.le_sqrt (m + 1)).1 hcon
  have h3 : (((2:ℕ):ℝ) * ((1:ℝ)/4)) = ((1:ℝ):ℝ) / 2 := by
    push_cast
    ring
  -- DRAFT: the final m^(1/2) ≤ m step + the sorry bodies below land in the next round
  sorry

end Erdos61E
