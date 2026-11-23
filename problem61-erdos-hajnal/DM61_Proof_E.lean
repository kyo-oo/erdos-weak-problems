import Mathlib
import Arsenal.ErdosTernary2.Basic
import Arsenal.CardinalWorlds

/-! # DM61_Proof_E — THE P4/SEINCHE OFFICIAL-FORM KERNEL (W85-61E, R2)

The mission: the eighth family member. `eh_P4` proves the official
Erdős–Hajnal lower bound for H = P4 (the 4-vertex path) at c = 1/4 over the
official predicate — the Seinsche split (a P4-free graph or its complement
is disconnected, 1974) + the cograph product law I·K ≥ n + the √n floor.

Architecture (AUDIT_W85_61E.md — the adversarially machine-verified contract
(52 PASS / 0 FAIL, exhaustive n ≤ 6); every draft defect repaired per audit §4):
§0 the official predicate (verbatim);
§1 P4 hand-rolled (adj = the +1 arithmetic; the Std field shapes per the S083
   playbook) + emb4 + the 16-cell grid p4_comap_of_path (cells (2,3)/(3,2)
   de-transposed — audit D1/D2);
§2 GReach — the campaign's own reachability closure (inductive, append
   shaped) + prepend/symm/trans (the branch-binder + second-walk-induction
   repairs — audit D6/D7/D8) + walk_crosses (audit D12) +
   sep_class_of_unreachable + the connectivity bridge;
§3 heredity: compl_comap REPAIRED at injective f (audit D4 — the draft's
   uninjective version was FALSE), comap_comap', p4free_comap (the defeq
   repair — audit D5);
§4 the Seinsche engine: last_exit (the subtype statement + the i = u motive
   — audit D9), the flip lemma, the isolated-vertex micro-lemma, caseA (the
   audit §1.2 case tree: STEP 1 neighbor-in-every-class, STEP 2 the mixed
   class → flip + two-class + the P4 completion (q, p, u, z′), STEP 3 the
   universality finish), the ψ self-complementarity bridge (P4ᶜ = P4.comap
   ψ, ψ = ![1,3,0,2]), and seinsche_split (strong induction, the n = 2
   base by the edge dichotomy + the 3-in-2 pigeonhole world fact);
§5 the witness product law (DIY strong induction; union/join split; the
   image transports; the ≤ 1 world by IsEmpty/Unique);
§6 sqrt_le_of_sq (the ring+omega tail — audit D10) + the 61A finisher chain
   (arsenal_threshold, le_sqrt_pow_four, rpow_quarter_le_sqrt,
   official_bound_of_sqrt — ported verbatim from the CI-green DM61_Proof_A,
   attributed);
§7 eh_P4 in the official form + the P̄4 complement transfer + the board +
   the Arsenal bridge.

Zero sorry, zero native_decide; `#print axioms` on every headline. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 262144

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
  Adj i j := ((i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ))
  adj_comm := ⟨fun h => Or.symm h⟩
  loopless := ⟨fun a => by
    show ¬ (((a : ℕ) + 1 = (a : ℕ)) ∨ ((a : ℕ) + 1 = (a : ℕ)))
    omega⟩

theorem P4_adj (i j : Fin 4) :
    P4.Adj i j ↔ ((i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ)) := Iff.rfl

/-- The 4-point embedding `![w, x, y, z]` (the green `emb2`/`emb3`
Matrix.cons pattern, extended; the 16 explicit inj' cells — no
`cons_val_three` dependency, audit D11). -/
def emb4 {n : ℕ} (w x y z : Fin n) (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : Fin 4 ↪ Fin n where
  toFun := ![w, x, y, z]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · simp only [emb4_zero, emb4_one, emb4_two, emb4_three] at h
      exact absurd h hwx
    · simp only [emb4_zero, emb4_one, emb4_two, emb4_three] at h
      exact absurd h hwy
    · simp only [emb4_zero, emb4_one, emb4_two, emb4_three] at h
      exact absurd h hwz
    · simp only [emb4_zero, emb4_one, emb4_two, emb4_three] at h
      exact absurd h.symm hwx
    · rfl
    · simp only [emb4_zero, emb4_one, emb4_two, emb4_three] at h
      exact absurd h hxy
    · simp only [emb4_zero, emb4_one, emb4_two, emb4_three] at h
      exact absurd h hxz
    · simp only [emb4_zero, emb4_one, emb4_two, emb4_three] at h
      exact absurd h.symm hwy
    · simp only [emb4_zero, emb4_one, emb4_two, emb4_three] at h
      exact absurd h.symm hxy
    · simp only [emb4_zero, emb4_one, emb4_two, emb4_three] at h
      exact absurd h.symm hxz
    · rfl
    · simp only [emb4_zero, emb4_one, emb4_two, emb4_three] at h
      exact absurd h.symm hwz
    · simp only [emb4_zero, emb4_one, emb4_two, emb4_three] at h
      exact absurd h.symm hyz
    · rfl

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
the 16-cell Fin 4 grid (cells (2,3)/(3,2) de-transposed per audit D1/D2). -/
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
  · exact iff_of_true (by decide) e3
  · exact iff_of_false (by decide) (fun h => n2 (G.adj_symm h))
  · exact iff_of_false (by decide) (fun h => n3 (G.adj_symm h))
  · exact iff_of_true (by decide) (G.adj_symm e3)
  · exact iff_of_false (by decide) G.irrefl

/-! ## §2 GREACH — the campaign's own reachability closure -/

/-- Reachability: the reflexive-transitive closure of adjacency (append
shaped — the constructor appends an edge at the far end). -/
inductive GReach {α : Type} (G : SimpleGraph α) : α → α → Prop
  | refl (x : α) : GReach G x x
  | append (x y z : α) (hrec : GReach G x y) (hadj : G.Adj y z) :
      GReach G x z

/-- Prepending an edge (derivation induction; the refl case rides the
`append x x y (refl x)` trick — branch binders only, audit D6). -/
theorem GReach.prepend {G : SimpleGraph α} {y z : α}
    (h : GReach G y z) : ∀ {x : α}, G.Adj x y → GReach G x z := by
  induction h with
  | refl a =>
      intro x hadj
      exact GReach.append x x a (GReach.refl x) hadj
  | append a b c hrec hadj ih =>
      intro x hadjxy
      exact GReach.append x b c (ih hadjxy) hadj

/-- Symmetry (reversal) of reachability (branch binder, audit D7). -/
theorem GReach.symm {G : SimpleGraph α} {x z : α} (h : GReach G x z) :
    GReach G z x := by
  induction h with
  | refl a => exact GReach.refl a
  | append a b c hrec hadj ih =>
      exact (GReach.prepend ih (G.adj_symm hadj) :
        GReach G c a)

/-- Transitivity of reachability (induction on the SECOND walk, peeling its
far end — the draft's first-walk strategy was circular, audit D8). -/
theorem GReach.trans {G : SimpleGraph α} {x y z : α}
    (h1 : GReach G x y) (h2 : GReach G y z) : GReach G x z := by
  induction h2 with
  | refl => intro h; exact h
  | append a b c hrec hadj ih =>
      exact fun h => GReach.append x b c (ih h) hadj

/-- **The walk-crossing lemma** (audit D12 — the missing inventory piece):
a walk from `a` to `b` crosses every separation between them. -/
theorem walk_crosses {G : SimpleGraph α} {a b : α} (h : GReach G a b) :
    ∀ (s : Finset α), a ∈ s → b ∉ s →
      ∃ p q, p ∈ s ∧ q ∉ s ∧ G.Adj p q := by
  induction h with
  | refl c =>
      intro s hs hs'
      exact absurd hs hs'
  | append x y z hrec hadj ih =>
      intro s hs hs'
      by_cases hy : y ∈ s
      · exact ⟨y, z, hy, hs', hadj⟩
      · exact ih s hs hy

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

/-- The connectivity bridge: no separation ⟹ every pair is walk-connected
(the contrapositive of `sep_class_of_unreachable`). -/
theorem conn_of_no_sep {α : Type} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α)
    (hn : ¬ ∃ s : Finset α, s.Nonempty ∧ s ≠ Finset.univ ∧
      ∀ a ∈ s, ∀ b ∉ s, ¬ G.Adj a b) :
    ∀ x y : α, GReach G x y := by
  intro x y
  by_contra hr
  exact hn (sep_class_of_unreachable G hr)

/-! ## §3 HEREDITY (P4-free passes to induced subgraphs) -/

/-- The complement commutes with comap at INJECTIVE functions (the draft's
uninjective version was FALSE — audit D4). -/
theorem compl_comap {α β : Type} (G : SimpleGraph α) (f : β → α)
    (hf : Function.Injective f) :
    (G.comap f)ᶜ = (Gᶜ).comap f := by
  ext a b
  simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun heq => h1 (hf heq)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun heq => h1 (congrArg f heq), h2⟩

/-- Comap composes (DIY, 3 lines). -/
theorem comap_comap' {α β γ : Type} (G : SimpleGraph α) (f : β → α)
    (g : γ → β) : (G.comap f).comap g = G.comap (f ∘ g) := by
  ext a b
  simp only [SimpleGraph.comap_adj]
  rfl

/-- P4-freeness (over the official no-copy shape — at `α := Fin n` this is
the official predicate's hypothesis definitionally, audit §3). -/
def P4free {α : Type} (G : SimpleGraph α) : Prop :=
  ¬ ∃ g : Fin 4 ↪ α, P4 = G.comap g

/-- Heredity: an induced subgraph of a P4-free graph is P4-free (at
injective carrier maps; the defeq repair, audit D5). -/
theorem p4free_comap {α β : Type} (G : SimpleGraph α) (f : β → α)
    (hf : Function.Injective f) (h : P4free G) : P4free (G.comap f) := by
  intro ⟨g, hg⟩
  refine h ⟨⟨(g : Fin 4 → α) ∘ f, fun a b hab => g.injective (hf hab)⟩, ?_⟩
  exact hg.trans (comap_comap' G f g)

/-! ## §4 THE SEINCHE ENGINE -/

/-- **The last-exit lemma** (the subtype statement, audit D9): a walk from
`u` to `z ≠ u` exits `u` for the last time through a `u`-neighbor `w` from
which `z` is reachable without `u`. The auxiliary statement carries
`i = u` in the motive; the conclusion carries the subtype proof flexibly. -/
theorem last_exit_aux {α : Type} (G : SimpleGraph α) (u : α) :
    ∀ (i j : α), GReach G i j → i = u → j ≠ u →
      ∃ w : {x : α // x ≠ u}, G.Adj u (w : α) ∧
        ∀ (hj : j ≠ u), GReach
          (G.comap (Subtype.val : {x : α // x ≠ u} → α)) w ⟨j, hj⟩ := by
  intro i j h
  induction h with
  | refl c =>
      intro hcu hcu'
      exact absurd hcu hcu'
  | append a b c hrec hadj ih =>
      intro hau hcu
      by_cases hbu : b = u
      · refine ⟨⟨c, hcu⟩, ?_, fun _ => GReach.refl ⟨c, hcu⟩⟩
        show G.Adj u (c : α)
        rw [← hbu]
        exact hadj
      · obtain ⟨w, hwadj, hwreach⟩ := ih hau hbu
        refine ⟨w, hwadj, fun _ => ?_⟩
        exact GReach.append w ⟨b, hbu⟩ ⟨c, hcu⟩ (hwreach hbu)
          (by simp only [SimpleGraph.comap_adj, Subtype.coe_mk]; exact hadj)

theorem last_exit {α : Type} (G : SimpleGraph α) (u : α) {z : α}
    (hz : z ≠ u) (h : GReach G u z) :
    ∃ w : {x : α // x ≠ u}, G.Adj u (w : α) ∧
      GReach (G.comap (Subtype.val : {x : α // x ≠ u} → α)) w ⟨z, hz⟩ := by
  obtain ⟨w, hw1, hw2⟩ := last_exit_aux G u u z h rfl hz
  exact ⟨w, hw1, hw2 hz⟩

/-- **The flip lemma** (audit §1.2 STEP 2): on an intra-class walk from `a`
to `b` (in G−u) where `u` is adjacent to `a` but not to `b`, some edge
p—q of the walk flips u-adjacency, and both p, q stay reachable from `a`
(the class membership receipts). -/
theorem flip {α : Type} (G : SimpleGraph α) (u : α) :
    ∀ (a b : {x : α // x ≠ u}),
      GReach (G.comap (Subtype.val : {x : α // x ≠ u} → α)) a b →
      G.Adj u (a : α) → ¬ G.Adj u (b : α) →
      ∃ p q : {x : α // x ≠ u},
        G.Adj (p : α) (q : α) ∧ G.Adj u (p : α) ∧ ¬ G.Adj u (q : α) ∧
        GReach (G.comap (Subtype.val : {x : α // x ≠ u} → α)) a p ∧
        GReach (G.comap (Subtype.val : {x : α // x ≠ u} → α)) a q := by
  intro a b h
  induction h with
  | refl c => intro h1 h2; exact absurd h1 h2
  | append x y z hrec hadj ih =>
      intro hxu hyu
      by_cases hmy : G.Adj u (y : α)
      · refine ⟨y, z, ?_, hmy, hyu, hrec, GReach.append x y z hrec hadj⟩
        simp only [SimpleGraph.comap_adj, Subtype.coe_mk] at hadj
        exact hadj
      · exact ih hxu hmy

/-- **The isolated-vertex micro-lemma** (audit §1.2 STEP 3): a walk from an
isolated vertex stays put. -/
theorem reach_isolated {α : Type} (H : SimpleGraph α) (u : α)
    (hiso : ∀ v : α, ¬ H.Adj u v) :
    ∀ {z : α}, GReach H u z → z = u := by
  intro z h
  induction h with
  | refl c => intro _; rfl
  | append x y z' hrec hadj ih =>
      intro hiso'
      have hxy : y = x := ih hiso'
      rw [hxy] at hadj
      exact absurd hadj (hiso' z')

/-- **caseA — the heart of Seinsche** (audit §1.2, machine-verified 23,724
constructive instances): if G and Gᶜ are both walk-connected, G is P4-free,
and some pair in G−u is unreachable in G−u, then False. The case tree:
a mixed class (STEP 2) yields the induced P4 (q, p, u, z′); a uniform
adjacency profile forces u G-universal (STEP 1 + STEP 3), so u is isolated
in Gᶜ — contradicting Gᶜ's connectivity. -/
theorem caseA {α : Type} (G : SimpleGraph α) (u : α)
    (hconn : ∀ x y : α, GReach G x y)
    (hconnC : ∀ x y : α, GReach (Gᶜ) x y)
    (hP4 : P4free G)
    (x' y' : {x : α // x ≠ u})
    (hunreach : ¬ GReach
      (G.comap (Subtype.val : {x : α // x ≠ u} → α)) x' y') : False := by
  -- STEP 1: u has a G-neighbor in every G−u class.
  have step1 : ∀ v : {x : α // x ≠ u}, ∃ w : {x : α // x ≠ u},
      G.Adj u (w : α) ∧ GReach
        (G.comap (Subtype.val : {x : α // x ≠ u} → α)) w v := by
    intro v
    obtain ⟨w, hw1, hw2⟩ := last_exit G u v.2 (hconn u v)
    exact ⟨w, hw1, hw2 v.2⟩
  by_cases hmix : ∃ a b : {x : α // x ≠ u},
      GReach (G.comap (Subtype.val : {x : α // x ≠ u} → α)) a b ∧
      G.Adj u (a : α) ∧ ¬ G.Adj u (b : α)
  · -- STEP 2 (the mixed class): flip, then the two-class trick, then the
    -- induced P4 (q, p, u, z′) with all six pairs accounted.
    obtain ⟨a, b, hreach, hua, hub⟩ := hmix
    obtain ⟨p, q, hpq, hup, huq, hrp, hrq⟩ := flip G u a b hreach hua hub
    -- The two-class trick: some of x', y' lies outside a's class.
    have hout : ¬ (GReach (G.comap (Subtype.val : {x : α // x ≠ u} → α)) a x'
        ∧ GReach (G.comap (Subtype.val : {x : α // x ≠ u} → α)) a y') := by
      rintro ⟨hx, hy⟩
      exact hunreach (GReach.trans (GReach.symm hx) hy)
    obtain ⟨v, hvout⟩ : ∃ v : {x : α // x ≠ u},
        ¬ GReach (G.comap (Subtype.val : {x : α // x ≠ u} → α)) a v := by
      by_cases hx : GReach (G.comap (Subtype.val : {x : α // x ≠ u} → α)) a x'
      · exact ⟨y', by rintro hy; exact hout ⟨hx, hy⟩⟩
      · exact ⟨x', hx⟩
    -- z′ : a u-neighbor in v's class (STEP 1) — hence outside a's class.
    obtain ⟨z', huz, hrz⟩ := step1 v
    have hzclass : ¬ GReach (G.comap (Subtype.val : {x : α // x ≠ u} → α))
        a z' := by
      rintro hcon
      exact hvout (GReach.trans hcon hrz)
    -- The cross non-adjacencies (p, q vs z′): an edge would join the
    -- classes through the walk machinery.
    have hnoCross : ∀ t : {x : α // x ≠ u},
        GReach (G.comap (Subtype.val : {x : α // x ≠ u} → α)) a t →
        ¬ G.Adj (t : α) (z' : α) := by
      intro t ht hadge
      have hca : (G.comap (Subtype.val : {x : α // x ≠ u} → α)).Adj t z' :=
        by
          simp only [SimpleGraph.comap_adj, Subtype.coe_mk]
          exact hadge
      have hwalk : GReach (G.comap (Subtype.val : {x : α // x ≠ u} → α))
          t z' := GReach.append t t z' (GReach.refl t) hca
      exact hzclass (GReach.trans ht hwalk)
    have hpz : ¬ G.Adj (p : α) (z' : α) := hnoCross p hrp
    have hqz : ¬ G.Adj (q : α) (z' : α) := hnoCross q hrq
    -- Distinctness receipts.
    have hqp : (q : α) ≠ (p : α) := by
      rintro h
      rw [← h] at hpq
      exact absurd hpq (G.irrefl _)
    have hqu : (q : α) ≠ u := fun h => q.2 h
    have hpu : (p : α) ≠ u := fun h => p.2 h
    have hqz' : (q : α) ≠ (z' : α) := by
      rintro h
      have hqe : q = z' := Subtype.ext_iff.2 h
      rw [hqe] at hrq
      exact hzclass hrq
    have hpz' : (p : α) ≠ (z' : α) := by
      rintro h
      have hpe : p = z' := Subtype.ext_iff.2 h
      rw [hpe] at hrp
      exact hzclass hrp
    have huz' : u ≠ (z' : α) := fun h => z'.2 h.symm
    -- THE INDUCED P4 (q, p, u, z′): edges q—p, p—u, u—z′; non-edges
    -- q—u, q—z′, p—z′. Contradiction with P4free.
    exact hP4 ⟨emb4 (q : α) (p : α) u (z' : α) hqp hqu hqz' hpu hpz' huz',
      p4_comap_of_path hqp hqu hqz' hpu hpz' huz'
        (G.adj_symm hpq) (G.adj_symm hup) huz huq hqz hpz⟩
  · -- STEP 3 (the uniform case): uniformity + STEP 1 ⟹ u G-universal ⟹
    -- u isolated in Gᶜ ⟹ Gᶜ disconnected — contradiction.
    push_neg at hmix
    have hmono : ∀ a b : {x : α // x ≠ u},
        GReach (G.comap (Subtype.val : {x : α // x ≠ u} → α)) a b →
        G.Adj u (a : α) → G.Adj u (b : α) := by
      intro a b hab hua'
      by_contra hb
      exact hmix a b hab hua' hb
    have huniv : ∀ v : {x : α // x ≠ u}, G.Adj u (v : α) := by
      intro v
      obtain ⟨w, hwadj, hwreach⟩ := step1 v
      exact hmono w v hwreach hwadj
    have hisoC : ∀ v : α, ¬ (Gᶜ).Adj u v := by
      intro v hv
      rcases eq_or_ne v u with rfl | hne
      · exact (SimpleGraph.compl_adj.1 hv).1 rfl
      · exact (SimpleGraph.compl_adj.1 hv).2 (huniv ⟨v, hne⟩)
    have hreachC := hconnC u (y' : α)
    have hyu : (y' : α) = u := reach_isolated (Gᶜ) u hisoC hreachC
    exact y'.2 hyu.symm

/-! ### The ψ self-complementarity bridge (audit §1.3) -/

/-- The self-complementarity carrier: P4ᶜ = P4.comap ψ with
ψ = ![1,3,0,2] (all 16 cells verified by the audit machine, S4). -/
def psi : Fin 4 → Fin 4 := ![1, 3, 0, 2]

theorem p4_compl_comap : (P4ᶜ) = P4.comap psi := by
  ext i j
  simp only [SimpleGraph.compl_adj, SimpleGraph.comap_adj, P4_adj]
  fin_cases i <;> fin_cases j <;> decide

/-- The reverse carrier: ψ ∘ ψ⁻¹ = id (ψ⁻¹ = ![2,0,3,1]). -/
def psiInv : Fin 4 → Fin 4 := ![2, 0, 3, 1]

theorem psi_comp : psi ∘ psiInv = id := by
  funext i
  fin_cases i <;> decide

/-- **The ψ-bridge**: P4-freeness passes to the complement (audit §1.3:
complement the copy equation, then pull back along ψ⁻¹). -/
theorem p4free_compl {α : Type} (G : SimpleGraph α) (h : P4free G) :
    P4free (Gᶜ) := by
  intro ⟨g, hg⟩
  refine h ⟨⟨(g : Fin 4 → α) ∘ psiInv,
    fun a b hab => g.injective (by simpa only [Function.comp_apply] using hab)⟩, ?_⟩
  -- P4ᶜ = (Gᶜ.comap g)ᶜ = G.comap g.
  have hcoe : (P4ᶜ) = G.comap (g : Fin 4 → α) := by
    have h1 : (P4ᶜ) = ((Gᶜ).comap g)ᶜ := by rw [← hg]
    rw [compl_comap _ _ (fun a b hab => g.injective hab),
      SimpleGraph.compl_compl] at h1
    exact h1
  -- P4 = (P4ᶜ).comap ψ⁻¹ (pull back along the reverse carrier).
  have h2 : P4 = (P4ᶜ).comap psiInv := by
    have h3 : (P4.comap psi).comap psiInv = P4.comap (psi ∘ psiInv) :=
      comap_comap' P4 psi psiInv
    rw [psi_comp, ← p4_compl_comap] at h3
    have h4 : P4.comap (id : Fin 4 → Fin 4) = P4 := SimpleGraph.comap_id
    rw [h4] at h3
    exact h3.symm
  rw [h2, hcoe]
  exact comap_comap' G _ _

/-! ### The card bookkeeping + the Seinsche split (strong induction) -/

/-- The card bookkeeping for the vertex-peel: |{x // x ≠ u}| + 1 = |α|. -/
theorem card_peel {α : Type} [Fintype α] [DecidableEq α] (u : α) :
    Fintype.card {x : α // x ≠ u} + 1 = Fintype.card α := by
  have h1 := Fintype.card_add_card_compl (p := fun x : α => x = u)
  have h2 : Fintype.card {x : α // x = u} = 1 := by
    haveI : Unique {x : α // x = u} :=
      ⟨⟨u, rfl⟩, fun y => Subtype.ext y.2⟩
    exact Fintype.card_unique
  have h3 : Fintype.card {x : α // ¬ (x = u)}
      = Fintype.card {x : α // x ≠ u} := rfl
  rw [h3] at h1
  omega

/-- **THE SEINCHE SPLIT** (1974): every P4-free graph on ≥ 2 vertices has a
separation — itself or its complement is disconnected (the explicit Finset
shape). Strong induction on the vertex count; the audit §1.1 case tree. -/
theorem seinsche_split_aux (n : ℕ) : ∀ (α : Type) [Fintype α] [DecidableEq α],
    Fintype.card α ≤ n → 2 ≤ Fintype.card α → ∀ (G : SimpleGraph α),
    P4free G →
    (∃ s : Finset α, s.Nonempty ∧ s ≠ Finset.univ ∧
      ∀ a ∈ s, ∀ b ∉ s, ¬ G.Adj a b) ∨
    (∃ s : Finset α, s.Nonempty ∧ s ≠ Finset.univ ∧
      ∀ a ∈ s, ∀ b ∉ s, ¬ (Gᶜ).Adj a b) := by
  induction n with
  | zero =>
      intro α _ _ hcard h2 _ _
      exfalso
      omega
  | succ n =>
      intro α _ _ hcard h2 G hP4
      by_cases hbase : Fintype.card α = 2
      · -- THE n = 2 BASE: the edge dichotomy (the world fact by the
        -- 3-in-2 pigeonhole).
        have he : α ≃ Fin 2 := by
          have h := Fintype.equivFin (α := α)
          rw [hbase] at h
          exact h
        have hxy : he.symm (0 : Fin 2) ≠ he.symm (1 : Fin 2) := by
          intro h
          have h2e : (he (he.symm (0 : Fin 2)))
              = (he (he.symm (1 : Fin 2))) := congrArg he h
          simp only [Equiv.apply_symm_apply] at h2e
          simp at h2e
        have hworld : ∀ v : α,
            v = he.symm (0 : Fin 2) ∨ v = he.symm (1 : Fin 2) := by
          intro v
          by_contra hv
          push_neg at hv
          have hinj : Function.Injective (fun i : Fin 3 =>
              ![he.symm (0 : Fin 2), he.symm (1 : Fin 2), v] i) := by
            intro i j h
            fin_cases i <;> fin_cases j <;>
              simp_all [Matrix.cons_val_zero, Matrix.cons_val_one,
                Matrix.cons_val_succ, Matrix.head_cons]
          have hcard := Fintype.card_le_of_injective
            (fun i : Fin 3 =>
              ![he.symm (0 : Fin 2), he.symm (1 : Fin 2), v] i) hinj
          simp at hcard
          omega
        by_cases hadj : G.Adj (he.symm (0 : Fin 2)) (he.symm (1 : Fin 2))
        · -- G has the edge: {x} separates the COMPLEMENT.
          refine Or.inr ⟨{he.symm (0 : Fin 2)},
            ⟨he.symm (0 : Fin 2), Finset.mem_singleton.2 rfl⟩, ?_, ?_⟩
          · intro hful
            have hym : he.symm (1 : Fin 2) ∈
                ({he.symm (0 : Fin 2)} : Finset α) := by
              rw [hful]; exact Finset.mem_univ _
            exact hxy (Finset.mem_singleton.1 hym)
          · intro a ha b hb hadjC
            have hax : a = he.symm (0 : Fin 2) := Finset.mem_singleton.1 ha
            have hbx : b ≠ he.symm (0 : Fin 2) :=
              fun h => hb (Finset.mem_singleton.2 h)
            have hby : b = he.symm (1 : Fin 2) := by
              rcases hworld b with h | h
              · exact absurd h hbx
              · exact h
            rw [hax, hby] at hadjC
            exact (SimpleGraph.compl_adj.1 hadjC).2 hadj
        · -- The pair is G-edgeless: {x} separates G.
          refine Or.inl ⟨{he.symm (0 : Fin 2)},
            ⟨he.symm (0 : Fin 2), Finset.mem_singleton.2 rfl⟩, ?_, ?_⟩
          · intro hful
            have hym : he.symm (1 : Fin 2) ∈
                ({he.symm (0 : Fin 2)} : Finset α) := by
              rw [hful]; exact Finset.mem_univ _
            exact hxy (Finset.mem_singleton.1 hym)
          · intro a ha b hb hadjG
            have hax : a = he.symm (0 : Fin 2) := Finset.mem_singleton.1 ha
            have hbx : b ≠ he.symm (0 : Fin 2) :=
              fun h => hb (Finset.mem_singleton.2 h)
            have hby : b = he.symm (1 : Fin 2) := by
              rcases hworld b with h | h
              · exact absurd h hbx
              · exact h
            rw [hax, hby] at hadjG
            exact hadj hadjG
      · -- THE RECURSION: peel u, apply the IH to G−u, run caseA.
        have h3 : 3 ≤ Fintype.card α := by omega
        obtain ⟨u⟩ : Nonempty α := by
          have hpos : 0 < Fintype.card α := by omega
          exact Fintype.card_pos_iff.1 hpos
        have hcardD := card_peel (α := α) u
        have hDfree : P4free (G.comap
            (Subtype.val : {x : α // x ≠ u} → α)) :=
          p4free_comap G _ Subtype.val_injective hP4
        have h2D : 2 ≤ Fintype.card {x : α // x ≠ u} := by omega
        have hnD : Fintype.card {x : α // x ≠ u} ≤ n := by omega
        obtain hsepD | hsepD :=
          seinsche_split_aux n {x : α // x ≠ u} hnD h2D _ hDfree
        · -- sep (G−u): extract the unreachable pair, run caseA on G.
          obtain ⟨s, hsne, hsne', hscross⟩ := hsepD
          by_cases hsepG : ∃ s : Finset α, s.Nonempty ∧ s ≠ Finset.univ ∧
              ∀ a ∈ s, ∀ b ∉ s, ¬ G.Adj a b
          · exact Or.inl hsepG
          · by_cases hsepGc : ∃ s : Finset α, s.Nonempty ∧ s ≠ Finset.univ ∧
              ∀ a ∈ s, ∀ b ∉ s, ¬ (Gᶜ).Adj a b
            · exact Or.inr hsepGc
            · exfalso
              have hconn := conn_of_no_sep G hsepG
              have hconnC := conn_of_no_sep (Gᶜ) hsepGc
              obtain ⟨x', hx'⟩ := hsne
              have hy' : ∃ a : {x : α // x ≠ u}, a ∉ s := by
                by_contra hcon
                push_neg at hcon
                exact hsne' (Finset.eq_univ_iff_forall.2 hcon)
              obtain ⟨y', hy'⟩ := hy'
              have hunreach : ¬ GReach
                  (G.comap (Subtype.val : {x : α // x ≠ u} → α)) x' y' := by
                intro hwalk
                obtain ⟨p, q, hps, hqs, hpq⟩ :=
                  walk_crosses hwalk s hx' hy'
                exact hscross p hps q hqs hpq
              exact caseA G u hconn hconnC hP4 x' y' hunreach
        · -- sep ((G−u)ᶜ) = sep (Gᶜ−u): run caseA on Gᶜ via the bridge.
          obtain ⟨s, hsne, hsne', hscross⟩ := hsepD
          have hcoe : ((G.comap
              (Subtype.val : {x : α // x ≠ u} → α))ᶜ) =
              (Gᶜ).comap (Subtype.val : {x : α // x ≠ u} → α) :=
            compl_comap G _ Subtype.val_injective
          by_cases hsepG : ∃ s : Finset α, s.Nonempty ∧ s ≠ Finset.univ ∧
              ∀ a ∈ s, ∀ b ∉ s, ¬ G.Adj a b
          · exact Or.inl hsepG
          · by_cases hsepGc : ∃ s : Finset α, s.Nonempty ∧ s ≠ Finset.univ ∧
              ∀ a ∈ s, ∀ b ∉ s, ¬ (Gᶜ).Adj a b
            · exact Or.inr hsepGc
            · exfalso
              have hconnC := conn_of_no_sep (Gᶜ) hsepGc
              have hconn : ∀ x y : α, GReach ((Gᶜ)ᶜ) x y := by
                rw [SimpleGraph.compl_compl]
                exact conn_of_no_sep G hsepG
              obtain ⟨x', hx'⟩ := hsne
              have hy' : ∃ a : {x : α // x ≠ u}, a ∉ s := by
                by_contra hcon
                push_neg at hcon
                exact hsne' (Finset.eq_univ_iff_forall.2 hcon)
              obtain ⟨y', hy'⟩ := hy'
              have hscross' : ∀ a ∈ s, ∀ b ∉ s,
                  ¬ ((Gᶜ).comap
                    (Subtype.val : {x : α // x ≠ u} → α)).Adj a b := by
                intro a ha b hb hadj
                rw [← hcoe] at hadj
                exact hscross a ha b hb hadj
              have hunreach : ¬ GReach
                  ((Gᶜ).comap (Subtype.val : {x : α // x ≠ u} → α))
                  x' y' := by
                intro hwalk
                obtain ⟨p, q, hps, hqs, hpq⟩ :=
                  walk_crosses hwalk s hx' hy'
                exact hscross' p hps q hqs hpq
              exact caseA (Gᶜ) u hconnC hconn (p4free_compl G hP4)
                x' y' hunreach

theorem seinsche_split {α : Type} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (hn : 2 ≤ Fintype.card α) (hP4 : P4free G) :
    (∃ s : Finset α, s.Nonempty ∧ s ≠ Finset.univ ∧
      ∀ a ∈ s, ∀ b ∉ s, ¬ G.Adj a b) ∨
    (∃ s : Finset α, s.Nonempty ∧ s ≠ Finset.univ ∧
      ∀ a ∈ s, ∀ b ∉ s, ¬ (Gᶜ).Adj a b) :=
  seinsche_split_aux (Fintype.card α) α (Nat.le_refl _) hn G hP4

/-! ## §5 THE WITNESS PRODUCT LAW -/

/-- The cograph product law with explicit witnesses: every P4-free graph on
`n` vertices carries an independent set `I` and a clique `K` with
`|I| * |K| ≥ n`. Strong induction (the DIY ∀-m ≤ n strengthening). -/
theorem p4_witness_product_aux (n : ℕ) : ∀ (α : Type) [Fintype α]
    [DecidableEq α], Fintype.card α ≤ n → ∀ (G : SimpleGraph α),
    P4free G →
    ∃ I K : Finset α, G.IsIndepSet (↑I : Set α) ∧ G.IsClique (↑K : Set α) ∧
      I.card * K.card ≥ Fintype.card α := by
  induction n with
  | zero =>
      intro α _ _ hcard G _
      have h0 : Fintype.card α = 0 := le_antisymm hcard (Nat.zero_le _)
      have hemp : IsEmpty α := Fintype.card_eq_zero.1 h0
      refine ⟨∅, ∅, ?_, ?_, ?_⟩
      · intro a ha _ _ _
        exact absurd ha (Set.notMem_empty a)
      · intro a ha _ _ _
        exact absurd ha (Set.notMem_empty a)
      · have h1 : (∅ : Finset α).card = 0 := Finset.card_empty
        omega
  | succ n =>
      intro α _ _ hcard G hP4
      by_cases hsmall : Fintype.card α ≤ 1
      · -- The ≤ 1 world: the full vertex set is both independent and a
        -- clique (no distinct pairs exist).
        rcases Nat.eq_zero_or_eq_one (Fintype.card α) with h0 | h1
        · have hemp : IsEmpty α := Fintype.card_eq_zero.1 h0
          refine ⟨∅, ∅, ?_, ?_, ?_⟩
          · intro a ha _ _ _
            exact absurd ha (Set.notMem_empty a)
          · intro a ha _ _ _
            exact absurd ha (Set.notMem_empty a)
          · have h1' : (∅ : Finset α).card = 0 := Finset.card_empty
            omega
        · obtain ⟨hu⟩ := Fintype.card_eq_one.1 h1
          haveI := hu
          refine ⟨Finset.univ, Finset.univ, ?_, ?_, ?_⟩
          · intro a _ b _ hab
            exact absurd hab (Subsingleton.elim a b)
          · intro a _ b _ hab
            exact absurd hab (Subsingleton.elim a b)
          · have h1' : (Finset.univ : Finset α).card = 1 := by
              rw [Finset.card_univ, h1]
            omega
      · -- The ≥ 2 world: split by Seinsche.
        have h2 : 2 ≤ Fintype.card α := by omega
        obtain hsep | hsep := seinsche_split G h2 hP4
        · -- THE UNION CASE: no cross G-edges between s and its complement.
          obtain ⟨s, hsne, hsne', hscross⟩ := hsep
          have hy' : ∃ y : α, y ∈ Finset.univ \ s := by
            by_contra hcon
            push_neg at hcon
            refine hsne' (Finset.eq_univ_iff_forall.2 fun a _ => ?_)
            by_contra has
            exact hcon a (Finset.mem_sdiff.2 ⟨Finset.mem_univ a, has⟩)
          obtain ⟨y, hy⟩ := hy'
          have hunivcard : (Finset.univ : Finset α).card
              = Fintype.card α := Finset.card_univ
          have hsdiffcard : (Finset.univ \ s).card
              = Fintype.card α - s.card := by
            rw [← hunivcard]
            exact Finset.card_sdiff (Finset.subset_univ s)
          have hspos : 0 < s.card := Finset.card_pos.2 hsne
          have hdiffpos : 0 < (Finset.univ \ s).card :=
            Finset.card_pos.2 ⟨y, hy⟩
          have hcard1 : Fintype.card {x : α // x ∈ s} = s.card :=
            Fintype.card_coe
          have hcard2 : Fintype.card {x : α // x ∈ Finset.univ \ s} =
              (Finset.univ \ s).card := Fintype.card_coe
          have hn1 : Fintype.card {x : α // x ∈ s} ≤ n := by
            rw [hcard1]; omega
          have hn2 : Fintype.card {x : α // x ∈ Finset.univ \ s} ≤ n := by
            rw [hcard2]; omega
          obtain ⟨I₁, K₁, hI₁, hK₁, hprod₁⟩ :=
            p4_witness_product_aux n {x : α // x ∈ s} hn1 _
              (p4free_comap G (Subtype.val : {x : α // x ∈ s} → α)
                Subtype.val_injective hP4)
          obtain ⟨I₂, K₂, hI₂, hK₂, hprod₂⟩ :=
            p4_witness_product_aux n {x : α // x ∈ Finset.univ \ s} hn2 _
              (p4free_comap G
                (Subtype.val : {x : α // x ∈ Finset.univ \ s} → α)
                Subtype.val_injective hP4)
          -- Transport to α.
          set I₁' : Finset α := I₁.image
            (Subtype.val : {x : α // x ∈ s} → α) with hI₁'def
          set I₂' : Finset α := I₂.image
            (Subtype.val : {x : α // x ∈ Finset.univ \ s} → α) with hI₂'def
          set K₁' : Finset α := K₁.image
            (Subtype.val : {x : α // x ∈ s} → α) with hK₁'def
          set K₂' : Finset α := K₂.image
            (Subtype.val : {x : α // x ∈ Finset.univ \ s} → α) with hK₂'def
          have hcardI₁' : I₁'.card = I₁.card := by
            rw [hI₁'def]
            exact Finset.card_image_of_injOn (fun _ _ _ _ h => Subtype.ext h)
          have hcardI₂' : I₂'.card = I₂.card := by
            rw [hI₂'def]
            exact Finset.card_image_of_injOn (fun _ _ _ _ h => Subtype.ext h)
          have hcardK₁' : K₁'.card = K₁.card := by
            rw [hK₁'def]
            exact Finset.card_image_of_injOn (fun _ _ _ _ h => Subtype.ext h)
          have hcardK₂' : K₂'.card = K₂.card := by
            rw [hK₂'def]
            exact Finset.card_image_of_injOn (fun _ _ _ _ h => Subtype.ext h)
          have hprod1' : I₁.card * K₁.card ≥ s.card := by
            rw [← hcard1]; exact hprod₁
          have hprod2' : I₂.card * K₂.card ≥ (Finset.univ \ s).card := by
            rw [← hcard2]; exact hprod₂
          have hdisj : Finset.Disjoint I₁' I₂' := by
            rw [Finset.disjoint_iff_inter_eq_empty]
            refine Finset.eq_empty_iff_forall_notMem.2 fun a ha => ?_
            obtain ⟨ha1, ha2⟩ := Finset.mem_inter.1 ha
            obtain ⟨a1, _, ha1v⟩ := Finset.mem_image.1 ha1
            obtain ⟨a2, _, ha2v⟩ := Finset.mem_image.1 ha2
            have h1 : a ∈ s := by rw [ha1v]; exact a1.2
            have h2 : a ∉ s := by
              have h2' : a ∈ Finset.univ \ s := by rw [ha2v]; exact a2.2
              exact fun hbs => (Finset.mem_sdiff.1 h2').2 hbs
            exact h2 h1
          have hIcard : (I₁' ∪ I₂').card = I₁'.card + I₂'.card :=
            Finset.card_disjoint_union hdisj
          -- The four membership helpers.
          have hindepUnion : G.IsIndepSet (↑(I₁' ∪ I₂') : Set α) := by
            intro a ha b hb hab
            have ha' : a ∈ I₁' ∪ I₂' := Finset.mem_coe.1 ha
            have hb' : b ∈ I₁' ∪ I₂' := Finset.mem_coe.1 hb
            rcases Finset.mem_union.1 ha' with ha1 | ha2
            · rcases Finset.mem_union.1 hb' with hb1 | hb2
              · obtain ⟨a1, ha1m, ha1v⟩ := Finset.mem_image.1 ha1
                obtain ⟨b1, hb1m, hb1v⟩ := Finset.mem_image.1 hb1
                have hne : a1 ≠ b1 := by
                  rintro h
                  exact hab (ha1v.trans (h ▸ hb1v))
                have hbadj := hI₁ a1 (Finset.mem_coe.2 ha1m)
                  b1 (Finset.mem_coe.2 hb1m) hne
                simp only [SimpleGraph.comap_adj] at hbadj
                rw [ha1v, hb1v] at hbadj
                exact hbadj
              · obtain ⟨a1, _, ha1v⟩ := Finset.mem_image.1 ha1
                obtain ⟨b2, _, hb2v⟩ := Finset.mem_image.1 ha2
                have hain : a ∈ s := by rw [ha1v]; exact a1.2
                have hbin : b ∉ s := by
                  have h2' : b ∈ Finset.univ \ s := by
                    rw [hb2v]; exact b2.2
                  exact fun hbs => (Finset.mem_sdiff.1 h2').2 hbs
                exact hscross a hain b hbin
            · rcases Finset.mem_union.1 hb' with hb1 | hb2
              · obtain ⟨a2, _, ha2v⟩ := Finset.mem_image.1 ha2
                obtain ⟨b1, _, hb1v⟩ := Finset.mem_image.1 hb1
                have hbin : b ∈ s := by rw [hb1v]; exact b1.2
                have hain : a ∉ s := by
                  have h2' : a ∈ Finset.univ \ s := by
                    rw [ha2v]; exact a2.2
                  exact fun hbs => (Finset.mem_sdiff.1 h2').2 hbs
                intro hadj
                exact hscross b hbin a hain (G.adj_symm hadj)
              · obtain ⟨a2, ha2m, ha2v⟩ := Finset.mem_image.1 ha2
                obtain ⟨b2, hb2m, hb2v⟩ := Finset.mem_image.1 hb2
                have hne : a2 ≠ b2 := by
                  rintro h
                  exact hab (ha2v.trans (h ▸ hb2v))
                have hbadj := hI₂ a2 (Finset.mem_coe.2 ha2m)
                  b2 (Finset.mem_coe.2 hb2m) hne
                simp only [SimpleGraph.comap_adj] at hbadj
                rw [ha2v, hb2v] at hbadj
                exact hbadj
          have hcliqueK₁ : G.IsClique (↑K₁' : Set α) := by
            intro a ha b hb hab
            obtain ⟨a1, ha1m, ha1v⟩ :=
              Finset.mem_image.1 (Finset.mem_coe.1 ha)
            obtain ⟨b1, hb1m, hb1v⟩ :=
              Finset.mem_image.1 (Finset.mem_coe.1 hb)
            have hne : a1 ≠ b1 := by
              rintro h
              exact hab (ha1v.trans (h ▸ hb1v))
            have hadj := hK₁ a1 (Finset.mem_coe.2 ha1m)
              b1 (Finset.mem_coe.2 hb1m) hne
            simp only [SimpleGraph.comap_adj] at hadj
            rw [ha1v, hb1v] at hadj
            exact hadj
          have hcliqueK₂ : G.IsClique (↑K₂' : Set α) := by
            intro a ha b hb hab
            obtain ⟨a2, ha2m, ha2v⟩ :=
              Finset.mem_image.1 (Finset.mem_coe.1 ha)
            obtain ⟨b2, hb2m, hb2v⟩ :=
              Finset.mem_image.1 (Finset.mem_coe.1 hb)
            have hne : a2 ≠ b2 := by
              rintro h
              exact hab (ha2v.trans (h ▸ hb2v))
            have hadj := hK₂ a2 (Finset.mem_coe.2 ha2m)
              b2 (Finset.mem_coe.2 hb2m) hne
            simp only [SimpleGraph.comap_adj] at hadj
            rw [ha2v, hb2v] at hadj
            exact hadj
          have hfull : s.card + (Finset.univ \ s).card
              = Fintype.card α := by omega
          rcases le_total K₁'.card K₂'.card with hkle | hkge
          · refine ⟨I₁' ∪ I₂', K₂', hindepUnion, hcliqueK₂, ?_⟩
            have hge1 : I₁.card * K₁.card ≤ I₁'.card * K₂'.card :=
              Nat.mul_le_mul (Nat.le_of_eq hcardI₁'.symm)
                (Nat.le_trans (Nat.le_of_eq hcardK₁'.symm) hkle)
            have hge2 : I₂.card * K₂.card ≤ I₂'.card * K₂'.card :=
              Nat.mul_le_mul (Nat.le_of_eq hcardI₂'.symm)
                (Nat.le_of_eq hcardK₂'.symm)
            have hsplit : (I₁' ∪ I₂').card * K₂'.card
                = I₁'.card * K₂'.card + I₂'.card * K₂'.card := by
              rw [hIcard, Nat.add_mul]
            have ha := hprod1'
            have hb := hprod2'
            omega
          · refine ⟨I₁' ∪ I₂', K₁', hindepUnion, hcliqueK₁, ?_⟩
            have hge1 : I₁.card * K₁.card ≤ I₁'.card * K₁'.card :=
              Nat.mul_le_mul (Nat.le_of_eq hcardI₁'.symm)
                (Nat.le_of_eq hcardK₁'.symm)
            have hge2 : I₂.card * K₂.card ≤ I₂'.card * K₁'.card :=
              Nat.mul_le_mul (Nat.le_of_eq hcardI₂'.symm)
                (Nat.le_trans (Nat.le_of_eq hcardK₂'.symm) hkge)
            have hsplit : (I₁' ∪ I₂').card * K₁'.card
                = I₁'.card * K₁'.card + I₂'.card * K₁'.card := by
              rw [hIcard, Nat.add_mul]
            have ha := hprod1'
            have hb := hprod2'
            omega
        · -- THE JOIN CASE: all cross pairs G-adjacent (the Gᶜ separation).
          obtain ⟨s, hsne, hsne', hscross⟩ := hsep
          have hy' : ∃ y : α, y ∈ Finset.univ \ s := by
            by_contra hcon
            push_neg at hcon
            refine hsne' (Finset.eq_univ_iff_forall.2 fun a _ => ?_)
            by_contra has
            exact hcon a (Finset.mem_sdiff.2 ⟨Finset.mem_univ a, has⟩)
          obtain ⟨y, hy⟩ := hy'
          have hunivcard : (Finset.univ : Finset α).card
              = Fintype.card α := Finset.card_univ
          have hsdiffcard : (Finset.univ \ s).card
              = Fintype.card α - s.card := by
            rw [← hunivcard]
            exact Finset.card_sdiff (Finset.subset_univ s)
          have hspos : 0 < s.card := Finset.card_pos.2 hsne
          have hdiffpos : 0 < (Finset.univ \ s).card :=
            Finset.card_pos.2 ⟨y, hy⟩
          have hcard1 : Fintype.card {x : α // x ∈ s} = s.card :=
            Fintype.card_coe
          have hcard2 : Fintype.card {x : α // x ∈ Finset.univ \ s} =
              (Finset.univ \ s).card := Fintype.card_coe
          have hn1 : Fintype.card {x : α // x ∈ s} ≤ n := by
            rw [hcard1]; omega
          have hn2 : Fintype.card {x : α // x ∈ Finset.univ \ s} ≤ n := by
            rw [hcard2]; omega
          obtain ⟨I₁, K₁, hI₁, hK₁, hprod₁⟩ :=
            p4_witness_product_aux n {x : α // x ∈ s} hn1 _
              (p4free_comap G (Subtype.val : {x : α // x ∈ s} → α)
                Subtype.val_injective hP4)
          obtain ⟨I₂, K₂, hI₂, hK₂, hprod₂⟩ :=
            p4_witness_product_aux n {x : α // x ∈ Finset.univ \ s} hn2 _
              (p4free_comap G
                (Subtype.val : {x : α // x ∈ Finset.univ \ s} → α)
                Subtype.val_injective hP4)
          set I₁' : Finset α := I₁.image
            (Subtype.val : {x : α // x ∈ s} → α) with hI₁'def
          set I₂' : Finset α := I₂.image
            (Subtype.val : {x : α // x ∈ Finset.univ \ s} → α) with hI₂'def
          set K₁' : Finset α := K₁.image
            (Subtype.val : {x : α // x ∈ s} → α) with hK₁'def
          set K₂' : Finset α := K₂.image
            (Subtype.val : {x : α // x ∈ Finset.univ \ s} → α) with hK₂'def
          have hcardI₁' : I₁'.card = I₁.card := by
            rw [hI₁'def]
            exact Finset.card_image_of_injOn (fun _ _ _ _ h => Subtype.ext h)
          have hcardI₂' : I₂'.card = I₂.card := by
            rw [hI₂'def]
            exact Finset.card_image_of_injOn (fun _ _ _ _ h => Subtype.ext h)
          have hcardK₁' : K₁'.card = K₁.card := by
            rw [hK₁'def]
            exact Finset.card_image_of_injOn (fun _ _ _ _ h => Subtype.ext h)
          have hcardK₂' : K₂'.card = K₂.card := by
            rw [hK₂'def]
            exact Finset.card_image_of_injOn (fun _ _ _ _ h => Subtype.ext h)
          have hprod1' : I₁.card * K₁.card ≥ s.card := by
            rw [← hcard1]; exact hprod₁
          have hprod2' : I₂.card * K₂.card ≥ (Finset.univ \ s).card := by
            rw [← hcard2]; exact hprod₂
          have hdisj : Finset.Disjoint K₁' K₂' := by
            rw [Finset.disjoint_iff_inter_eq_empty]
            refine Finset.eq_empty_iff_forall_notMem.2 fun a ha => ?_
            obtain ⟨ha1, ha2⟩ := Finset.mem_inter.1 ha
            obtain ⟨a1, _, ha1v⟩ := Finset.mem_image.1 ha1
            obtain ⟨a2, _, ha2v⟩ := Finset.mem_image.1 ha2
            have h1 : a ∈ s := by rw [ha1v]; exact a1.2
            have h2 : a ∉ s := by
              have h2' : a ∈ Finset.univ \ s := by rw [ha2v]; exact a2.2
              exact fun hbs => (Finset.mem_sdiff.1 h2').2 hbs
            exact h2 h1
          have hKcard : (K₁' ∪ K₂').card = K₁'.card + K₂'.card :=
            Finset.card_disjoint_union hdisj
          have hcliqueUnion : G.IsClique (↑(K₁' ∪ K₂') : Set α) := by
            intro a ha b hb hab
            have ha' : a ∈ K₁' ∪ K₂' := Finset.mem_coe.1 ha
            have hb' : b ∈ K₁' ∪ K₂' := Finset.mem_coe.1 hb
            rcases Finset.mem_union.1 ha' with ha1 | ha2
            · rcases Finset.mem_union.1 hb' with hb1 | hb2
              · obtain ⟨a1, ha1m, ha1v⟩ := Finset.mem_image.1 ha1
                obtain ⟨b1, hb1m, hb1v⟩ := Finset.mem_image.1 hb1
                have hne : a1 ≠ b1 := by
                  rintro h
                  exact hab (ha1v.trans (h ▸ hb1v))
                have hadj := hK₁ a1 (Finset.mem_coe.2 ha1m)
                  b1 (Finset.mem_coe.2 hb1m) hne
                simp only [SimpleGraph.comap_adj] at hadj
                rw [ha1v, hb1v] at hadj
                exact hadj
              · obtain ⟨a1, _, ha1v⟩ := Finset.mem_image.1 ha1
                obtain ⟨b2, _, hb2v⟩ := Finset.mem_image.1 ha2
                have hain : a ∈ s := by rw [ha1v]; exact a1.2
                have hbin : b ∉ s := by
                  have h2' : b ∈ Finset.univ \ s := by
                    rw [hb2v]; exact b2.2
                  exact fun hbs => (Finset.mem_sdiff.1 h2').2 hbs
                have hne : a ≠ b := by
                  rintro h
                  rw [h] at hain
                  exact hbin hain
                by_contra hg
                exact hscross a hain b hbin (SimpleGraph.compl_adj.2 ⟨hne, hg⟩)
            · rcases Finset.mem_union.1 hb' with hb1 | hb2
              · obtain ⟨a2, _, ha2v⟩ := Finset.mem_image.1 ha2
                obtain ⟨b1, _, hb1v⟩ := Finset.mem_image.1 hb1
                have hbin : b ∈ s := by rw [hb1v]; exact b1.2
                have hain : a ∉ s := by
                  have h2' : a ∈ Finset.univ \ s := by
                    rw [ha2v]; exact a2.2
                  exact fun hbs => (Finset.mem_sdiff.1 h2').2 hbs
                have hne : a ≠ b := by
                  rintro h
                  rw [h] at hbin
                  exact hain hbin
                by_contra hg
                exact hscross b hbin a hain
                  (SimpleGraph.compl_adj.2
                    ⟨Ne.symm hne, fun h => hg (G.adj_symm h)⟩)
              · obtain ⟨a2, ha2m, ha2v⟩ := Finset.mem_image.1 ha2
                obtain ⟨b2, hb2m, hb2v⟩ := Finset.mem_image.1 hb2
                have hne : a2 ≠ b2 := by
                  rintro h
                  exact hab (ha2v.trans (h ▸ hb2v))
                have hadj := hK₂ a2 (Finset.mem_coe.2 ha2m)
                  b2 (Finset.mem_coe.2 hb2m) hne
                simp only [SimpleGraph.comap_adj] at hadj
                rw [ha2v, hb2v] at hadj
                exact hadj
          have hindepI₁ : G.IsIndepSet (↑I₁' : Set α) := by
            intro a ha b hb hab
            obtain ⟨a1, ha1m, ha1v⟩ :=
              Finset.mem_image.1 (Finset.mem_coe.1 ha)
            obtain ⟨b1, hb1m, hb1v⟩ :=
              Finset.mem_image.1 (Finset.mem_coe.1 hb)
            have hne : a1 ≠ b1 := by
              rintro h
              exact hab (ha1v.trans (h ▸ hb1v))
            have hbadj := hI₁ a1 (Finset.mem_coe.2 ha1m)
              b1 (Finset.mem_coe.2 hb1m) hne
            simp only [SimpleGraph.comap_adj] at hbadj
            rw [ha1v, hb1v] at hbadj
            exact hbadj
          have hindepI₂ : G.IsIndepSet (↑I₂' : Set α) := by
            intro a ha b hb hab
            obtain ⟨a2, ha2m, ha2v⟩ :=
              Finset.mem_image.1 (Finset.mem_coe.1 ha)
            obtain ⟨b2, hb2m, hb2v⟩ :=
              Finset.mem_image.1 (Finset.mem_coe.1 hb)
            have hne : a2 ≠ b2 := by
              rintro h
              exact hab (ha2v.trans (h ▸ hb2v))
            have hbadj := hI₂ a2 (Finset.mem_coe.2 ha2m)
              b2 (Finset.mem_coe.2 hb2m) hne
            simp only [SimpleGraph.comap_adj] at hbadj
            rw [ha2v, hb2v] at hbadj
            exact hbadj
          have hfull : s.card + (Finset.univ \ s).card
              = Fintype.card α := by omega
          rcases le_total I₁'.card I₂'.card with hile | hige
          · refine ⟨I₂', K₁' ∪ K₂', hindepI₂, hcliqueUnion, ?_⟩
            have hge1 : I₁.card * K₁.card ≤ I₂'.card * K₁'.card :=
              Nat.mul_le_mul (Nat.le_trans (Nat.le_of_eq hcardI₁'.symm) hile)
                (Nat.le_of_eq hcardK₁'.symm)
            have hge2 : I₂.card * K₂.card ≤ I₂'.card * K₂'.card :=
              Nat.mul_le_mul (Nat.le_of_eq hcardI₂'.symm)
                (Nat.le_of_eq hcardK₂'.symm)
            have hsplit : I₂'.card * (K₁' ∪ K₂').card
                = I₂'.card * K₁'.card + I₂'.card * K₂'.card := by
              rw [hKcard, Nat.mul_add]
            have ha := hprod1'
            have hb := hprod2'
            omega
          · refine ⟨I₁', K₁' ∪ K₂', hindepI₁, hcliqueUnion, ?_⟩
            have hge1 : I₁.card * K₁.card ≤ I₁'.card * K₁'.card :=
              Nat.mul_le_mul (Nat.le_of_eq hcardI₁'.symm)
                (Nat.le_of_eq hcardK₁'.symm)
            have hge2 : I₂.card * K₂.card ≤ I₁'.card * K₂'.card :=
              Nat.mul_le_mul (Nat.le_trans (Nat.le_of_eq hcardI₂'.symm) hige)
                (Nat.le_of_eq hcardK₂'.symm)
            have hsplit : I₁'.card * (K₁' ∪ K₂').card
                = I₁'.card * K₁'.card + I₁'.card * K₂'.card := by
              rw [hKcard, Nat.mul_add]
            have ha := hprod1'
            have hb := hprod2'
            omega

theorem p4_witness_product {α : Type} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (hP4 : P4free G) :
    ∃ I K : Finset α, G.IsIndepSet (↑I : Set α) ∧ G.IsClique (↑K : Set α) ∧
      I.card * K.card ≥ Fintype.card α :=
  p4_witness_product_aux (Fintype.card α) α (Nat.le_refl _) G hP4

/-! ## §6 THE √n FLOOR + THE RPOW FINISHER (the 61A green chain, ported) -/

/-- `n ≤ m² → √n ≤ m` (DIY: by_contra + Nat.lt_sqrt + ring + omega — the
ring normalization is mandatory, omega sees (m+1)² as one atom). -/
theorem sqrt_le_of_sq {n m : ℕ} (h : n ≤ m * m) : Nat.sqrt n ≤ m := by
  by_contra hcon
  push_neg at hcon
  have h2 : m * m < n := Nat.lt_sqrt.1 hcon
  have h4 : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
  omega

/-- The Arsenal dyadic threshold: `0 < 4` and `2 ≤ 4` from `two_pow_pos`
[CardinalWorlds.lean:420] and `two_pow_ge2` [CardinalWorlds.lean:431] at
`j = 2` (root-namespace declarations; the 61A green bridge, ported
verbatim). -/
theorem arsenal_threshold : (0:ℕ) < 4 ∧ 2 ≤ 4 := by
  have h1 : (0:ℕ) < 2^2 := two_pow_pos 2
  have h2 : (2:ℕ) ≤ 2^2 := two_pow_ge2 2 (by norm_num)
  have e : (2:ℕ)^2 = 4 := by decide
  rw [e] at h1 h2
  exact ⟨h1, h2⟩

/-- For `n ≥ 4`: `n ≤ (Nat.sqrt n) ^ 4` (via `n < (s+1)² ≤ (s·s)²`,
`s ≥ 2`). (61A green, ported verbatim.) -/
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

/-- The real finisher: `(n : ℝ)^(1/4) ≤ Nat.sqrt n` for `n ≥ 4`.
(61A green, ported verbatim.) -/
theorem rpow_quarter_le_sqrt {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) ^ ((1:ℝ) / 4) ≤ (Nat.sqrt n : ℝ) := by
  have hx : (0:ℝ) ≤ ((Nat.sqrt n : ℕ) : ℝ) := by positivity
  have hkey : (n : ℝ) ≤ ((Nat.sqrt n : ℕ) : ℝ) ^ (((4:ℕ):ℝ)) := by
    have h0 : (n : ℝ) ≤ ((Nat.sqrt n : ℕ) : ℝ) ^ (4:ℕ) := by
      exact_mod_cast le_sqrt_pow_four hn
    rw [Real.rpow_natCast]
    exact h0
  have h1 : (n : ℝ) ^ ((1:ℝ)/4)
      ≤ (((Nat.sqrt n : ℕ) : ℝ) ^ (((4:ℕ):ℝ))) ^ ((1:ℝ)/4) :=
    Real.rpow_le_rpow (by positivity) hkey (by positivity)
  refine le_trans h1 ?_
  have h2 : (((Nat.sqrt n : ℕ) : ℝ) ^ (((4:ℕ):ℝ))) ^ ((1:ℝ)/4)
      = ((Nat.sqrt n : ℕ) : ℝ) ^ ((((4:ℕ):ℝ) * ((1:ℝ)/4))) :=
    (Real.rpow_mul hx ((4:ℕ):ℝ) ((1:ℝ)/4)).symm
  have h3 : (((4:ℕ):ℝ) * ((1:ℝ)/4)) = 1 := by ring
  rw [h3] at h2
  rw [h2, Real.rpow_one]

/-- The dichotomy finisher: `indepNum` or `cliqueNum` ≥ `Nat.sqrt n`
implies the official bound at `c = 1/4` (for `n ≥ 4`). (61A green, ported.) -/
theorem official_bound_of_sqrt {n : ℕ} (hn : 4 ≤ n) {G : SimpleGraph (Fin n)}
    (h : G.indepNum ≥ Nat.sqrt n ∨ G.cliqueNum ≥ Nat.sqrt n) :
    G.indepNum ≥ (n : ℝ) ^ ((1:ℝ)/4) ∨ G.cliqueNum ≥ (n : ℝ) ^ ((1:ℝ)/4) := by
  have hle := rpow_quarter_le_sqrt hn
  rcases h with h | h
  · left; exact le_trans hle (Nat.cast_le.2 h)
  · right; exact le_trans hle (Nat.cast_le.2 h)

/-! ## §7 THE OFFICIAL THEOREMS -/

/-- The official-level complement transfer: `H` at `f` ⟹ `Hᶜ` at `f`.
(61A green, ported verbatim.) -/
theorem isEH_compl {α : Type*} [Fintype α] [DecidableEq α]
    {H : SimpleGraph α} {f : ℕ → ℝ}
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

/-- **THE EIGHTH FAMILY MEMBER — P4**: the official Erdős–Hajnal lower
bound for the 4-vertex path at `c = 1/4`, over the official predicate.
Route: Seinsche split → the witness product law → the integer-√ floor →
the max-case dichotomy → the 61A rpow finisher. -/
theorem eh_P4 : IsErdosHajnalLowerBound P4 (fun n => (n : ℝ) ^ ((1:ℝ)/4)) := by
  rw [IsErdosHajnalLowerBound, Filter.eventually_atTop]
  refine ⟨4, ?_⟩
  intro n hn G hG
  -- The official no-copy hypothesis IS P4free at α := Fin n (audit §3).
  obtain ⟨I, K, hI, hK, hprod⟩ := p4_witness_product (α := Fin n) G hG
  have hcard : Fintype.card (Fin n) = n := by simp
  rw [hcard] at hprod
  set M := Nat.max I.card K.card with hM
  have hM1 : I.card ≤ M := by rw [hM]; exact Nat.le_max_left _ _
  have hM2 : K.card ≤ M := by rw [hM]; exact Nat.le_max_right _ _
  have hmul : I.card * K.card ≤ M * M := Nat.mul_le_mul hM1 hM2
  have hsq : Nat.sqrt n ≤ M := sqrt_le_of_sq (le_trans hprod hmul)
  rcases le_total I.card K.card with hI' | hI'
  · have hle := SimpleGraph.IsClique.card_le_cliqueNum (t := K) (tc := hK)
    have hKeq : K.card = M := by rw [hM]; exact Nat.max_eq_right hI'
    rw [hKeq] at hle
    exact official_bound_of_sqrt hn (Or.inr (le_trans hsq hle))
  · have hle := SimpleGraph.IsIndepSet.card_le_indepNum (t := I) (tc := hI)
    have hIeq : I.card = M := by rw [hM]; exact Nat.max_eq_left hI'
    rw [hIeq] at hle
    exact official_bound_of_sqrt hn (Or.inl (le_trans hsq hle))

/-- **P̄4**: by the complement transfer. -/
theorem eh_Pbar4 : IsErdosHajnalLowerBound (P4ᶜ)
    (fun n => (n : ℝ) ^ ((1:ℝ)/4)) := isEH_compl eh_P4

/-- **THE BOARD**: the P4/P̄4 pair at the uniform exponent c = 1/4 over the
official predicate (mirrors 61D's erdos_61_k5_e5). -/
theorem erdos_61_p4 : ∃ c > (0:ℝ),
    IsErdosHajnalLowerBound P4 (fun n => (n : ℝ) ^ c) ∧
    IsErdosHajnalLowerBound (P4ᶜ) (fun n => (n : ℝ) ^ c) := by
  refine ⟨(1:ℝ)/4, by positivity, ?_, ?_⟩
  · exact eh_P4
  · exact eh_Pbar4

end Erdos61E

#print axioms Erdos61E.last_exit
#print axioms Erdos61E.walk_crosses
#print axioms Erdos61E.seinsche_split
#print axioms Erdos61E.p4_witness_product
#print axioms Erdos61E.sqrt_le_of_sq
#print axioms Erdos61E.eh_P4
#print axioms Erdos61E.eh_Pbar4
#print axioms Erdos61E.erdos_61_p4
#print axioms Erdos61E.arsenal_threshold

#eval "DM61E_P4_GREEN"
