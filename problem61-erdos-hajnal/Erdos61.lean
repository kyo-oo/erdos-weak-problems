import Mathlib

/-!
# Erdos61 — THE ERDŐS–HAJNAL KERNEL (Kernel #61, Task 2-a-S, W1-B1S) — STATEMENT-ONLY

Target (verbatim): "For any graph H is there some c = c(H) > 0 such that every
graph G on n vertices that does not contain H as an induced subgraph contains
either a complete graph or independent set on ≥ n^c vertices?" — the
Erdős–Hajnal conjecture.  OPEN in general.

This file is the STATEMENT-ONLY kernel of the strike: the theorem statements
of PROOF.md, as `Prop` definitions.  NO proofs, NO `sorry`, NO
`native_decide`, NO tactics — statements only, built from quantifiers and
`SimpleGraph` primitives (`⊤` = complete graph, `⊥` = edgeless graph).
Authored in a sandbox with no Lean toolchain (boss override), so this file is
UNCOMPILED here; the repo comparator CI is the verifier of record (the same
discipline as Arsenal/CardinalWorlds.lean).  NO PUSH.

Companion artifacts: engine61.py, receipts61.txt (machine receipts cited in
PROOF.md §6), PROOF.md (complete unconditional proofs of Theorems 1–4;
Theorem 5 cited as the certified baseline; the full conjecture remains OPEN).
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000000

namespace Erdos61

/-! ## §0 The master statement (the conjecture itself — OPEN) -/

/-- An injective map `Fin k → Fin n` whose image induces exactly `H`. -/
def InducedCopy {n k : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin k))
    (φ : Fin k → Fin n) : Prop :=
  Function.Injective φ ∧ ∀ x y : Fin k, G.Adj (φ x) (φ y) ↔ H.Adj x y

/-- `G` avoids `H` as an induced subgraph. -/
def Avoids {n k : ℕ} (G : SimpleGraph (Fin n)) (H : SimpleGraph (Fin k)) : Prop :=
  ∀ φ : Fin k → Fin n, Function.Injective φ → ¬ InducedCopy G H φ

/-- Homogeneous set: clique or independent set. -/
def IsHomogeneous {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  (∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y) ∨
  (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ G.Adj x y)

/-- The Erdős–Hajnal property for a fixed `H` (on `Fin k`) with exponent
`c > 0`: every H-free graph on `n` vertices has a homogeneous set of size at
least `n ^ c`. -/
def ErdosHajnalFor (k : ℕ) (H : SimpleGraph (Fin k)) (c : ℝ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    Avoids G H → ∃ S : Finset (Fin n),
      IsHomogeneous G S ∧ (n : ℝ) ^ c ≤ (S.card : ℝ)

/-- THE MASTER STATEMENT (the fortress target — OPEN in general): for every
H there is a positive exponent. -/
def ErdosHajnalConjecture : Prop :=
  ∀ (k : ℕ) (H : SimpleGraph (Fin k)), ∃ c : ℝ, 0 < c ∧ ErdosHajnalFor k H c

/-! ## §1 THEOREM 1 (K₂): c = 1 (the maximum possible exponent). -/

/-- **Theorem 1 (statement).**  Every K₂-free graph on `n` vertices is
edgeless, hence the whole vertex set is an independent set of size `n`. -/
def Theorem61_1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    Avoids G (⊤ : SimpleGraph (Fin 2)) →
      ∃ S : Finset (Fin n),
        S = Finset.univ ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ G.Adj x y

/-! ## §2 THEOREM 2 (P₃): structure classification + the ⌈√n⌉ law. -/

/-- The P₃-avoidance predicate, written out (no graph constant needed):
no triple with two adjacent edges and a non-edge across them. -/
def AvoidsP3 {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ x y z : Fin n, ¬ (G.Adj x y ∧ G.Adj y z ∧ ¬ G.Adj x z)

/-- The clique-union structure predicate, written out as the local form of
"disjoint union of cliques": every neighborhood is a clique (equivalent to
every component being a clique — Theorem 2 of PROOF.md). -/
def IsDisjointUnionOfCliques {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v x y : Fin n, x ≠ v → y ≠ v → x ≠ y → G.Adj v x → G.Adj v y → G.Adj x y

/-- **Theorem 2 (statement).**  (i)+(ii) P₃-free graphs are exactly the
disjoint unions of cliques (both directions, as the equivalence of the two
predicates); (iii) every P₃-free graph on `n` vertices has a homogeneous set
of size `t` with `t * t ≥ n` (i.e. `t ≥ ⌈√n⌉`). -/
def Theorem61_2 : Prop :=
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      AvoidsP3 G ↔ IsDisjointUnionOfCliques G) ∧
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      AvoidsP3 G →
        ∃ S : Finset (Fin n), IsHomogeneous G S ∧ S.card * S.card ≥ n)

/-! ## §3 THEOREM 3K₁): the complement-side law t(t+1) ≥ n. -/

/-- The 3K₁-avoidance predicate, written out: no independent triple. -/
def Avoids3K1 {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ x y z : Fin n, ¬ (¬ G.Adj x y ∧ ¬ G.Adj x z ∧ ¬ G.Adj y z)

/-- **Theorem 3 (statement).**  Every 3K₁-free graph on `n` vertices has a
*clique* of size `t` with `t * (t + 1) ≥ n` — the sharp complement-side law
`t = ⌈(√(4n+1) − 1)/2⌉ ≥ ⌊√n⌋`; hence a homogeneous set of that size. -/
def Theorem61_3 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    Avoids3K1 G →
      ∃ S : Finset (Fin n),
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y) ∧ S.card * (S.card + 1) ≥ n

/-! ## §4 THEOREM 4 (substitution closure — the uniform blow-up frame). -/

/-- Uniform blow-up frame: a partition into nonempty classes that are
pairwise fully joined or fully non-joined, with quotient `Q`. -/
def IsUniformBlowup {n q : ℕ} (G : SimpleGraph (Fin n))
    (P : Fin q → Finset (Fin n)) (Q : SimpleGraph (Fin q)) : Prop :=
  (∀ i, (P i).Nonempty) ∧
  (∀ i j : Fin q, i ≠ j →
    (Q.Adj i j ∧ ∀ x ∈ P i, ∀ y ∈ P j, G.Adj x y) ∨
    (¬ Q.Adj i j ∧ ∀ x ∈ P i, ∀ y ∈ P j, ¬ G.Adj x y))

/-- **Theorem 4A(1) (statement) — the transversal law.**  In a uniform
blow-up, homogeneous sets of the quotient blow up pointwise: every pair of
vertices from classes indexed by a clique of `Q` is adjacent, and every pair
from classes indexed by an independent set of `Q` is non-adjacent — so every
transversal is a clique / independent set of `G`. -/
def Theorem61_4A_transversal : Prop :=
  ∀ (n q : ℕ) (G : SimpleGraph (Fin n)) (P : Fin q → Finset (Fin n))
    (Q : SimpleGraph (Fin q)),
    IsUniformBlowup G P Q →
    (∀ S : Finset (Fin q),
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → Q.Adj i j) →
        ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, G.Adj x y) ∧
    (∀ S : Finset (Fin q),
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬ Q.Adj i j) →
        ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∀ x ∈ P i, ∀ y ∈ P j, ¬ G.Adj x y)

/-- The class `S` of `G`, as an induced subgraph, avoids `H₂` (written with
plain quantifiers over the ambient vertex type). -/
def ClassAvoids {n b : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (H₂ : SimpleGraph (Fin b)) : Prop :=
  ∀ φ : Fin b → Fin n, Function.Injective φ → (∀ x, φ x ∈ S) →
    ¬ (∀ x y : Fin b, G.Adj (φ x) (φ y) ↔ H₂.Adj x y)

/-- **Theorem 4B (statement) — exponent composition `f = c₁c₂/(c₁+c₂)`.**
If `H₁` and `H₂` satisfy EH with exponents `c₁, c₂ > 0`, then every uniform
blow-up with `q` classes of size `≥ s` whose quotient avoids `H₁` or some
class avoids `H₂` (the avoidance disjunction that H₁[H₂]-freeness provides,
Theorem 4A(2) in PROOF.md) has a homogeneous set of size ≥
`min (q ^ c₁) (s ^ c₂)`; at the balanced split `q * s = n`, `q ^ c₁ = s ^ c₂`
this is `n ^ f` with `f = c₁ * c₂ / (c₁ + c₂)` — the exact optimum of the
frame. -/
def Theorem61_4B : Prop :=
  ∀ (a b : ℕ) (H₁ : SimpleGraph (Fin a)) (H₂ : SimpleGraph (Fin b))
    (c₁ c₂ : ℝ), 0 < c₁ → 0 < c₂ →
    ErdosHajnalFor a H₁ c₁ → ErdosHajnalFor b H₂ c₂ →
    ∀ (n q s : ℕ) (G : SimpleGraph (Fin n)) (P : Fin q → Finset (Fin n))
      (Q : SimpleGraph (Fin q)),
      IsUniformBlowup G P Q → (∀ i, s ≤ (P i).card) →
      (Avoids Q H₁ ∨ ∃ i, ClassAvoids G (P i) H₂) →
      ∃ S : Finset (Fin n),
        IsHomogeneous G S ∧
        min ((q : ℝ) ^ c₁) ((s : ℝ) ^ c₂) ≤ (S.card : ℝ)

/-- **Theorem 4C (statement) — multi-level iteration.**  The harmonic
composition law for k-level substitution chains: `F₂ = c₁c₂/(c₁+c₂)` and
`F₃ = f(F₂, c₃) = 1/(1/c₁ + 1/c₂ + 1/c₃)` (symmetric identity,
machine-receipt [A6] in receipts61.txt; the general law is
`F_k = (Σ 1/c_i)⁻¹`). -/
def Theorem61_4C : Prop :=
  ∀ (c₁ c₂ c₃ : ℝ), 0 < c₁ → 0 < c₂ → 0 < c₃ →
    (c₁ * c₂ / (c₁ + c₂)) * c₃ / (c₁ * c₂ / (c₁ + c₂) + c₃)
      = 1 / (1 / c₁ + 1 / c₂ + 1 / c₃)

/-! ## §5 THEOREM 5 (the certified baseline — cited, not proved here). -/

/-- **Theorem 5 (statement, as cited baseline).**  For every fixed nonempty
`H` there is `c_H > 0` such that every H-free graph on `n ≥ 2` vertices
contains a homogeneous set of size ≥ `exp(c_H * √(log n))` (classical
Erdős–Hajnal 1977 baseline; the modern refinement
`exp(c_H √(log n log log n))` is [BNSS23]).  Context only — used as a step by
nothing in this kernel. -/
def Theorem61_5 : Prop :=
  ∀ (k : ℕ) (H : SimpleGraph (Fin k)), 0 < k →
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), 2 ≤ n →
        Avoids G H →
        ∃ S : Finset (Fin n),
          IsHomogeneous G S ∧ Real.exp (c * Real.sqrt (Real.log n)) ≤ (S.card : ℝ)

end Erdos61
