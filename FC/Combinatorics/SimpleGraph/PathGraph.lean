/-
Vendored for the Erdős weak-problems campaign (W82 foundation).

`FormalConjectures/ErdosProblems/61.lean` of google-deepmind/formal-conjectures
@ 2207c54d references `pathGraph` in the official statement of
`erdos_61.variants.p5` (the path graph P₅). At the campaign's pinned toolchain
(leanprover/lean4:v4.33.0-rc2, Mathlib v4.33.0-rc2) no `pathGraph` exists in
Mathlib or in `FormalConjecturesForMathlib` (verified against the repo at
2207c54d — only `cycleGraph` exists, in `Mathlib.Combinatorics.SimpleGraph.
CycleGraph`). This file provides the canonical definition, following the
style of `SimpleGraph.cycleGraph`.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

namespace SimpleGraph

variable (n : ℕ)

/-- The path graph `Pₙ` on `Fin n`: vertices `0, …, n-1` with edges exactly
between consecutive integers. `pathGraph 5` is the P₅ of
`erdos_61.variants.p5`. -/
def pathGraph : SimpleGraph (Fin n) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm := by
    intro a b h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  loopless := by
    intro a h
    rcases h with h | h
    · omega
    · omega

@[simp]
theorem pathGraph_adj {n : ℕ} {i j : Fin n} :
    (pathGraph n).Adj i j ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := Iff.rfl

theorem pathGraph_card_adj {n : ℕ} {i j : Fin n} (h : (pathGraph n).Adj i j) :
    i.val + j.val ≥ 1 := by
  rcases h with h | h <;> omega

end SimpleGraph
