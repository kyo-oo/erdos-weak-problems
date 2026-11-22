/-
OFFICIAL STATEMENT FILE — Erdős Problem #61 (Erdős–Hajnal Conjecture).

Source: google-deepmind/formal-conjectures @ 2207c54d,
FormalConjectures/ErdosProblems/61.lean — byte-verified identical to the
campaign's vendored copy deepmind-comparator/DM_61.lean (diff empty, W82).

Transformation (provenance-recorded, statement-preserving ONLY):
- module-system syntax stripped (`module`, `public import` -> `import`,
  `@[expose] public section` removed, `@[category …]` attribute lines
  removed — attributes are metadata, not statement content).
- `FormalConjecturesUtil` import replaced by `Mathlib` +
  the vendored FC definitions (`FC.Combinatorics.SimpleGraph.PathGraph`
  provides `pathGraph`, referenced-but-undefined in the upstream file).

This file carries the OFFICIAL DEFINITION `IsErdosHajnalLowerBound` verbatim
and the OFFICIAL TARGET STATEMENTS verbatim (as spec text). Proof kernels
(DM61_Proof_*.lean) must declare each target theorem with a byte-identical
statement signature and a complete proof — no sorry, no hidden hypotheses.
-/
import Mathlib
import FC.Combinatorics.SimpleGraph.PathGraph

/-!
# Erdős Problem 61 -- Erdős–Hajnal Conjecture

*Reference:* [erdosproblems.com/61](https://www.erdosproblems.com/61)
-/

open Filter
open SimpleGraph
open Real

namespace Erdos61

/-
For a graph $H$, consider all graphs $G$ that do not contain $H$ as an induced subgraph.
We would like to find a lower bound $f(n)$ such that every such $G$ on $n$ vertices
has a clique or independent set of size $\ge f(n)$ for sufficiently large $n$.
-/
def IsErdosHajnalLowerBound {α : Type*} [Fintype α] [DecidableEq α]
  (H : SimpleGraph α) (f : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ G : SimpleGraph (Fin n),
    (¬∃ g : α ↪ Fin n, H = G.comap g) → G.indepNum ≥ f n ∨ G.cliqueNum ≥ f n

/-! ## THE OFFICIAL TARGET STATEMENTS (verbatim signatures, spec record)

THE OPEN CORE (research open):

    theorem erdos_61 :
        ∀ {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
          ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H (fun n : ℕ => (n : ℝ) ^ c)

THE SOLVED VARIANTS (the official decomposition; the W82 kill targets):

    theorem erdos_61.variants.erha89 :
        ∀ {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
          ∃ c > (0 : ℝ), IsErdosHajnalLowerBound H (fun n : ℕ => exp (c * sqrt (log n)))

    theorem erdos_61.variants.bnss23 :
        ∀ {α : Type*} [Fintype α] [DecidableEq α] (H : SimpleGraph α),
          ∃ c > (0 : ℝ),
            IsErdosHajnalLowerBound H (fun n : ℕ => exp (c * sqrt (log n * log (log n))))

    theorem erdos_61.variants.p5 :
        ∃ c > (0 : ℝ), IsErdosHajnalLowerBound (pathGraph 5) (fun n : ℕ => (n : ℝ) ^ c)

    theorem erdos_61.variants.c5 :
        ∃ c > (0 : ℝ), IsErdosHajnalLowerBound (cycleGraph 5) (fun n : ℕ => (n : ℝ) ^ c)

Campaign position at W82 (honest ledger — never dress partial as complete):
the open core `erdos_61` is NOT claimed. The banked in-frame family results
(F7 + P4, the K5/E5 Ramsey routes, the 32/34 five-vertex closure map) are
being lifted to the official `IsErdosHajnalLowerBound` statement form by the
W82-61A/B lanes, and the classical solved variant `erha89` is the primary
W82 Lean target. -/

theorem dm61_statements_green : True := trivial

#eval "DM61_STATEMENTS_GREEN"

end Erdos61
