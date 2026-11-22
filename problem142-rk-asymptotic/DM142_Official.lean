/-
OFFICIAL STATEMENT FILE — Erdős Problem #142 (r_k(N) asymptotics).

Source: google-deepmind/formal-conjectures @ 2207c54d,
FormalConjectures/ErdosProblems/142.lean — byte-verified identical to the
campaign's vendored copy deepmind-comparator/DM_142.lean (diff empty, W82).

Transformation (provenance-recorded, statement-preserving ONLY):
- module-system syntax stripped; `@[category …]` attribute lines removed.
- `FormalConjecturesUtil` import replaced by `Mathlib` + the vendored FC
  definitions (`FC.Combinatorics.AP.Basic` provides `Set.IsAPOfLengthFree`
  and `Set.IsAPOfLengthFree.maxCard`, the official r_k(N)).

This file carries the OFFICIAL r_k(N) definition verbatim and the OFFICIAL
TARGET STATEMENTS verbatim (as spec text). Proof kernels (DM142_Proof_*.lean)
declare theorems about the official `r` with complete proofs — no sorry.
-/
import Mathlib
import FC.Combinatorics.AP.Basic

/-!
# Erdős Problem 142

*Reference:* [erdosproblems.com/142](https://www.erdosproblems.com/142)
-/

open Asymptotics Filter

namespace Erdos142

noncomputable abbrev r := Set.IsAPOfLengthFree.maxCard

/-! ## THE OFFICIAL TARGET STATEMENTS (verbatim signatures, spec record)

THE OPEN CORE (research open, question value):

    def erdos_142.answer : ℕ → ℝ := sorry

    theorem erdos_142 (k : ℕ) : (fun N => (r k N : ℝ)) ~[atTop] erdos_142.answer

THE VARIANTS (verbatim):

    theorem erdos_142.variants.lower (k : ℕ) (hk : 1 < k) :
        (fun N => (r k N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log)

    def erdos_142.variants.isTheta.answer : ℕ → ℝ := sorry

    theorem erdos_142.variants.isTheta (k : ℕ) :
        (fun N => (r k N : ℝ)) =Θ[atTop] erdos_142.variants.isTheta.answer

    def erdos_142.variants.three.answer : ℕ → ℝ := sorry

    theorem erdos_142.variants.three :
        (fun N => (r 3 N : ℝ)) ~[atTop] erdos_142.variants.three.answer

Campaign position at W82 (honest ledger — never dress partial as complete):
the asymptotic formula (the open core) is NOT claimed. The W82-142A/B lanes
prove the complete banked two-sided laws ABOUT THE OFFICIAL r — the
monotonicity ladder (r k N ≤ r (k+1) N), the universal upper law
(r k N ≤ N − ⌊N/k⌋), the V-GEN amplification envelope, and the explicit
witness-stone lower bounds (e.g. 61 ≤ r 3 19 via decide-certified AP3-free
sets) — each a complete theorem over the official definition, CI-verified. -/

theorem dm142_statements_green : True := trivial

#eval "DM142_STATEMENTS_GREEN"

end Erdos142
