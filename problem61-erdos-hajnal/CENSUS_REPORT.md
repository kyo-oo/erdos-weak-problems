# Erdős #61 — CENSUS REPORT (S060, W1-T3b salvage + commander)

## The exhaustive censuses (complete unconditional finite theorems)

m(H, n) = min over H-INDUCED-free graphs G on n vertices of max(ω(G), α(G)).
Every cell = full enumeration (no sampling). n = 7: all 2,097,152 graphs.
Source: census_engine.py (the fallen agent's engine, output recovered:
census_results_n1-7.json + n8_state.json).

| H \ n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8* |
|---|---|---|---|---|---|---|---|---|
| E₃ | 1 | 2 | 2 | 2 | 2 | 3 | 3 | 3 |
| K₂+E₁ | 1 | 2 | 2 | 2 | 3 | 3 | 3 | 3 |
| P₃ | 1 | 2 | 2 | 2 | 3 | 3 | 3 | 3 |
| K₃ | 1 | 2 | 2 | 2 | 2 | 3 | 3 | 3 |
| E₄ | 1 | 2 | 2 | 2 | 2 | 3 | 3 | 3 |
| K₂+2E₁ | 1 | 2 | 2 | 2 | 2 | 3 | 3 | 3 |
| 2K₂ | 1 | 2 | 2 | 2 | 2 | 3 | 3 | 3 |
| P₃+E₁ | 1 | 2 | 2 | 2 | 2 | 3 | 3 | 3 |
| P₄ | 1 | 2 | 2 | 2 | 3 | 3 | 3 | 3 |
| C₄ | 1 | 2 | 2 | 2 | 2 | 3 | 3 | 3 |
| K₃+E₁ | 1 | 2 | 2 | 2 | 2 | 3 | 3 | 3 |
| paw | 1 | 2 | 2 | 2 | 2 | 3 | 3 | 3 |
| diamond | 1 | 2 | 2 | 2 | 2 | 3 | 3 | 3 |
| K₄ | 1 | 2 | 2 | 2 | 2 | 3 | 3 | 3 |
| K₁,₃ | 1 | 2 | 2 | 2 | 2 | 3 | 3 | 3 |
| P₅ | 1 | 2 | 2 | 2 | 2 | 3 | 3 | 3 |
| C₅ | 1 | 2 | 2 | 2 | 3 | 3 | 3 | 3 |
| bull | 1 | 2 | 2 | 2 | 2 | 3 | 3 | 3 |
| K₅ | 1 | 2 | 2 | 2 | 2 | 3 | 3 | 3 |
| E₅ | 1 | 2 | 2 | 2 | 2 | 3 | 3 | 3 |
| house | 1 | 2 | 2 | 2 | 2 | 3 | 3 | 3 |

*n = 8: the lower side m ≥ 3 is Ramsey-universal (R(3,3) = 6 ≤ 8: every
graph on ≥ 6 vertices has ω ≥ 3 or α ≥ 3); the upper side m ≤ 3 by the
recovered n=8 witnesses (all 21 H-families had certified witnesses in the
partial sweep state before the agent's context death). m(H, 8) = 3 for all
21 H.

## Reading the table (the theory interlock)

- m(H, n) ≥ 3 exactly from n = 6 for EVERY H — the R(3,3) = 6 wall, the
  census confirming classical Ramsey cell-by-cell.
- The P₄ and P₃/K₂+E₁/C₅ rows reach m = 3 already at n = 5 — these H force
  structure earliest, consistent with the cograph law ω·α ≥ n (P₄-free:
  max ≥ √5 ⟹ ≥ 3) and the C₅-free theory.
- The K₃/E₃ rows: m = 2 at n = 5 (the C₅ witness: triangle-free AND
  α = 2 — the Ramsey-extremal), m = 3 from n = 6 — exactly the
  L₃(n) values of Theorem 1 (L₃(5) = 2, L₃(6) = 3): **the census values
  EQUAL the Ramsey-exact lower bounds L₃(n) — the theorem's constants are
  TIGHT at these cells.**
- The verify_theorems.py interlock: every ring theorem re-verified on all
  graphs n ≤ 7 — ALL GREEN (after the Turán-route audit correction).

## The dual-verification layer

The engine's design (per its header, recovered): V1 slow-census (different
algorithm) for n ≤ 5 all H + n = 6 spot H's; V2 Z3 UNSAT certificates for
selected (H, n) — both layers recorded in the engine output.

## Files

- experiments/census_engine.py (the engine), census_results_n1-7.json (the
  tables + witnesses), n8_state.json (the partial n = 8 sweep + witnesses)
- experiments/verify_theorems.py + verify_theorems_results.json (the ring
  verification, ALL GREEN)
