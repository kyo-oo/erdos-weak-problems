# CENSUS_VERIFICATION.md — THE 61E GROUND TRUTH (W75, S074)

VERDICT: ALL GREEN (receipts61census.txt + census61.json, wall 537s).

1. THE CENSUS (n = 1..8, exact): h_H(n) = min over H-free graphs of
   max(alpha,omega), computed exhaustively (n<=7 full labeled enumeration;
   n=8: the 2^28 m=3-stratum exhaustive scan + the universal floor m>=3).
   The five 61K targets' rows (n=2..8): C4, 2K2, paw, diamond, K2+2K1 ALL
   = [2,2,2,2,3,3,3] — rho exponents at n=8: 0.528 for each. Dual
   independent implementation lanes agree everywhere (n=7 both lanes).
2. THE BATTERY: alpha/omega/containment cross-checks — 0 disagreements;
   complement self-test h_H == h_Hbar: 0 mismatches; h monotone: clean;
   inheritance law (CORRECTED direction, the W75 commander fix: H induced
   in H' => h_H >= h_H'): 0 violations.
3. THE LEMMA VERDICTS (E9 — the adversarial catches):
   - L1/L2 (Reiman/KST edge bounds): FALSE in the induced-C4-free reading
     (K4, diamond counterexamples), TRUE in the subgraph reading —
     certified; any use must scope subgraph.
   - L4a ('paw-free => N(v) P3-free'): FALSE — the diamond (paw-free) is
     the counterexample; the CORRECT law L4b: paw-free => N(v) is 2K2-free
     (0 violations, certified) — an induced 2K2 in N(v) completes an
     induced paw with center v.
   - L4c ('diamond-free => N(v) P3-free'): TRUE (15,573 graphs, 0
     violations) — the W75-61K THEOREM DIAMOND's law, independently
     certified here.
   - L5 (P3-free => disjoint union of cliques): the checker's first
     implementation was buggy (open-neighborhood comparison); corrected to
     the transitivity check: 0 violations; the P3-free counts equal the
     Bell numbers at every n — the classical law certified.
4. THE WITNESS FAMILIES: block graphs, C5-blowups, Petersen (rho 0.602),
   Clebsch (rho 0.581), polarity graphs ER_2 (rho 0.565) / ER_3 (0.627)
   (prime fields; ER_4/ER_5 scoped out — GF(4) is not Z/4).
5. BANKED-CLAIM RE-DERIVATION: every banked #61 claim (F7 family, Seinsche,
   CLAW, RAM) re-derived from the census numbers — all consistent.

The census is the ground truth the theorems must clear; the 61K package
clears it. The engine never stops; it never lies.
