# SOLUTION FILE — Erdős #61 (against CHALLENGE_61, the comparator verdict)

## Honest scoreboard

| Comparator question | Verdict | Delivered |
|---|---|---|
| Q1 full conjecture | OPEN (fortress) | — |
| Q2 the H-families with complete proofs | **DELIVERED: the complete ≤3-vertex family + P₄, K_t, E_t with explicit constants** | DERIVATION.md |
| Q3 finite shadows m(H,n) | **DELIVERED: n ≤ 7 exhaustive (21 H-families) + n = 8 witnesses** | CENSUS data + K67 |

## The delivered mathematics

1. **THEOREM RING (DERIVATION.md — every proof complete and self-contained):**
   - Lemma A: complement duality (ω/α swap, H ↔ H̄).
   - Lemma R: the Ramsey recursion R(k,l) ≤ R(k−1,l) + R(k,l−1) with
     R(k,l) ≤ C(k+l−2, k−1) — the 5-line Erdős–Szekeres induction, fully
     proved.
   - **Theorem 1 (K_t, t ≥ 3):** every induced-K_t-free G on n vertices has
     α(G) ≥ L_t(n) = max{l : R(t,l) ≤ n} ≥ n^{1/(t−1)}/8 for
     n ≥ (8(t−2))^{t−1}; any c < 1/(t−1) works eventually. MACHINE-AUDITED:
     an earlier draft's Turán-route claim (α ≥ n/(t−1)) was REFUTED by the
     exhaustive census (C₅: α = 2 < 2.5) and replaced by the correct
     Ramsey-route proof — the engine caught the error.
   - **Theorem 2 (E_t):** by duality, same constants.
   - **Theorem 3 (P₃):** components are cliques; ω·α ≥ n; c = 1/2 TIGHT
     (s·K_s family) — complete shortest-path proof.
   - **Theorem 4 (K₂+E₁):** by duality, c = 1/2 tight.
   - **Theorem 5 (P₄ decomposition):** every P₄-free graph with ≥ 2 vertices
     is disconnected or co-disconnected — complete induction proof
     (every case branch written out; verified on all P₄-free graphs n ≤ 7:
     78,416 graphs at n = 7).
   - **Theorem 6 (P₄):** ω·α ≥ n for every cograph; c = 1/2 TIGHT
     (s·K_s and its complement).
   - **Corollary: the FULL ≤ 3-vertex H family has the Erdős–Hajnal
     property** — every one of the four unlabeled graphs on ≤ 3 vertices,
     with explicit constants and complete proofs.
2. **THE CENSUS (n ≤ 7 exhaustive, 21 H-families):** m(H, n) tables for all
   H on ≤ 4 vertices + P₅, C₅, bull, K₅, E₅, house; every table entry a
   complete unconditional finite theorem by exhaustive enumeration
   (2,097,152 graphs at n = 7); n = 8 witnesses for all 21 H (m(H,8) = 3,
   lower side by Ramsey R(3,3) = 6, upper side by certified witnesses).
   Spot dual-verification (Z3 UNSAT) on selected cells.
3. **KERNEL 67 (CI-carried):** R(3,3) = 6 decide-certified over all 2^15
   graphs (32 chunks); the C₅ tightness; the K₃ laws at n = 5, 6 (α ≥ 2, 3);
   the P₄ decomposition + ω·α ≥ n at n = 5 (all 1024 graphs); the P₃ law;
   the 2·K₂ tightness family.
4. **The verify_theorems engine:** every DERIVATION claim machine-verified
   on all graphs n ≤ 7 — ALL GREEN (after the audit caught and fixed the
   Turán-route error).

## Comparator verdict (honest)

The general conjecture remains open (frontier: BNSS23 for all H; all H on
≤ 5 vertices known by research mathematics). Our ring: the complete
≤ 3-vertex family + the P₄/K_t/E_t families with explicit constants and
complete proofs, the exhaustive n ≤ 7 census for 21 H-families, and the
kernel layer on CI.
