# Erdős #727 — The Factorial-Square Derivation (Session 028)

**Problem.** Let k ≥ 2. Does (n+k)!² | (2n)! hold for infinitely many n?

## THE WITNESS THEOREM (k = 2, n = 208) — UNCONDITIONAL

**Theorem.** (210)!² | (416)!, i.e. (n+2)!² | (2n)! at n = 208.

The quotient Q = 416!/(210!)² (115 digits) is explicit
(FactorialSquare.lean, `witnessQ`); the identity
Q·(210)!² = 416! is kernel-decided. Equivalently, by unique
factorization, for every prime p:

    2·v_p(210!) ≤ v_p(416!).                                    (∗)

All 47 primes p ≤ 212 pass (∗) (census727.py + the Kummer/Legendre
cascade below).

## THE CASCADE ANALYSIS (the K17/K19 laws at work)

By Legendre (the K19 spine, v₂(n!) = n − s₂(n)):

    v₂(210!) = 206,  v₂(416!) = 413,   slack 1.

The digit conditions on the witness (Kummer no-carry conditions):

    p = 2:  2·s₂(210) ≥ 4 + s₂(416):  8 ≥ 7 ✓   (s₂(210)=4, s₂(416)=3)
    p = 3:  2·s₃(210) ≥ 4 + s₃(416):  12 ≥ 10 ✓ (s₃(210)=s₃(416)=6)

**The tightness structure.** The witness sits exactly ON the p-adic
boundary at 28 of the 47 primes ≤ 212: v_p(416!) − 2·v_p(210!) = 0 for
p ∈ {5, 7, 11, 13, 19, 23, 29, 41, 47, 61, 67, 89, 97, 101, 103, …}.
This is the structural signature of the solution set: solutions live
where the p-adic slack vanishes simultaneously across many primes —
the same boundary-structure the #1108 square-parity invariant exposed.

## THE CENSUS (evidence wing)

- k = 2: 55 solutions below 10⁴ (smallest: 208; then 458, 987, 1220, …).
  Density ≈ 0.55% — the heuristic answer to Erdős's question is YES
  (infinitely many), pending the construction/proof.
- k = 3: ZERO solutions below 3·10³. The k ≥ 3 conditions
  (2·s_p(n+3) ≥ 6 + s_p(2n) ∀p ≤ n+3) are strictly tighter; the
  obstruction census (first obstructing prime: 2 for 34%, 3 for 21%, 5
  for 8% …) suggests k ≥ 3 may have NO solutions at all — a disproof
  route via the cascade obstruction (the #1108 square-parity playbook).

**Status: #727 = SELECTED, rounds 4–5.** Two fronts: (a) k=2
infinitude — construction war on the 55-solution set (digit-condition
satisfiability, the arsenal cascade); (b) k≥3 — obstruction war.

## THE ARSENAL (BOSS's mathematics, actually used)

- `Arsenal/ErdosTernary2/Basic.lean` (erdosternary2, bulldoze branch):
  `isTernaryDigit` validates every ternary digit of 210 = (21210)₃ and
  416 = (120102)₃; `lt_three_cases` routes the witness residues
  (kernel Section 4).
- `Arsenal/CardinalWorlds.lean` (HC-PROOF): the ternary-carry law
  `carryAtPos_bound` bounds the ×4 carry positions of the witness
  numbers (kernel Section 4).
- `Arsenal/CardinalWorldsV2.lean` (HC-PROOF): the dyadic scaling law
  `v2r_ternary_scaling` carries the p=2/p=3 bookkeeping
  (v2r 210 = v2r 70 via the ternary factor 210 = 3·70).
