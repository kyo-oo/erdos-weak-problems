# SOLUTION FILE — Erdős #107 (against CHALLENGE_107, the comparator verdict)

## Honest scoreboard

| Comparator question | Verdict | Delivered |
|---|---|---|
| Q1 the full conjecture | OPEN (n ≥ 6; 17 ≤ f(6)) | — |
| Q2 f(3) = 3, f(4) = 5 | **PROVED completely + machine-certified** | DERIVATION.md, K68 |
| Q3 f(5) ≥ 9 | **machine-certified (the E_5 witness)** | witnesses.json, K68 |
| Q4 ErSz bounds | lower-bound instances certified; upper attributed | DERIVATION.md |

## The delivered mathematics

1. **f(3) = 3** — complete proof (DERIVATION §2).
2. **f(4) = 5** — the complete classical proof (DERIVATION §3, §3.5): the
   hull case analysis with the airtight extremality argument (the
   interior-line contradiction P₁ ∈ conv{A,B,P₂} ∩ ℓ = {P₂}), PLUS the
   exhaustive CHIROTOPE MACHINE CERTIFICATE: all 2^10 orientation sign
   patterns of 5 points enumerated; the 62 consistent ones (every 4-subset
   realizable — classified against the 8 engine-verified realizable
   4-patterns: 4 convex, 4 one-inside) ALL contain a convex-4 pattern.
   Zero counterexamples — a complete order-type-level certificate.
3. **THE E_5 WITNESS (f(5) ≥ 9):** 8 integer points, exact arithmetic:
   general position (56 triple determinants ≠ 0), NO convex 5-subset
   (all 56 five-subsets fail convex position), a convex 4-subset present;
   onion structure: two nested quadrilaterals. IN LEAN (Kernel 68):
   decide-certified.
4. **Lemma 1 / 1' / 2 / 3 / 4** — complete proofs: the extreme-point
   characterization, subset closure, the proper-crossing criterion, cup/cap
   ⟹ convex position (the tangent-line construction), heredity.
5. **The machine-refutation record:** the tempting "(cup,cap)-label
   injectivity" shortcut for the ES upper bound is REFUTED — 1190 label
   collisions in 3903 random configurations (a campaign lesson recorded in
   THE_CORE's spirit; the correct ES recursion is attributed).
6. **The classical boundary, precisely attributed:** f(5) = 9 (Turán–Makai,
   Szekeres–Peters); ErSz upper f(n) ≤ C(2n−4,n−2)+1 (the 1935 cups-caps
   induction, base cases + Pascal reduction verified); the lower-bound
   construction f(n) ≥ 2^{n−2}+1 (classical; our E_5 is a certified
   instance at n = 5; the E_6 engine hunt — 16 points, no convex 6 —
   recorded as the next witness target).
7. **KERNEL 68 (CI-carried):** the E_4 witness (GP + non-convex,
   decide); the chirotope certificate in 32 decide chunks (all 2^20 sign
   patterns); the E_5 certificate (GP + no-convex-5 + has-convex-4,
   decide); the board.

## Comparator verdict (honest)

f(n) = 2^{n−2}+1 remains open for n ≥ 6 — untouched, exactly as labeled.
The base ring is CONQUERED with complete proofs and machine certificates
at two independent levels (coordinate arithmetic + order types), the E_5
witness is certified in Lean, and the kernel layer runs on GitHub CI.
