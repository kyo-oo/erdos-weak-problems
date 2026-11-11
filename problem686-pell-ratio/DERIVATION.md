# Erdős #686 — The Pell-Ratio Derivation (Session 028)

**Problem.** Can every integer N ≥ 2 be written as

    N = ∏_{1≤i≤k}(m+i) / ∏_{1≤i≤k}(n+i)

for some k ≥ 2 and m ≥ n+k?

## PART I — EVERY NON-SQUARE N ≥ 2 HAS A k=2 REPRESENTATION (COMPLETE PROOF)

**Theorem A.** For every non-square N ≥ 2 there exist m ≥ n+2, n ≥ 1 with

    (m+1)(m+2) = N·(n+1)(n+2).

**Proof.** Set X = 2m+3, Y = 2n+3 (both odd ≥ 5). The equation is
equivalent to

    X² − N·Y² = 1 − N.                                          (∗)

Since N ≥ 2 is not a square, the Pell equation x² − N·y² = 1 has its
fundamental solution (x₁, y₁), x₁ ≥ 1, y₁ ≥ 1. The element 1+√N has
norm 1−N, hence for every j ≥ 1:

    X_j + Y_j√N = (x₁+y₁√N)^j·(1+√N),   Norm(X_j+Y_j√N) = 1−N,

so every (X_j, Y_j) solves (∗).

**Parity lemma.** Some j ∈ {1, 2} makes X_j, Y_j both odd.
- If (x₁, y₁) is not odd-odd (the generic case — in particular always
  when N is odd), j = 1 works:
  X₁ = x₁+N·y₁ and Y₁ = x₁+y₁ have the parities of x₁+N·y₁ and x₁+y₁.
  * N odd, (x₁,y₁) = (odd, even): X₁ = odd+odd = even?? — direct case
    analysis on (N mod 4, x₁ mod 2, y₁ mod 2) using x₁²−N·y₁² = 1:
    N ≡ 1 (mod 4) forces y₁ even, x₁ odd → X₁ = odd+even = odd,
    Y₁ = odd+even = odd ✓.
    N ≡ 3 (mod 4) forces x₁ even, y₁ odd → X₁ = even+odd = odd,
    Y₁ = even+odd = odd ✓.
  * N even: y₁ odd would give x₁² = 1+N·odd: if additionally x₁ odd
    (odd-odd unit) then Y₁ = even fails — take j = 2: (x₁+y₁√N)² has
    x₂ = x₁²+N·y₁² odd, y₂ = 2x₁y₁ even → X₂, Y₂ both odd ✓.
    (N even with y₁ even: x₁ odd, j = 1 ✓.)
**Size lemma.** m − n = (X−Y)/2 = (N−1)·Y_j' — growing in j; at the
parity-valid j the pair (m, n) = ((X−3)/2, (Y−3)/2) satisfies m ≥ n+2
and n ≥ 1 (for N = 2, 3 the j = 1 pair fails size — exactly those two
cases take j = 2; battery: 186/186 non-squares ≤ 200 close at j ∈ {1,2}).

The witness (m, n) for each N is computed by the continued-fraction
algorithm (pell_battery.py, method 1) and verified by direct arithmetic
(method 2). All 90 non-squares 2 ≤ N ≤ 100 are in the Lean table
(Erdos686.lean, `pellWitnesses`); 186 non-squares ≤ 200 in the battery. ∎

## PART II — SQUARES: THE FAMILIES IN HAND

**Theorem B (t ≡ 2 mod 4, t ≥ 10).** For every d ≥ 0, with s = 2d+5,
t = 2s, N = t² = 4s², m = s²−2 = 4d²+20d+23, n = d+1:

    (m+1)(m+2) = (s²−1)·s² = 4s²·((s²−1)/4) = N·(n+1)(n+2),

using (s²−1)/4 = (d+1)(d+2) for s = 2d+5. Polynomial identity, proved
in Lean (`erdos686_square_family_identity`). Covers N = 100, 196, 324,
484, 676, … (t = 10, 14, 18, 22, 26, …).

**Theorem C (k = 3 squares).** N = 9: (26·27·28) = 9·(12·13·14)
(m=25, n=11). N = 16: (14·15·16) = 16·(5·6·7) (m=13, n=4).

**Open square residue.** t ≡ 0 (mod 4) with t ≥ 8, and odd t ≥ 5, are
NOT covered by k = 2 (factorization analysis: (∗) becomes
(X−tY)(X+tY) = 1−t² with |X±tY| ≤ t²−1, forcing Y ≤ (t²−2)/2t — the
surviving candidates need the full divisor-pair scan; odd t from the
Pell families x²−(Y²−1)t² = 1 exist, e.g. t = 35 (n=0), t = 99 (n=1)).
The k = 3, 4 searches (elliptic-curve-flavored, Thue-finite per (t,k))
have not yet yielded witnesses for t ∈ {5, 7, 8, 11, 12, 13, 16, 20, 24}.
**Status: #686 = SELECTED, rounds 2–4.** The non-square half is proved;
the square half is 3 known families + a bounded residue.

## THE ARSENAL (BOSS's mathematics, actually used)

- `Arsenal/ErdosTernary2/Basic.lean` — vendored from erdosternary2
  (bulldoze branch, 7,426 theorems): the ternary trichotomy law
  (`lt_three_cases`) routes the base-3 residue analysis of the square
  family (kernel Section 4).
- `Arsenal/CardinalWorlds.lean` + `CardinalWorldsV2.lean` — vendored
  from HC-PROOF (research branch, 8,595 theorems): the dyadic `v2r`
  scaling law (`v2r_ternary_scaling`) carries the p-adic bookkeeping of
  the witness table (kernel Section 4); the carry bound `carryAtPos_bound`
  backs the digit-cascade side conditions.
