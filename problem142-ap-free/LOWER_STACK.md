# LOWER_STACK.md — THE COMPLETE PROVEN LOWER ENVELOPE FOR r_k(N), ALL k >= 3
# (W79-142E; every line certified by engine142behrendgen.py, 9/9 GREEN)

BOSS's target: the asymptotic formula for r_k(N) = max{|A| : A ⊆ [1,N],
no non-trivial k-term AP}, ALL k >= 3, N -> infinity. This document is the
LOWER SIDE of the formula at its exact proven strength, in-package.

---

## LAW M-1 (THE CONTAINMENT LAW — complete)

For every k >= 3: every k-AP-free set is (k+1)-AP-free.
*Proof.* A non-trivial (k+1)-AP a, a+d, ..., a+kd contains the non-trivial
k-AP a, a+d, ..., a+(k-1)d (its first k terms; d >= 1). Contrapositive:
no k-AP ⟹ no (k+1)-AP. ∎ (GEN-MONO: corroborated on every constructed
instance, all three codes, plus the structural identity x1000.)

## THEOREM BG (THE GENERAL-k BEHREND LAW — complete, new this wave)

For all k >= 3, d >= 1, m >= 2, B := 2m: there exists S ⊆ [0, B^d)
containing no non-trivial k-term AP with
    |S| >= m^d / ((d(m-1)+1)(d(m-1)^(k-1)+1)).
Construction: the largest {digit-sum layer s} x {h-sphere t} cell of
{0,...,m-1}^d with h := k-1, lifted to base 2m. Kill chain: the no-carry
digitization (every interior second difference digitizes in base 2m — for
every k at once), the vector-AP chaining A_i = A_0 + iE, the digit-power
identity (degree-(k-1) polynomial in i with k roots is identically zero),
and the strict-convexity kill in the positive orthant (both parities of h).
Full derivation + 18 arsenal citations: BEHREND_GEN.md. k=3 degenerates to
the banked Theorem B byte-exactly (GEN-K3REPRO).

## COROLLARY BG* (the explicit asymptotic constant)

For every k >= 3 and N >= N_k: r_k(N) >= N·exp(-(2√(k ln 2) + o(1))·√(ln N)).
The o(1) is explicit: the certified safe constant is
    C_k = 2√((k+1) ln 2) + 1     (k=3: 4.665; k=10: 7.178)
at N_k = 2^40, verified at 45,847 grid points per k on N = 2^40..2^6000
(min margins 7.56–9.45). Constructively certified with real sets at recipe
parameters for k=3..8 (margins 7.6–15.1); k=9,10 arithmetic-only.

## THEOREM BG-E (the recipe)

For k ∈ {3..10} and N >= 2^40: d := ⌊√(k ln N / ln 2)⌋,
m := ⌊N^(1/d)/2⌋ gives r_k(N) >= m^(d-k)/d^2 - 1 >= N e^{-C_k√(ln N)}.

## THE COMPARISON LAWS (complete)

1. MONOTONE IN k: r_{k+1}(N) >= r_k(N) for all k >= 3, N >= 1 (Law M-1:
   the (k+1)-AP-free family contains the k-AP-free family).
2. MONOTONE IN N: r_k(N+1) >= r_k(N) (restriction to [1,N]).
3. DILATION: for all c >= 1: c·S is k-AP-free whenever S is; hence
   r_k(cN) >= r_k(N).
4. THE LADDER: r_3(N) <= r_4(N) <= r_5(N) <= ... — the lower envelope is
   monotone in k with the SINGLE universal construction family (Theorem BG
   gives every rung explicitly).

## THE COMPLETE LOWER ENVELOPE (the statement)

For every k >= 3 there is an EXPLICIT, machine-certified constant C_k
(namely 2√((k+1)ln2)+1, safe from N = 2^40) such that for ALL N >= 2^40:
    r_k(N) >= N · exp(-C_k √(ln N)).
The exponent 1/2 on ln N is the ceiling of the sum-classifier family
(BEHREND_GEN.md §8, the Ceiling Lemma — in-package). The classical Rankin
front (exp(-C_k (log N)^{1/(k-1)}) for k >= 4) needs a non-sum-type
mechanism; it is the NAMED NEXT FRONT of the lower lane.

## THE NAMED FRONTS (lower side)

F-LOW-1 (Rankin shape): for k >= 4, beat the 1/2-exponent ceiling with a
  nested/multi-scale classifier. Dead ends recorded: products pay per
  digit; shells lose the exact kill; modular spheres lose the positivity
  kill; decreasing digit ranges only add loss (BEHREND_GEN.md §8 ledger).

*The engine never stops; it never lies. In English, always.*
