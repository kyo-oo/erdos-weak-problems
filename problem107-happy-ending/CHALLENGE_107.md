# CHALLENGE FILE — Erdős #107 (the comparator target)

## Source A — erdosproblems.com/107 (verbatim)

> Let $f(n)$ be minimal such that any $f(n)$ points in $\mathbb{R}^2$, no
> three on a line, contain $n$ points which form the vertices of a convex
> $n$-gon. Prove that $f(n)=2^{n-2}+1$.

Prize: $500 (proof) / $100 (disproof). Known: f(3)=3, f(4)=5 (Klein 1931),
f(5)=9 (Turán–Makai; Szekeres–Peters); ErSz bounds 2^{n−2}+1 ≤ f(n) ≤
C(2n−4,n−2)+1; Suk 2017: f(n) ≤ 2^{(1+o(1))n}; HMPT20: f(n) ≤
2^{n+O(√(n log n))}. Open for n ≥ 6 (17 ≤ f(6)).

## Source B — Google DeepMind formal-conjectures (ErdosProblems/107.lean, verbatim)

```
def cardSet (n : ℕ) := { N | ∀ (pts : Finset ℝ²), pts.card = N → NonTrilinear (pts : Set ℝ²) →
  HasConvexNGon n pts }

noncomputable def f (n : ℕ) : ℕ := sInf (cardSet n)

@[category research open, question, AMS 52]
theorem erdos_107 : ∀ n ≥ 3, f n = 2^(n - 2) + 1

@[category research solved, AMS 52, formal_proof using lean4 at
  "https://github.com/linrock/math-proofs/blob/.../erdos-107/Solution.lean#L59"]
theorem nonempty_cardSet : ∀ n ≥ 3, (cardSet n).Nonempty

@[category test, AMS 52] theorem f_zero_eq : f 0 = 0
@[category test, AMS 52] theorem f_three_eq : f 3 = 3

@[category research solved, AMS 52]
theorem variants.ersz_bounds :
    ∀ n ≥ 3, 2^(n - 2) + 1 ≤ f n ∧ f n ≤ Nat.choose (2 * n - 4) (n - 2) + 1
```

## The comparator questions

Q1. f(n) = 2^{n−2}+1 for all n — OPEN (fortress; n ≥ 6).
Q2. f(3) = 3, f(4) = 5 — classical, completely provable in-round.
Q3. f(5) ≥ 9 (the 8-point witness) — machine-certifiable.
Q4. The ErSz bounds — classical; the lower bound construction + the cup-cap
    upper bound (attributed with proof sketch; the label-injectivity
    shortcut machine-REFUTED by this campaign).
