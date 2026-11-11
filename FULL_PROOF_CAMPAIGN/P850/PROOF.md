# Erdős #850 — The Radical Triple Coincidence (Erdős–Woods, length 3)

**Agent W2-P850 · FULL-PROOF CAMPAIGN · status: IN PROGRESS (updated live)**

## §0. VERBATIM TARGET (corpus-erdos/data/problems.yaml #850, corpus_statements_full.json)

> **"Can there exist two distinct integers $x$ and $y$ such that $x,y$ have the
> same prime factors, $x+1,y+1$ have the same prime factors, and $x+2,y+2$
> also have the same prime factors?"**

Context (corpus `add`): "This is sometimes known as the Erdős–Woods conjecture.
For just $x,y$ and $x+1,y+1$ one can take $x=2(2^r-1)$ and $y=x(x+2)$.
Erdős also asked whether there are any other examples. Makowski [Ma68]
observed that $x=75$ and $y=1215$ is another example … No other examples are
known. This sequence is listed as A343101 at the OEIS."

SUCCESS CONTRACT: the answer is YES (exhibit a witness, i.e. distinct integers
x, y with coincident prime-factor sets on the full three-term window) or NO
(no such pair exists — an impossibility theorem). Weaker substitutes
(restricted families, "almost-all") do NOT count.

Prior campaign state (THE_LIST/W-2 briefing): no witness < 2·10⁴ (census);
engine assigned: radical/vff parity machinery.

## §1. NOTATION

- `supp(n)` = set of prime divisors of n (n ≥ 1); `rad(n)` = ∏_{p∈supp(n)} p.
- Window radical: **R(n) := rad(n(n+1)(n+2))**.
- Witness: x ≠ y, x,y ≥ 1 (justified in Lemma 0), x < y, D := y − x.

## §2. CORE REDUCTION (derived this session — the engine)

**Lemma 0 (positivity).** Any witness with a window member in {−1, 0, +1}
collapses (case analysis); both-negative witnesses are positive witnesses of
the reversed windows. WLOG 1 ≤ x < y.

**Theorem A (Window Divisibility Equivalence).** For 1 ≤ x < y, D = y − x:
  supp(x+i) = supp(y+i) for i = 0,1,2
  ⟺ **R(x) | D and R(y) | D**.
(Generalizes verbatim to windows of any length k, with
R_k(n) = rad(∏_{i<k}(n+i)).)

**Theorem B (Top-window collapse).** In any witness,
  **R(y) ≤ y − 1**, i.e. rad(y(y+1)(y+2)) < y.
Corollaries: 6 | D; y ≥ 7; each of y, y+1, y+2 is non-squarefree;
D ∈ {m·R(y)}; x ≡ y (mod R(y)) with x = y − m·R(y) ≥ 1.

**Theorem C (quality-2 abc embedding).** In any witness, the coprime triple
  a = (y+1)² − 1, b = 1, c = (y+1)²  (a + b = c)
satisfies rad(abc) = R(y) < √c, i.e. **abc-quality q > 2**. No abc triple of
quality > 2 (any form) has ever been found (world record q ≈ 1.63); abc
conjecture permits only finitely many.

**Theorem D (known k=2 families die at k=3).** Erdős family
x = 2(2^r−1), y = x(x+2): supp matches at i=0,1 always, never at i=2
(proof: rad(x+2) = 2 forces y+2 = 2^t, but y+2 = 2·(odd > 1)). Makowski
(75, 1215): dies at i = 2 (77 = 7·11 vs 1217 prime).

## §3. CENSUS (in progress)

Certified exhaustive search via Theorem A+B: scan all y ≤ N with R(y) < y
(the only possible tops), then x = y − m·R(y) with R(x) | m·R(y).
Target N = 10⁹ (segmented radical sieve). Dual method: direct (x, D)-multiple
scan + brute-force pairs at small N.

## §4. WALL (named, if no kill)

**Wall-W (the ε-gap / quality-2 barrier):** a witness requires
rad(y(y+1)(y+2)) < y. Unconditionally only rad ≳ P_max(y(y+1)(y+2)) ≳
polylog(y) is provable; the abc conjecture itself only forces
R(y) ≳ y^{1−ε} (ε > 0) — a y^{ε} short of the needed bound, equivalent to an
abc hit of quality > 2 in the restricted family (n²−1, 1, n²).

## §5. FULL PROOFS — being written (§A–§D above; see bottom for final text)
