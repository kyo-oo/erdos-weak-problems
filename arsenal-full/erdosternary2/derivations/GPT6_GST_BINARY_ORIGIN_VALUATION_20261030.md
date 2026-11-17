# Erdős 406 — GST binary-origin / ternary-survivor dual-scale research

**Branch:** `gpt6/problem406-binary-origin-valuation-20261030`  
**Original production target:** `∀ K ≥ 5, K ≠ 7, CommonTwo K`.  
**Comparator unchanged:** no new hGate premise, no custom axiom, no source substitution.

## 1. Why this is a different mathematical route

Earlier routes exploit ternary carry-state exclusion, GST Worldtrace nonlinearity,
3-adic exponent isometry, exact archimedean phase windows, and all-scale physical
coefficient identities. Alone they never use the full *binary terminal order*
of the original literal power source `4^K`.

This route couples three data of the SAME physical integer simultaneously:
1. source multiplicative identity `R = 4^K = 2^(2K)`;
2. all-row GST no-common carry automaton for `R -> 4R`;
3. exact finite ternary source endpoint.

A complete theorem must rule out the joint three-way configuration
for every K>=13, then use directly checked K=5,6,8,...,12, with K=7 excluded.

## 2. New global Lean-verified source theorem

The new module `GSTProblem406BinaryOriginExponentScale.lean` proves
unconditionally for **every natural K >= 13**:

```text
L(K) := (4K-1)/3,
4^K < 3^L(K),
3*L(K) < 4*K,
2^((3*L(K))/2 + 1) divides 4^K,
p >= L(K) -> digit3(4^K,p)=0.
```

The universal proof comes from the exact recurrence over exponent increments
of three, `4^(K+3) = 4^K*4^3` and `L(K+3)=L(K)+4`, with
`4^3 = 64 < 81 = 3^4`; the three bases K=13,14,15 are exact
natural-integer computations. No hGate, surrogate source or completion axiom
is used, and the source is the literal original `4^K`.

**Strict isolated Lean kernel CI PASS:**
https://github.com/kyo-oo/erdosternary2/actions/runs/40970652313

This improves the earlier unconditional physical endpoint
`2(K+1)+1` to `(4K-1)/3` when K>=13.

## 3. Direct remaining mathematical implication (not postulated)

For any integer R>0 define BAD(R) to mean no positive row p with
`digit3(R,p)=digit3(4R,p)=2`. Define `L` an upper ternary cutoff.

A potentially sufficient **new lemma to PROVE** (not an axiom) is:

```text
For every L >= 10 and every positive integer R < 3^L,
if R % 3 = 1 and 2^(floor(3L/2)+1) divides R,
then NOT BAD(R).
```

Together with the already *proved* physical-source theorem this would
produce a genuine original `CommonTwo K` for every K>=13, and
the explicitly checked K=5,6,8,9,10,11,12 close the remaining cases.

However, the proposed lemma is strictly **stronger** than the required
physical-power target, because it quantifies over arbitrary R with the
same binary/ternary magnitude constraints, not just literal powers 4^K.
Failure to prove this stronger lemma is not proof of failure of the
original hGate. NEVER substitute this proposed lemma as an assumption
into `Solution.lean`, `ErdosTernary2.lean`, or a custom axiom.
Try to derive it from GST cross-radix dynamics; if disproved, restrict
to the actual powers 4^K and continue.

## 4. Exact broad falsification test

`scripts/gst_406_binary_origin_valuation_audit.py` exhaustively enumerates
ALL positive R satisfying the three premises within
`10 <= L <= 240`, using

```text
t = floor(3L/2) + 1
R = q*2^t
0 < q*2^t < 3^L
q mod3 = (-1)^t mod3 .
```

This is an exhaustive arithmetic parametrization of the selected class,
not sampled exponents. A 4-state GST carry algorithm checks all rows,
and an independent literal-power digit implementation is exhaustively
cross-checked for all 1<=R<3^8 before the main run.

**Exact tested candidates: 4,812,489.**  
**Proposed-lemma violations: 0 within L=10,...,240.**  
**Strict GitHub Actions script receipt PASS:**
https://github.com/kyo-oo/erdosternary2/actions/runs/40970465209

Independent Wolfram check for L=10,...,30:
15 candidates, zero violations. Independent Wolfram checks on the genuinely
BAD non-power source `R=76490824921120768` confirm:
base-3 length 36, binary valuation 46, no shared positive-position
ternary two in R and 4R. This illustrates that BAD sources DO exist,
just not among those with valuation greater than 3/2 of their ternary cut
in the tested range.

**Finite testing does not establish the quantified lemma for L>240.**

## 5. Exact source of novelty and the open mechanism

Prior global archimedean restriction
`8R <= 7(9^m-1)` is sharp for generic BAD ternary words;
density/spectral bounds cannot exclude even one specific natural exponent,
and arbitrary finite bad ternary prefixes have real perfect-power mimics.

The binary endpoint theorem adds a *different*, physical cross-radix invariant:
high binary valuation alongside the *full ternary terminal word*.
For L=2m, the proposed barrier says no positive number
`R=2*q*8^m < 9^m`, `R==1 (mod3)`, survives all GST pair-collision
rows, once m>=5. The leading factor 2 is required because the binary
valuation threshold is `3m+1`. Its multiplier satisfies
`2q < (9/8)^m`.

A rigorous length-uniform theorem must now link
2-adic divisibility to the complete GST four-state carry recurrence
and exclude a high-valuation BAD source without assuming the desired
common-two witness. One potential route is a genuine *dual-radix
renormalization invariant*, not another fixed-prefix classifier or
density-zero conclusion. The exact first unproved implication is
the global valuation-vs-automaton exclusion for all L, or a weaker
version restricted to R=4^K.

## 6. Verification boundary

- Fully proved: exact **all-K>=13 physical binary/ternary scale gap**
  and strict cutoff, via Lean kernel.
- Reproduced only on finite range: high-valuation automaton exclusion
  for 10<=L<=240.
- **Not proved**: the all-L binary-valuation survivor exclusion.
- **Not proved**: the original universal `gst_four_power_third_wave_gate`.
- Production `Solution.lean` still has the explicit hGate argument.
- The legacy comparator `scripts/comparator.sh` cannot certify
  an unconditional final theorem unless the binder-free theorem type
  and full kernel axiom dependencies are checked separately.

This is a substantive, source-exact new mathematical route and
an audited checkpoint, **not a completed proof of Erdős 406**.

## 7. Certified physical source BAD reduction

The separate module `GSTProblem406BinaryOriginBadSurvivor.lean` proves without
custom axioms that *any real hypothetical exception* `K>=13` to
the original `CommonTwo K` induces a packet
`L=physicalShortCut K, R=4^K` satisfying **all** of:

```text
L>=10, 0<R<3^L, R%3=1,
2^((3*L)/2+1) divides R,
every p>=1 is noncollision in (R,4R).
```

This is a valid source-exact one-way implication, not a proof that no
packet exists and not an assumption. The exact original proof was
Lean kernel-certified in targeted workflow:
https://github.com/kyo-oo/erdosternary2/actions/runs/40971389441 .

A further module `GSTProblem406PhysicalCutGateEquivalence.lean` gives
the exact same-source equivalence for all K>=13:
```text
CommonTwo K iff there exists p where
  1<=p<floor((4K-1)/3)
  and digit3(4^K,p)=digit3(4^(K+1),p)=2.
```
Strict dedicated Lean kernel CI PASS:
https://github.com/kyo-oo/erdosternary2/actions/runs/40972917391 .
This improves the old
physical finite-search horizon from `2(K+1)+1` to `floor((4K-1)/3)`;
it does NOT establish the witness's existence.

## 8. New all-depth weighted GST carry contraction

A distinct, unconditional four-state structural improvement now has
its own Lean module `GSTProblem406DualValuationEntropy.lean`.
The exact original affine carry transition matrix is
```text
M = [[1,1,0,0],
     [1,1,0,1],
     [1,0,1,1],
     [0,1,1,0]]
```
The strictly positive integer weight vector `w=(7,10,10,8)`
satisfies `M*w=(17,25,25,20)`, and
`2*M*w=(34,50,50,40) <= 5*w=(35,50,50,40)` entrywise.
By induction the survivor count from every carry state obeys
```text
7 * 2^n * survivingCount(n,c) <= w_c * 5^n, all n>=0.
```
In particular, at the *true affine physical carry c=1*:
```text
7 * 2^n * survivingCount(n,1) <= 10 * 5^n
7 * 4^m * survivingCount(2m,1) <= 10 * 25^m.
```
This is a strict asymptotic improvement over the old
`survivingCount(2m,1)<=7^m`. It reduces the exponent-residue
population upper exponent to `log_3(5/2) ~ 0.83404`, provided
the existing finite exponent-prefix isometry is used in the
transfer. Wolfram independently verified the matrix inequality.
Targeted strict Lean kernel workflow PASS:
https://github.com/kyo-oo/erdosternary2/actions/runs/40972493936 .
It supplies **no** universal witness by itself: a zero-density
exceptional set may still contain some natural exponents.

## 9. Exact remaining theorem

The precise unresolved inference in this new research route is:

```text
forall L>=10, forall R>0,
  R<3^L and R%3=1 and
  2^((3*L)/2+1) divides R
  implies EXISTS a positive ternary row p such that
    digit3(R,p)=digit3(4R,p)=2.
```

This strong all-integer lemma might turn out to be false or harder
than the original; if so, retain the physical origin `R=4^K`.
The finite experiment tests 10<=L<=240 only, and no theorem of
this all-L scope has been verified.

**Final required outcome remains** the original Lean term
`gst_four_power_third_wave_gate` with no hGate argument or custom
axiom, followed by a binder-free, kernel-checked exact comparator.
This checkpoint does not claim that outcome.

## 10. Exact original small exponent base packet, strict kernel PASS

The final small-K module `GSTProblem406BinaryOriginSmallCases.lean`
proves the literal original `CommonTwo K` for EVERY
`5<=K<=12, K!=7`, by the actual same-row physical witnesses:

```text
K   actual shared-two row p
5           2
6           2
7       EXCLUDED
8           4
9           7
10         10
11         10
12         10
```

These arithmetic witnesses were independently checked with Wolfram.
The strict Lean kernel workflow **PASS**:
https://github.com/kyo-oo/erdosternary2/actions/runs/40973285557 .

Thus **every actual physical small-K base case has been discharged**;
for K>=13 the exact all-depth unproved inference remains the
source-specific exclusion of a high-binary-order, finite-word BAD trace.
This file is an auditable checkpoint, NOT an unconditional solution.
