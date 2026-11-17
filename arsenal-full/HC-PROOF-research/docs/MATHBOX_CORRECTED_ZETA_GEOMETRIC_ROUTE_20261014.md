# Mathbox — corrected indexed GST–zeta Equation (3)

**Date:** 2026-10-14
**Base:** branch `mathbox/bd23-single-operator-charge-wedge`, as of
`3a3ff46adc5334ac7db587cc12b422d6bb870892`.
**Source:** user-provided corrected equation image.
**Public target:** `HodgeConjecture.ClassicalHodgeTarget`.
**Formal file:** `GSTMathboxCorrectedZetaGeometry.lean`.
**Verification:** see the dedicated workflow
`.github/workflows/gst-mathbox-corrected-zeta-geometry.yml`;
do not label uncompleted jobs green.

## Original corrected expression

```text
L(t(s)) s = zeta(s) * Sum_{n -> R} 1 / (x^n - y^(n+1)) ⊕ (H × Q)
```

This supersedes the previous photograph's constant denominator
`x^1-y^2`. The new index dependence is a meaningful correction.
We **do not** assume what the symbol `n -> R` means: it could describe
a discrete upper-cutoff limit, a summation domain, or something else.
The most conservative ordinary-series interpretation uses integer
`n >= 1`, with the separate cutoff `N` tending to infinity.
Lean uses `m=n-1` so the denominator is `x^(m+1)-y^(m+2)`.

The expression remains untyped as a complete equality until
`L`, `t`, `s`, `R`, `x`, `y`, and the precise operation
`⊕ (H × Q)` are defined. In particular, direct sum and Cartesian
product are *different* constructions, and the rational Hodge
fiber cannot automatically be scaled by arbitrary complex
`zeta(s)` values.

## Wolfram exact tests

For the ordinary series over positive integers:

```text
D_n(x,y) = x^n - y^(n+1)
S(x,y) = Sum_{n=1}^infinity 1/D_n(x,y)
```

1. **Real pole:** `D_1(4,2) = 4 - 4 = 0`.
   Changing the exponent does not rule out singular terms.
2. **Diagonal exact sum:** if `x=y=q>1` (real),
   `D_n(q,q)=(1-q)q^n` and
   `S(q,q)=-1/(q-1)^2`.
   In particular `S(2,2)=-1` for n>=1 and `-2`
   if n begins at zero.
3. **Useful off-diagonal case:** for `x=3,y=2` the
   first denominators for n=1,2,3 are `-1,1,11`.
   Starting the sum at n=2 avoids the initial negative term
   and gives `1.119330698811034997...`, a convergent
   positive tail.
4. **No unconditional positivity:** `x=3,y=2,n=1`
   contributes `-1`, so the series is not termwise positive
   without restrictions.
5. **Zeta factor:** if `s=2`, the diagonal scalar
   `zeta(2)*S(2,2) = -pi^2/6`; this is **not a
   rational number**. A rational cycle class does not arise
   from multiplying an existing rational vector by this
   scalar unless a separately defined rational descent is
   proved. Zeta values may vanish in other parameter regimes.

For real `x>y^2>=1` with `y>=1`, each n>=1
denominator is positive and, because `y/x<1`,
there is a uniform `c=1-y^2/x>0` such that
```text
0 < 1/D_n(x,y) <= x^(-n)/c.
```
This follows by factoring
`D_n=x^n*(1-y*(y/x)^n)` and observing
`y*(y/x)^n <= y^2/x` for n>=1.
Therefore the positive tail is absolutely summable by
comparison with a geometric series, since `x>1`.
This is an **analytical derivation** recorded separately
from the checked Lean finite-sum results.

## Mathbox proof route implemented

The dedicated Lean source proves:

- the exact indexed denominator and an explicit pole;
- at `x=y=2`, all corrected terms are strictly negative;
- all **nonempty finite** partial sums are strictly negative;
- multiplying by a nonzero real zeta scalar preserves
  nonvanishing at finite cutoff;
- if a genuinely constructed rational native cycle has its
  rational Hodge-coordinate readout *equal* to that
  nonzero real scalar expression, the cycle class is outside
  the span of all old native cycles. This works for an
  arbitrary old index type, not just two directions.

The last theorem has an explicit geometry comparison equality.
It is neither an axiom nor a clandestine assumption that every
Hodge class has an algebraic representative. It is a checkable
premise to be obtained from the user's GST correspondence
geometry.

## Mathematical consequence and remaining exact input

The correction removes the earlier constant-summand divergence
obstruction and supplies meaningful convergent parameter
regimes. The next load-bearing implication for the *actual*
Hodge conjecture is NOT merely analytic convergence:

```text
A concretely constructed finite closed algebraic correspondence
→ a canonical full Betti cohomology operator (not an arbitrary
extension from the algebraic image)
→ a proved zeta/CM numerical coordinate formula for the
  image of an actual native algebraic cycle
→ enough independently detected genuine rational cycle classes
  to span every rational (p,p) Hodge fiber.
```

The current abstract `HodgeBigradedBettiData` record admits a
zero-cycle-class countermodel, verified in the repository.
Thus even a complete kernel-checked theorem conditional on
nonzero geometric readouts, or a complete analytic summation
theorem, does not establish all four arrows above for
all smooth projective varieties.

**Target status:** original full Hodge conjecture unproved.
**Corrected equation status:** numerical denominator fixed;
finite series/rank implication formalized; full semantics and
universal geometric cycle generation remain open.

## Additional structural result: Lambert-series re-expansion

Under the explicit **real** hypotheses `y >= 1` and `x > y^2`,
the infinite indexed series has a positive, convergent Lambert-type
re-expansion.

Let `r_n=y*(y/x)^n`. Then `0<=r_n <= y^2/x < 1`
for all `n>=1`, so the geometric expansion is valid:

```text
1/(x^n-y^(n+1))
  = x^(-n)/(1-r_n)
  = sum_{k=0}^infinity [ y^k*(y^k/x^(k+1))^n ].
```

All terms are nonnegative, allowing exchange of the two sums
under these hypotheses. Summing over n>=1 first gives

```text
sum_{n=1}^infinity 1/(x^n-y^(n+1))
  = sum_{k=0}^infinity y^(2*k)/(x^(k+1)-y^k).
```

Moreover the original series obeys the explicit comparison bound

```text
0 < S(x,y) <= 1/((x-1)*(1-y^2/x)).
```

This is an actual analytical improvement: the corrected formula
has a controlled absolutely convergent region and an alternative
series representation. It is **not** a cohomological cycle theorem.

Wolfram cross-checked at `x=5,y=2`:

```text
original  = 1.070091446954301971953287296299712...
repacked = 1.070091446954301971953287296299499...
upper bound = 5/4 = 1.25.
```

The tiny difference above is numerical truncation/precision,
not a mathematical discrepancy. The symbolic derivation is
independent of this numerical example.

For the diagonal `x=y=q>1`, the original series has the
exact rational closed form `S(q,q)=-1/(q-1)^2`.
At the analytic continuation value `zeta(0)=-1/2`,
`zeta(0) S(2,2)=1/2` is rational. At `zeta(2)=pi^2/6`,
the corresponding scalar is not rational; rationality must
be proved or separately descended before using it as a
scalar on rational native cycles.

**A precision point:** The Lean file currently checks the
index-dependent finite terms and their geometric detection
mechanism. The infinite-sum comparison and Lambert exchange
are analytically derived and Wolfram cross-checked here;
they are not yet recorded as standalone Lean kernel theorems.

## Lean proof completion checkpoint: infinite sum, safe domain, genuine Hodge route

The corrected Equation (3) research now has **FOUR independently compiled**
Lean modules, not just symbolic calculations:

| Lean file | Core result | GitHub Actions passed |
|---|---|---|
| `GSTMathboxCorrectedZetaGeometry.lean` | Corrected x^n-y^(n+1) denominator, explicit pole, finite scalar detector and arbitrary-rank native span exclusion | `38603472321` |
| `GSTMathboxCorrectedZetaInfinite.lean` | TRUE infinite summability at (x,y)=(2,2), exact `tsum=-1`, nonzero scalar amplification | `38604173599` |
| `GSTMathboxCorrectedZetaSafeDomain.lean` | All denominators positive for **every n** if y>=1 and x>y^2; all positive-cutoff sums nonzero | `38605217121` |
| `GSTMathboxCorrectedZetaActualHodge.lean` | Any nonzero native cycle is a Hodge seed under actual correspondence irreducibility; corrected infinite series proves seed nonzero from genuine geometric readout; full all-weights conditional Hodge theorem | `38605438617` |

The independent verification jobs passed with the source's `#print
axioms` audits and no `sorryAx`. Do NOT mistake these individual
successes for the entire public `HodgeConjecture.lean` module.
The four files, their library registration, and a new conditional
`classicalHodgeTarget_of_corrected_zeta_actual_geometry` theorem
were atomically integrated into the **unchanged** public Hodge
target at commit `c69ed255b8ad5841d26ad6b2f86129b197fbdb7d`.
The full-root CI is `38605997725` and needs independent verification.

### Coefficient/rationality consistency check

For the EXACT (2,2) case, `sum=-1`. Hence any proposed
**rational** Hodge-coordinate readout satisfying
`real(read(cycleClass(Z))) = zeta(s) * sum`
implies `zeta(s) = -real(read(cycleClass(Z)))`, which is itself
rational. Therefore the condition cannot hold with
`s=2` and `zeta(2)=pi^2/6` in the rational coefficient model.
It *could* hold at a rational special value, for example
`zeta(0)=-1/2`, where the scalar equals `+1/2`.
This is a real mathematical type restriction, not a formatting
issue. If the intended object uses complex periods, a genuine
period comparison and rational descent map must be built rather
than inserting an arbitrary transcendental scalar into a
Q-module.

### What is still NOT an unconditional Hodge proof

The numerical equation and its convergence are now established
in genuine parameter families. The conditional native Hodge
landing depends on:

1. A **genuinely constructed** algebraic codimension-p cycle
   with a proved canonical cohomological coordinate identified
   with the corrected infinite zeta expression.
2. The geometric irreducibility of the **actual realized
   Hodge-compatible finite closed correspondence algebra**
   on each nonzero rational Hodge fiber, or a separate
   construction of a full native algebraic Hodge basis.
3. The full authentic cycle-class/Hodge semantics, rather than
   unconstrained fields that admit the zero-class countermodel.

None of those universal existence inputs is proved merely by
the analytic indexed series. The classical Hodge conjecture is
not proved by this checkpoint. These hypotheses remain exact
research targets, not artificial new axioms.
