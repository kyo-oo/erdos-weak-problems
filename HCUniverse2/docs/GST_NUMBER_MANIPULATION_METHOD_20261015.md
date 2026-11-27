# GST Number Manipulation (NM) — exact kernel transformation

**Status:** Candidate mathematical definition of the contributor's proposed
Number Manipulation (NM), pending confirmation of the original NM rules.

The contributor's three-equation proposal mentions NM as a proposed
mechanism for manipulating number expressions while studying geometry.
The photographic record does **not** specify an algebraic signature,
typed domain, allowed moves, conservation rules or equivalence relation
for NM. Thus the identities below are new explicit **candidate**
formalizations, not a claim that the contributor's entire NM framework
was already defined or verified.

## Original corrected Equation (3)

Its scalar indexed kernel, with n>=1, is

\[
K_n(x,y)=\frac{1}{x^n-y^{n+1}}.
\]

An exact pole exists at x=4,y=2,n=1. A positive safe domain is
y>=1 and x>y². The x=y=2 case is a *different* safe branch whose
summands are negative, with sum exactly -1.

## NM exact second-order transformation

For any a≠0 and a≠b:

\[
\frac1{a-b}
=\frac1a+\frac b{a^2}
+\frac{b^2}{a^2(a-b)}.
\tag{NM-2}
\]

This is an algebraic identity with **exact** remainder, not a
truncated heuristic. Insert a=x^n and b=y^{n+1} to get

\[
K_n(x,y)=x^{-n}
+\frac{y^{n+1}}{x^{2n}}
+\frac{y^{2n+2}}{x^{2n}(x^n-y^{n+1})}.
\]

For y>=1 and x>y², the denominator cannot vanish and
all terms are positive. A new dedicated Lean 4 file,
`GSTNumberManipulationExactKernel.lean`, formalizes this
identity for all indices and exact finite partial sums, with
`#print axioms` trust auditing. Its GitHub Actions gate is
`gst-number-manipulation-exact-kernel.yml`, and the exact-kernel
proof **PASSED** Lean (GitHub run 38675768877, source commit
`3a0fdd79ab2ba8fde0c12c8c175a901f8ae73312`). The separately
described infinite dual-index resummation remains a mathematical
derivation not yet machine-formalized.

Wolfram Language exact symbolic algebra evaluated the difference
between both sides of (NM-2) to zero.

## NM dual-index infinite resummation (mathematical derivation)

Assume y>=1 and x>y². For each n>=1,
q_n=y^{n+1}/x^n satisfies 0<=q_n<=y²/x<1.
Geometric expansion therefore gives

\[
K_n(x,y)=\frac1{x^n}\sum_{k=0}^\infty q_n^k
=\sum_{k=0}^\infty
\frac{y^{k(n+1)}}{x^{n(k+1)}}.
\]

Because the summands are nonnegative, the order of the two
infinite sums can be exchanged. For each fixed k, the ratio
r_k=y^k/x^{k+1} is strictly between 0 and 1. Hence

\[
\boxed{
\sum_{n=1}^\infty\frac1{x^n-y^{n+1}}
=\sum_{k=0}^\infty
\frac{y^{2k}}{x^{k+1}-y^k}
}
\quad(y\ge1,\;x>y^2).
\tag{NM-dual}
\]

Both series converge: the original terms are bounded by
x^{-n}/(1-y²/x), and x>1. The displayed right side is therefore
an exact re-indexed series, not a numerical coincidence.

**Wolfram verification** at (x,y)=(5,2):

- original sum: 1.070091446954301971953287296299712...
- dual-index sum: 1.070091446954301971953518189525519...
- the small displayed difference is from numerical NSum
  approximation at different effective precision.

The dual-index identity has a mathematical derivation in this
note but **has not yet been kernel-formalized in Lean**.
Do not cite the numerical check as a universal theorem.

## Why NM alone is not a Hodge proof

An exact real-variable number manipulation remains an identity
of scalar kernels. A genuine Hodge theorem needs:
- a geometry-defined map from algebraic cycles to actual Betti
  cohomology (not an arbitrary algebraic surrogate);
- a fixed geometric period or detector whose evaluation is
  independently identified with the NM expression;
- sufficient genuinely constructed algebraic correspondences
  to generate all needed rational Hodge directions;
- rational descent of any complex period coefficients.

The existing `GSTClassicalHodgeGeometricKrylovMomentDeterminant.lean`
already proves that a single degree functional acting as an
eigenfunctional of a correspondence has a *zero 2x2 Hankel minor*,
so positive degrees or a lone zeta amplitude cannot magically
force a full-rank higher-dimensional geometric orbit.
Its `projectiveDegreeMoment_first_minor_zero_of_degree_eigen`
theorem is a decisive obstruction to that shortcut.

The repository's OpenAI geometry atlas and
`GSTClassicalHodgeOpenAIGeometryNoncircularityAudit.lean`
explicitly distinguish special-variety geometric certificates from
unconditional Hodge, and prove their completeness is equivalent to
supplying genuine algebraic representatives in the first place.
Reusing certificate names does not discharge the geometric source.

## Exact next noncircular test

Build a genuine canonical proper correspondence on a concrete
source-target projective pair, with a Betti cup/Gysin formula and
a fixed nonzero rational period. Test NM against that measured
period and show the associated *multiple* geometric readout
matrix has nonzero rank; a single scalar NM value is insufficient
for unrestricted rank. Each step must use actual geometry, not
an assumed abstract matrix unit.

The user's personal name is intentionally omitted.
