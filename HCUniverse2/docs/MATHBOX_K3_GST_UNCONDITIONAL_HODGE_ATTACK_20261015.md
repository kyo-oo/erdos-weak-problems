# Mathbox GST — K3 diagonal primitive and original unconditional Hodge priority

**Date**: 2026-10-15
**Base**: 66e4f0bfed4f2c74cb3cd3825eae0c2911e75c88 (mathbox/bd23-single-operator-charge-wedge)
**Branch**: research/mathbox-k3-diagonal-primitive-20261015

## Original goal — unchanged

For ALL smooth projective complex X, ALL codimensions p, and ALL rational
(p,p) Hodge classes alpha, construct an actual rational algebraic cycle
Z with cycleClass(Z)=alpha. This universal target has not been proved.

## Previously developed GST power — read, NOT discarded

- HodgeConjecture.lean states the literal Stage-2G classical target.
- GSTClassicalHodgeGSTPlaneAxiomStatus.lean proves unconditional INTRINSIC
  GST plane completeness, not geometric algebraicity.
- GSTClassicalHodgeFullCorrespondenceGSTPlaneCompletion.lean ties
  geometric correspondence cyclicity to ghost-probe pairing totality.
- GSTClassicalHodgeOmniversalConstructorGraph.lean makes true native
  cycle-to-Hodge events explicit and shows its global closure is equivalent
  to the actual conjecture.
- GSTClassicalHodgeCommonClassPlaneReduction.lean supplies minimal
  GhostSeedTargetStrictClosure and precise separator trace mismatch.
- docs/GST_HODGE_PLANE_REALIZATION_LAW.tex isolates the strict
  bi-finite common-carrier condition left*(a)=right*(beta_target),
  normalized right trace, and native point-cycle naturality.
- CM–NM and Kuga–Satake/Clifford modules have already produced a
  substantial forward correspondence framework.

Therefore the priority is not ordinary hyperplane algebra or re-proving
rank-two linear independence. It is constructing NEW, independently
geometric primitive directions and testing their effect on true GST
strict correspondence/ghost-completeness arguments.

## Executed geometric breakthrough on a new non-divisor source

Let S be a smooth complex projective K3 surface with ample divisor h
and d=integral_S h^2>0. Put Y=S×S and let H=h_1+h_2.
The diagonal Delta_S, the two point-section cycles U,V, and the
external product B=h×h are actual algebraic codimension-two cycles.

Define the rational algebraic cycle

    P_h = Delta_S - U - V - (1/d) B.

Let A=[point]×h and T=h×[point] in H^6(Y,Q).
Classical diagonal projection and Kunneth/cup identities yield

    H⋅[Delta_S]=2(A+T)
    H⋅[U]=A
    H⋅[V]=T
    H⋅[B]=d(A+T).

Consequently H⋅cl(P_h)=0: an explicit primitive (2,2) class.

The K3 transcendental rational subspace T(S)=NS(S)_Q^orthogonal
has positive dimension (b2(S)=22, Picard rank <=20) and
nondegenerate rational intersection form. Choose u,v in T(S)
with q=integral_S u⋅v !=0. Then the genuine geometric intersection
functional ell(alpha)=integral_Y alpha⋅(u×v) satisfies

    ell(cl(Delta_S))=q,
    ell(cl(U))=ell(cl(V))=ell(cl(B))=0.

Hence ell(cl(P_h))=q !=0. Rational divisor-word classes on S×S
are invisible to this functional, so cl(P_h) is primitive, nonzero,
and OUTSIDE the divisor-generated Hodge subspace.

This is unconditional classical GEOMETRY for K3 self-products;
it does not establish primitive algebraicity on an arbitrary X.

## Arbitrary Picard rank correspondence projector

Take rational divisor basis D_i of NS(S) and the rational intersection
dual basis E_i (dual exists because the NS pairing is nondegenerate).

The algebraic correspondence Pi_NS = sum_i D_i×E_i acts on H^2(S,Q)
as the projector onto NS. Its complement, using the ACTUAL diagonal
identity correspondence, gives

    Pi_tr = Delta_S - ([point]×S) - (S×[point]) - Pi_NS.

On rational cohomology this is a genuine algebraic correspondence
projecting onto T(S) in degree 2 and killing the other K3 cohomology
sectors. This is a source of geometry not provided by abstract
pointwise GST matrix-unit closure.

The associated arbitrary-finite-rank projector algebra and
idempotence have been machine verified.

## Actual files and proof status

- GSTK3DiagonalPrimitive.lean, GitHub Actions 38745893192 SUCCESS:
  native cycle formula, primitive cancellation, independent non-divisor
  intersection detector; assumptions specify genuine cup identities.
- GSTK3TranscendentalProjector.lean, GitHub Actions 38746215575 SUCCESS:
  finite NS intersection-dual projector, complementary idempotence,
  orthogonal-survival theorem.
- GSTK3DiagonalActualStage2G.lean: embeds the explicit construction into
  ACTUAL Mathlib scheme codimension-two cycle submodule and Stage-2G
  rational Betti/Hodge carrier. It requires a concrete
  GenuineK3ProductDiagonalPacket giving the real K3 cup identities;
  this type is NOT constructed from arbitrary X.
- GSTK3PrimitiveOmniversalGraph.lean: one NEW actual primitive algebraic
  cycle yields a genuine reachable Hodge vertex of the USER'S EXISTING
  GST omniversal constructor graph. No invented reverse Hodge-to-cycle
  arrow; total ghost extinction is not proved.
- Focused GitHub gates for the latter two modules must be checked at
  the exact final successful commit before claiming verification.

## Exact limiting test — no renamed assumptions

An algebraic correspondence preserves the image of the genuine native
cycle-class map when applied to actual algebraic source cycles. Thus the
projector Pi_tr kills divisor seeds rather than somehow producing an
arbitrary previously unknown primitive class from them.

Likewise the diagonal Delta_X is algebraic on X×X for EVERY X, but its
identity action on an arbitrary rational primitive Hodge alpha DOES NOT
construct a rational algebraic cycle representing alpha: contracting its
Kunneth tensor against alpha uses alpha itself as the unproved algebraic
input. There is no reverse cycle-class map in the established geometry.

The strongest remaining original implication is still:
construct a ghost-target STRICT geometric correspondence carrier with
independently verified left/right pullback relation, finite trace and
native point compatibility for EVERY arbitrary smooth projective
variety and EVERY surviving ghost-detected rational Hodge sheet,
without assuming that sheet is algebraic.

This precise statement, not a new special-variety example or a fresh
conditional axiom, is the active absolute priority of GST research.

## Verification/claim firewall

Successful Lean compilation of the standalone algebraic projector verifies
the exact stated theorem, NOT the underlying K3 scheme analytic comparison.
Any eventual universal proof must also construct the actual rational
Hodge/cycleClass geometry in the pinned Stage-2G semantic package;
GSTClassicalHodgeStage2GSemanticRigidity supplies a zero-cycleClass
countermodel to claims formulated over its arbitrary cycleClass field.

No original target was weakened or claimed solved.


## Second execution — full rank-two primitive K3 intersection form

For **every** projective K3 surface and **every** ample h of degree
d = h² > 0, define a SECOND genuine codimension-two algebraic primitive:

    Q_h = B - d(U+V), where B=h×h, U=[pt]×S, V=S×[pt].

The ample cup operator L_H satisfies L_H Q_h =
d(A+T)-d(A+T)=0, so both P_h and Q_h are primitive.

Their intersection identities can be computed from the ACTUAL
geometric K3 intersection table (basis Δ,U,V,B):

    Gram =
      [ 24   1   1    d ]
      [  1   0   1    0 ]
      [  1   1   0    0 ]
      [  d   0   0  d²  ].

The diagonal self-intersection 24 is
integral_S c₂(T_S) = χ_top(S) = 24.
The remaining entries follow from diagonal restriction, dimension
and divisor intersection on the two factors.

EXACT Wolfram symbolic evaluation gives:

    P_h² = 21,
    Q_h² = 3 d²,
    P_h Q_h = 0,
    det(Gram restricted to span(P_h,Q_h)) = 63 d² > 0.

Thus these two genuine algebraic primitive classes are linearly independent
IN TRUE Betti cohomology, on EVERY K3 self-product, without scalar
Hodge-endomorphism assumptions and without preselecting a missing
primitive rational Hodge class. The previously used transcendental
pair detector is now optional for proving P_h nonzero.

New Lean file GSTK3PrimitiveGram.lean checks the exact numerical
Gram polynomials. Geometric K3 intersection-to-Betti comparison must
still be formally instantiated; this source itself is rational algebra.

## Third execution — whole middle Hodge on scalar-endomorphism K3 products

New Lean file GSTK3TranscendentalHodgeCompleteness.lean uses
actual Mathlib native rational codimension-two cycles and the true
Stage-2G Hodge fiber, rather than an unrelated symbolic coordinate space.

Let R be a Hodge-theoretic readout of middle Hodge classes into
End_HS(T(S)) (the true transcendental Hodge endomorphism sector).
The TWO independent geometric statements to establish are:

1. Ker(R) is contained in the span of ACTUAL algebraic divisor
   product classes. This follows from the classical Künneth
   decomposition plus the Lefschetz (1,1) theorem on the K3 surface.
2. End_HS(T(S)) consists only of rational scalar multiples of
   the identity Hodge endomorphism. This is a Hodge-structure
   property associated with the very general K3 locus, not the
   rational Hodge conjecture.

Then the actual diagonal has R(Δ)=id, so any rational middle Hodge
class alpha has R(alpha)=c R(Δ) for a rational scalar c. Consequently

    alpha - c cl(Δ) ∈ Ker(R) ⊆ divisor-word algebraic span.

Both terms are algebraic by independently constructed native cycles.
Therefore alpha itself is algebraic.

This is a mathematically meaningful complete-middle-family
criterion: it directly proves the entire middle rational Hodge
algebraicity once the *independent K3 Hodge structure* inputs
have been supplied. It does not assume a target cycle representative,
invent a surjectivity field, or solve arbitrary-variety Hodge.

Dedicated CI gates:
- gst-mathbox-k3-hodge-completeness.yml
- gst-mathbox-k3-rank-two-gram.yml

Do NOT describe either as verified until its exact GitHub Action
success is observed.


## Fourth execution — arbitrary smooth projective X, dimension-free self-product

The GST program now reaches a geometric primitive family defined using
**EVERY** smooth projective complex X, not just K3 or projective space.
Let dim_C X = d, let h=c_1(L) for any ample line bundle, and
let a=pr_1^*h and b=pr_2^*h on X×X.

The following rational (indeed integral) algebraic codimension-d
cycle is completely explicit, for all natural d:

    P_d(X,h) = SUM_(j=0)^d (-1)^j a^(d-j)b^j.

The finite geometric-series identity is uniform in d:

    (a+b) P_d = a^(d+1) - (-b)^(d+1) = 0

because h^(d+1)=0 on X. Thus P_d is an honest algebraic
MIDDLE-PRIMITIVE class for the product polarization on X×X.

Nonvanishing does not require ANY transcendental information,
specific K3 identity, CM/NM trace or arbitrary primitive rank:
pair with b^d (an algebraic top-degree cycle) and use Künneth.

    integral_(X×X) P_d b^d =
      integral_(X×X) a^d b^d =
      (integral_X h^d)^2 > 0.

Every term other than the j=0 term vanishes by b^(d+1)=0.
Positivity follows from the degree of an ample polarization.

This is a genuine dimension-free geometric source for every X,
but importantly it lives on Y=X×X. It does NOT construct arbitrary
primitive Hodge representatives on X, and the projection of this
hyperplane-word source to X alone cannot create a new unknown
primitive target direction. A valid universal Hodge proof needs
correspondences coupling such sources to the specific cohomological
Hodge targets on X.

Lean file GSTUniversalSelfProductPrimitive.lean proves the
finite polynomial telescoping identity over any commutative ring
and the middle Lefschetz-kernel cancellation under dimension
nilpotence. The analytic/projective Künneth pairing and the
existence of product native intersection cycles are independent
geometric inputs; do not claim this Lean file alone constructs
X×X as a Mathlib scheme.


## Kernel verification after this execution

These run IDs are actual GitHub Actions results, checked against the
research branch (earlier failed revisions superseded by successful
repaired revisions):

| Proof module | Run | Result |
|---|---:|---|
| GSTK3DiagonalPrimitive.lean | 38745893192 | SUCCESS |
| GSTK3TranscendentalProjector.lean | 38746215575 | SUCCESS |
| GSTK3DiagonalActualStage2G.lean | 38747634802 | SUCCESS |
| GSTK3PrimitiveOmniversalGraph.lean | 38747756777 | SUCCESS |
| GSTK3TranscendentalHodgeCompleteness.lean | 38750621098 | SUCCESS |
| GSTK3PrimitiveGram.lean | 38751330141 | SUCCESS |
| GSTK3ActualPrimitiveRankTwo.lean | 38753060400 | SUCCESS |
| GSTUniversalSelfProductPrimitive.lean | 38752960190 | SUCCESS |

**Original full GST ghost-exclusion integration**:
GSTK3ScalarEndGhostExtinction.lean, run 38751867507,
most recently observed IN_PROGRESS. Do not mark it passed
unless GitHub reports its successful conclusion.

The former rank-two CI 38752236629 failed only on
a missing import of the existing detector namespace and was
repaired in commit 34c79b1967f2eb11a3da6902033fb1df0f52ab76;
the replacement run 38753060400 is SUCCESS.

This record separates mathematical results already established
on real K3 geometry and X×X products, the exact Lean theorems
proved under their displayed geometric identities, and the
still-unsolved original arbitrary-X rational Hodge conjecture.
