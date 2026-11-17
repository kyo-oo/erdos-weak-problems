# GST Hodge program: universal hyperplane source and primitive obstruction

Date: 2026-10-15. Attribution anonymous. No public internet search.
Target: for every smooth projective complex variety X, every rational
Hodge (p,p) class in H^(2p)(X,Q) is represented by a rational
algebraic cycle, without assuming that cycle's preimage.

## A. The universal source EXISTENCE question has a standard answer

For any smooth projective X of dimension d, take its projective
embedding and ample hyperplane class h=cl(H) in H²(X,Q). Its top
intersection integral is deg(X)>0, hence h^d is nonzero.

For every 0<=p<=d, h^p is the genuine class of an intersection of
p algebraic hyperplanes. If h^p=0 then h^d=h^p cup h^(d-p)=0,
contradiction. Therefore for every permissible codimension of
EVERY smooth projective X, h^p supplies an actually algebraic,
nonzero rational (p,p) class. d ranges over ALL finite dimensions,
not an imposed global dimension limit.

This resolves existence of one genuine nonzero native source at
every weight without native coefficient mass, fixed CM sources,
an arbitrary zeta coefficient, or an assumed nonzero seed.

The repository already contains genuine scheme hyperplanes in
GSTClassicalHodgeProjectiveHyperplaneSection.lean and a
degree-trace semantic structure in
GSTClassicalHodgeProjectiveDegreeTrace.lean. The new
GSTUniversalHyperplaneAndCMObstruction.lean uses Lean to verify
the algebraic inference from a positive top-degree readout to
nonzero h^p at EVERY p<=d. Its dedicated CI
38687088672 PASSED. That Lean kernel does not yet derive
the full cup-product and integration pairing from Mathlib
scheme-theoretic geometry; classical projective geometry
provides that external input.

## B. A nonzero seed is NOT a complete Hodge generating family

Take X=P¹×P¹ with the two rational algebraic divisor rulings a,b.
They are independent. The ample class h=a+b is algebraic but
the primitive nonzero class delta=a-b satisfies
h cup delta=a²-b²=0 because a²=b²=0.

Thus a valid universal Hodge proof must produce independently
realized PRIMITIVE classes beyond the hyperplane subalgebra.
A numerical nonzero CM/NM trace does not by itself establish
the necessary new native directions. For this example the
two rulings already provide them; for general X this is
the outstanding problem.

## C. Universal finite-degree coverage by a fixed Gaussian-CM E^g is false

The green GSTCMFiniteGeometricDegreeDescent.lean gives a
correct descent: a real finite dominant f:A->X of degree m>0
with Hodge known on A would give Hodge on X through
m^(-1) f_* f^*.

However, for a smooth genus-two curve C, no nonconstant
elliptic E->C map exists. Riemann-Hurwitz would require
0=m*(2g(C)-2)+R=2m+R>0.

For a product E^g, restricting any map E^g->C to any
single elliptic coordinate (others fixed) is constant by
the same argument. Changing coordinates one at a time
makes the whole morphism constant. Therefore the
universal fixed-CM-source dominant-transfer premise is
false. This is a counterexample to THAT PROPOSED ROUTE,
not to the Hodge conjecture itself.

The new Lean file checks the exact RH integer contradiction.
It does NOT itself formalize scheme-theoretic Riemann-Hurwitz.
Also generic finite projection X->P^d has the reverse
direction: it cannot transfer known Hodge algebraicity
from P^d to unknown primitive classes on X.

## D. Tensoring an arbitrary X with CM E does not solve it

Take X×E with T=id_X×[i] acting on the E factor.
For a rational class alpha from X, its pullback is
pi_X^*(alpha)=alpha tensor 1 in Kunneth cohomology.
Since [i]^*(1)=1, we have

  T^*(pi_X^*(alpha)) = pi_X^*(alpha).

Thus this natural factor-selective CM operator creates
no independent Hodge direction from classes pulled back
from X. To force new primitive directions, one must
construct *mixed* algebraic correspondences with
nontrivial action on primitive cohomology. These are not
supplied merely by choosing a Gaussian-integer NM
denominator or an abstract CM polynomial.

## E. Exact status and next genuine mathematical target

Completed: universal existence of a nonzero algebraic
Hodge seed h^p in every permissible codimension.
Verified Lean structural theorem: CI 38687088672 GREEN.
Excluded: a universally generically finite Gaussian-CM
abelian source covering ALL projective varieties.

Still OPEN: independent construction of actual algebraic
representatives for arbitrary PRIMITIVE rational Hodge
classes on general smooth projective X. The previous
conditional correspondence cyclicity and period
comparison assumptions encode rather than prove this
remaining existence. The total Hodge conjecture
has not been proved.

The correct research continuation is to construct mixed
CM/non-CM cup-Gysin correspondences hitting specified
primitive classes on test varieties (generic surfaces
and hypersurfaces), then test whether their geometric
identities generalize without assuming surjectivity.
Do not claim a Lean import/green build of conditional
statements proves that existence.
