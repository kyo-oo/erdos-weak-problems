# GST primitive Hodge research: exact target, universal operations, and verified limits

**15 October 2026.** Contributor attribution intentionally anonymous.

## Nonnegotiable target

For every smooth projective complex variety X, every codimension p, and every rational Hodge class α in H^(2p)(X,Q) intersect H^(p,p)(X), construct a genuine algebraic codimension-p rational cycle Z with cl(Z)=α. More precisely the unresolved part is algebraicity of all primitive rational Hodge classes at middle degrees. This is the unchanged classical Hodge conjecture, not the existence of one primitive example.

A successful Lean proof must establish the geometry behind the cycle-class map and cannot insert an arbitrary Stage2G class-preimage, Hodge basis packet, geometric cyclicity axiom, or period equality equivalent to α being algebraic.

## Route 1: explicit all-variety primitive divisor constructor

File: \`GSTUniversalPrimitiveDivisorConstruction.lean\`.
CI: \`gst-universal-primitive-divisor.yml\`, initial 38697994233 failed because \`GSTUniversalLefschetzCurveCycles\` was not registered as a Lake root, not because its mathematics was refuted. Final corrected run **38698778620 — SUCCESS**. Earlier 38697994233 failed from a missing Lake root; the next attempt exposed and repaired one rational division-equality orientation.

For X smooth projective of dimension d, fix ample h, and define the actual rational top-intersection functional on H¹(X,Q) (i.e. the Hodge (1,1) part of degree-two Betti cohomology):

\[
\deg_h(\beta)=\int_X \beta\smile h^{d-1},\quad \deg_h(h)=\int_X h^d>0.
\]

Given an actual divisor D and its Hodge class [D], construct the **native algebraic primitive divisor**
\[
D_{\mathrm{prim}}=D-
\frac{\deg_h([D])}{\deg_h(h)}\,H.
\]
All coefficients are rational; the output is an ACTUAL rational algebraic divisor, and \(\deg_h([D_{\mathrm{prim}}])=0\). If β is an arbitrary primitive rational Hodge (1,1) class, the established Lefschetz (1,1) theorem produces a divisor D with [D]=β, and the normalization preserves that target class **exactly**. This proves a genuine universal constructive algebraicity statement for *all primitive rational divisor Hodge classes*, subject to the standard Lefschetz (1,1) theorem and the natural Betti intersection pairing. It is not new to mathematics but is new explicit GST formalization.

The Lean input \`DivisorsRepresentHodge11\` denotes the independently established classical Lefschetz (1,1) theorem; HC-PROOF does not itself supply a formal proof of that analytic-geometric theorem. The new file must not be called fully formalized scheme geometry merely because its conditional algebra compiles.

## Route 2: algebraic fourfold Lefschetz correction and primitive native-cycle extraction

File: \`GSTUniversalFourfoldPrimitiveExtraction.lean\`.
CI: \`gst-universal-fourfold-primitive-extraction.yml\`, final corrected run **38698778667 — SUCCESS**. Its full dependency closure and explicit cycle construction compiled under GitHub Lean.

For X any smooth projective complex fourfold, let L denote cup with the ample h. Hard Lefschetz gives L²:H²(X,Q)→H⁶(X,Q) an isomorphism of rational Hodge structures. Given *any* rational (2,2) class α, define
\[
\beta=(L^2)^{-1}(L\alpha)\in H^2(X,Q)\cap H^{1,1}(X).
\]
By the known (1,1) theorem, choose a genuine divisor D with cl(D)=β. Then the actual native algebraic correction \(h\cdot D\) has
\[
L(\mathrm{cl}(hD)) = L^2\beta=L\alpha.
\]
Therefore
\[
\alpha_{\mathrm{prim}}=\alpha-\mathrm{cl}(hD),\quad L\alpha_{\mathrm{prim}}=0,\quad
\alpha=\alpha_{\mathrm{prim}}+\mathrm{cl}(hD).
\]

This is a construction of an ACTUAL algebraic complement for every codimension-two Hodge class of any fourfold, and it can also take an already algebraic codimension-two Z and construct an actual algebraic primitive Z - h·D.

It does **NOT** establish an actual algebraic representative of an arbitrary unknown α_prim; proving this primitive representation is precisely what the original target requires. The finite-dimensional and Hodge-formal data fields in the Lean interface model classical theorems but are not proved inhabited by existing Mathlib constructions. Do not call the formal implication an unconditional formalization of Hard Lefschetz and Gysin in Lean.

## Route 3: stronger special-family primitive geometry (previously green)

\`GSTMiddlePrimitiveProjectiveProduct.lean\` / run 38692915421 green: for P²×P², primitive middle classes are precisely rational multiples of a²-ab+b², and each basis term is a genuine algebraic intersection (the scheme-cohomology identification is external). This constructs every primitive rational Hodge class in that explicit special fourfold.

\`GSTCubicFourfoldPlanePrimitive.lean\` / run 38694969552 green: a smooth cubic fourfold containing a plane has the explicit algebraic primitive class 3[P]-h², and the intersection pairing is nonzero. The file verifies the exact integer arithmetic of geometric intersection numbers, not the actual scheme construction in Lean.

\`GSTMaximalLinearHypersurfacePrimitive.lean\` / run 38695158747 green: smooth degree-d hypersurfaces of even dimension 2m containing a maximal linear plane P^m have an actual middle primitive algebraic class d[P^m]-h^m, with exact squared intersection (-1)^m d(d-1)^(m+1). Again it proves existence of **one** genuine primitive class in each stated special carrier family, not all Hodge classes on arbitrary varieties.

## Route 4: CM+NM rational rank audit

A single Gaussian CM operation J on a rational Hodge fiber, with J²=-id, has the seed orbit
\[
\mathbb Q[J]\cdot z=\{a z+b Jz:a,b\in\mathbb Q\}
\]
of rational dimension ≤ 2. No quantity of powers of J or *scalar* rational CM/NM coefficients increases that dimension. This is a structural consequence of J²=-id, not an arbitrary numerical threshold.

Wolfram exact calculation used the rational four-dimensional action
\(J=\begin{pmatrix}0&-1\\1&0\end{pmatrix}\oplus
\begin{pmatrix}0&-1\\1&0\end{pmatrix}\).
One seed orbit {J^k z}_{k=0}^{11} has **rank 2** while the ambient rational Hodge space has rank 4. Its characteristic CM relation J²+I=0 holds exactly. Thus a single CM Gaussian orbit is not a universal independent-direction generator. Higher rank needs genuinely independent *algebraically realized* seeds or correspondences mixing actual primitive cohomology.

**Important:** The numerical rank check is a valid example testing a proposed mechanism, not a counterexample to the Hodge conjecture.

## Wolfram exact projector consistency on P²×P²

In bases H²={a,b}, H⁴={a²,ab,b²}, H⁶={a²b,ab²}, with h=a+b, one has
\[
L:H^4\to H^6=\begin{pmatrix}1&1&0\\0&1&1\end{pmatrix},\quad
L:H^2\to H^4=\begin{pmatrix}1&0\\1&1\\0&1\end{pmatrix},
\quad
L^2:H^2\to H^6=\begin{pmatrix}2&1\\1&2\end{pmatrix}.
\]
The universal rational primitive projector is
\[
P_{\rm prim}=I-L(L^2)^{-1}L
=\frac13\begin{pmatrix}
1&-1&1\\-1&1&-1\\1&-1&1
\end{pmatrix}.
\]
Wolfram exactly verified P²=P, rank(P)=1, and L·P=0, with primitive generator (1,-1,1). Since a,b are genuine divisor classes, this particular projector is implemented by native rational algebraic cycle combinations, not an arbitrary Hodge matrix.

## Where the original arbitrary-variety problem stands

**NOT PROVED.** Already genuine universal algebraic primitives: codimension one via (1,1) and the opposite-to-divisor codimension d-1 via Hard Lefschetz. Constructed primitive corrections: codimension two of arbitrary fourfolds, and explicit middle primitive cycles for stated special varieties.

Still missing: for an arbitrary smooth projective X and an arbitrary *unknown primitive* Hodge class α in a middle codimension 2≤p≤d-2, produce a concrete algebraic Z with cl(Z)=α without injecting that equality or an equivalent geometric cyclicity premise.

Any universal proposed CM/NM transfer must establish that actual projective correspondences act nontrivially and span the primitive class space of the arbitrary target, rather than merely generate a rational scalar field or a Gaussian CM orbit of one seed. A failed theorem or an unfinished CI test must not be portrayed as a result.

No public internet search was performed.


## Route 5: unbounded-dimension codimension-two primitive extraction

The new \`GSTUniversalCodimensionTwoPrimitiveExtraction.lean\` file
strengthens the fourfold correction to EVERY possible dimension
d>=4. It uses the actual weight-dependent Lefschetz arrows

\[
L^{d-3}: H^{2,2}(X,\mathbb Q)\to
H^{d-1,d-1}(X,\mathbb Q),\qquad
L^{d-2}:H^{1,1}(X,\mathbb Q)\xrightarrow{\sim}
H^{d-1,d-1}(X,\mathbb Q).
\]

For any rational (2,2) class α the standard analytic Hard Lefschetz
theorem and rational Lefschetz (1,1) theorem construct

\[
D_\alpha\in CH^1(X)_\mathbb Q,\quad
\mathrm{cl}(D_\alpha)
=(L^{d-2})^{-1}L^{d-3}\alpha.
\]

The actual **native algebraic codimension-two cycle**
\(Z_{\rm correction}=H\cdot D_\alpha\) satisfies
\(L^{d-3}\mathrm{cl}(Z_{\rm correction})=L^{d-3}\alpha\).
Therefore
\[
\alpha=\underbrace{\bigl(\alpha-\mathrm{cl}(H\cdot D_\alpha)\bigr)}
_{\in\ker L^{d-3}}\;+\;
\underbrace{\mathrm{cl}(H\cdot D_\alpha)}
_{\text{explicitly algebraic}}.
\]

If the input α is the class of an actual native algebraic
cycle Z, then subtracting the constructed correction from Z
returns an actual algebraic **primitive** codimension-two cycle.
This is a universal nonprimitive-component construction without
any global upper bound on d.

The original universal primitive algebraicity requirement remains
the equality of an arbitrary UNKNOWN primitive remainder with
the class of a concrete algebraic cycle. Nothing here assumes or
proves that assertion.

**CI:** \`gst-universal-codimension-two-primitive.yml\`,
run 38699408237 — **SUCCESS**. The actual arbitrary-dimensional
codimension-two algebraic correction compiled under Lean 4 without
new custom axioms or sorry placeholders. Older fourfold and divisor proofs
are independently green (38698778667 and 38698778620).


## 2026-10-16 Mathbox: arbitrary-fourfold primitive from an actual Gram minor

The exact universal target remains construction of rational algebraic cycles
for every primitive rational (p,p) class of every smooth projective complex X.
This record does not assert that target has been closed.

**New existing-file Lean results** in `GSTUniversalFourfoldPrimitiveExtraction.lean`:
`algebraicLefschetzCorrection_in_divisor_image`,
`primitiveizeNativeMiddleCycle_detector_invariant`,
`nonzero_native_primitive_of_numerical_detector`,
`primitive_native_direction_outside_prior_cycle_span`, and
`native_primitive_of_nonzero_intersection_gram`.
The first four were remote-kernel-verified by GitHub Action run 38910187554.
The Gram-minor theorem also passed its exact GitHub Lean kernel gate:
run 38910663004, conclusion SUCCESS, head 19ea255b36b6fbb50c401c92320f66008a1511d3.
This checks the Lean formalization, NOT the all-X existence conjecture.

Here is the new independent geometric test rather than an arbitrary Hodge
cycle-selector. On a smooth projective complex fourfold let U and Z be
**already constructed actual codimension-two algebraic cycles** and let
r_U, r_Z be rational linear readouts on the rational (2,2) Hodge fiber,
obtained in a genuine application from verified Poincare intersection
pairings. Suppose every divisor-Lefschetz class is in Q*[U]. Set

    D = r_U(cl(U)),  M = r_Z(cl(U)),
    C = r_U(cl(Z)),  N = r_Z(cl(Z)).

If the actual 2x2 determinant Δ = D*N - M*C is nonzero, the explicitly
constructed rational detector

    R(x) = D*r_Z(x) - M*r_U(x)

annihilates the ENTIRE divisor-Lefschetz image while
R(cl(Z)) = Δ ≠ 0. The universal fourfold GST algebraic Lefschetz
correction subtracts an actual native divisor product from Z, constructing

    Z_prim = Z - corrected_divisor_product(Z).

The proof gives primitiveTest(cl(Z_prim))=0 AND R(cl(Z_prim))=Δ≠0.
Thus a **nonzero algebraic primitive cycle exists** in this geometric
situation without assuming an algebraic representative of an unknown
Hodge target. This is existence, not an equivalent Hodge hypothesis.
The required U,Z, readouts, divisor-line property, and determinant must be
certified by independent geometry for each application.

For an actual symmetric intersection form take U=h^2 and r_U(x)=int_X x*h^2,
r_Z(x)=int_X x*[Z]. Then D=int_X h^4, M=C=int_X h^2*[Z],
N=int_X [Z]^2. The explicit rational cycle D*[Z]-M*h^2 is orthogonal
to h^2, with self-intersection D*(D*N-M^2). In a fourfold with one-dimensional
rational H^2 and H^6, orthogonality to h^2 additionally proves geometric
primitivity under the true Lefschetz map. This is a classical mathematical
interpretation of the exact Lean determinant certificate, not a fully
formalized scheme-theoretic intersection pairing in Mathlib.

The concrete cubic-fourfold-with-plane check gives (D,M,N)=(3,1,3),
Δ=8, primitive cycle 3[P]-h^2, self-pairing 24. This recovers and
extends the existing example with a reusable any-fourfold rank test.

**Three active completion routes:** (A) independently construct sufficiently
many algebraic surfaces and certify nonzero Gram minors, ultimately in every
primitive Hodge direction; (B) CM/NM correspondences across actual varieties
with proven period compatibility and rational descent; (C) fixed-class
calibrated integer-rectifiable geometric cycles. None currently establishes
all X, all p, all rational Hodge classes. The finite-dimensional Gram test
cannot create a missing actual source cycle or force the ranks to saturate.

## 2026-10-16 Mathbox: exact universal primitive residual detector firewall

Original target (NOT proved): for every smooth projective complex X, all
codimensions p, and each rational primitive class alpha of type (p,p),
construct an actual rational algebraic cycle Z on X with cl(Z)=alpha.

New formal theorems in EXISTING source
`GSTResidualNormZeroExactHodgeEquivalence.lean`, commit
`0e2f0346e7114e21cec134a6ddec7b3d846b478c`:

- `residual_orthogonal_to_every_native_cycle`
- `no_native_polarized_detector_of_residual`
- `missing_primitive_residual_positive_but_native_undetectable`

They passed the focused Lean kernel CI run **38912526573** (SUCCESS).
The transitive axiom audit for these declarations should be read in that
run's exact source output; the CI pass is not a classical Hodge proof.

Assumptions: Q is the rational polarized intersection pairing on the
primitive (p,p) Hodge fiber. P is a genuine native-cycle packet whose
actual cycle classes span the ENTIRE algebraic image A (not merely a
finite list of discovered representatives), whose detector coordinates
are Q-pairings with native generators. Such a basis of A is legitimate
when the rational Hodge fiber is finite-dimensional, regardless of
whether Hodge algebraicity holds.

For any rational primitive Hodge alpha set

    r(alpha) = alpha - cl(projectedNativeCycle(P,alpha)).

Then for EVERY native algebraic codimension-p cycle Z,

    Q(r(alpha),cl(Z)) = 0.

If alpha is hypothetically missing, the already verified positive
definiteness and projection facts imply

    Q(r(alpha),r(alpha)) > 0

at the very same time as EVERY native-cycle readout Q(r,cl(Z)) vanishes.
There is no contradiction. The new theorem explicitly rules out
saturating the missing direction solely by increasing the list of
already-native intersection detectors. In particular, a newly
DISCOVERED cycle still belonged to the mathematical definition of A
before it was discovered; it does not enlarge the complete image A.

Executed program routes, with exact first unresolved implications:

1. Full GST rank-free matrix units: these mix rational Hodge basis
   coordinates abstractly. Constructing equivalent *geometrically
   realized* operators on arbitrary X remains unproved; the existing
   native-realization firewall demonstrates why abstract operator
   identities are insufficient.
2. CM/NM, graph words, native commutators and rational Gram growth:
   when the operations are true algebraic correspondences, they act
   within A, and cannot pair nontrivially with r(alpha). Special
   geometries (P1xP1, cubic fourfold with a plane, abelian/CM and K3
   examples) yield genuine constructions only for their stated scopes.
3. Projective anti-graph and integral-current surgery: projective
   cellular parity identities do not extend to arbitrary X without
   independent algebraic basis cycles. A positive smooth closed current
   after an ample shift is NOT an integral rectifiable calibrated
   algebraic cycle; the latter independent geometric replacement is
   unproved for each arbitrary rational primitive Hodge class.

The only successful universal endgame would independently establish
that no nonzero residual r(alpha) is possible for the actual geometric
cycle map, or construct an actual algebraic representative of alpha
without assuming an equivalent reachability, Gram-saturation, or
period-certificate existence statement. We did NOT obtain that theorem.
The experiment eliminates a false universal inference but does not
rule out a fundamentally new GST geometric construction.

Next direct research attack, rather than more formal rank wrappers:
construct from alpha a genuinely closed integral (p,p)-calibrated
rectifiable representative in the exact rational homology class after
clearing denominators and a known algebraic ample correction. Check
every proposed GST N-current surgery preserves the prescribed
homology class and integral multiplicities; a smooth positive or weak
limit alone cannot discharge this. Independently investigate
geometrically obtained cross-carrier correspondences whose native
cycle outputs provably cover a previously unavailable primitive
Hodge direction, without using alpha as a preexisting cycle input.


## Mathbox 2026-10-16: exact all-X projective stabilization to primitive MIDDLE Hodge classes

**Unchanged universal target.** For every smooth projective complex
X, dimension d, rational Hodge (p,p) class alpha (primitive when 2p<=d),
construct an ACTUAL rational algebraic cycle representing alpha.
The target remains open: the following is an unconditional geometric
REDUCTION, not existence of a middle primitive cycle.

### An explicit construction on EVERY X, every p with 2p<=d

Put m=d-2p and Y=X x P^m (complex dimension d+m=2(p+m)),
with projections pi_X, pi_P. Choose an actual ample class h on X
and the actual P^m hyperplane class t. If alpha is primitive,
h^(m+1)*alpha=0.

Set the RATIONAL MIDDLE-HODGE class
  B(alpha) = sum_{j=0}^m (-1)^j pi_X^*(h^j alpha) pi_P^*(t^(m-j)).

All terms have Hodge type (p+m,p+m) and cohomological degree
2(p+m)=dim_C(Y). Multiplication by the PRODUCT ample class
H=pi_X^*h+pi_P^*t produces:
* interior coefficient of h^j alpha t^(m+1-j), j=1,...,m:
  (-1)^(j-1)+(-1)^j=0;
* P^m bottom boundary t^(m+1)=0;
* X top boundary (-1)^m h^(m+1)alpha=0.
Thus H*B(alpha)=0, i.e. B(alpha) is a GENUINE PRIMITIVE
rational middle Hodge class of Y. No chosen Chow preimage is used.

Fiber integration pi_{X*}:H^{2(p+m)}(Y)->H^{2p}(X)
takes the coefficient of t^m, hence pi_{X*} B(alpha)=alpha.
On algebraic cycles, if B(alpha)=[W] with W an actual codimension
p+m rational Chow cycle of Y, the genuine algebraic Chow pushforward
Z=pi_{X*} W has codimension p and [Z]=alpha by cycle-class
naturality. Conversely if alpha=[Z] is algebraic then the explicit
Chow packet sum (-1)^j pi_X^*(H_X^j * Z)pi_P^*(H_P^(m-j))
represents B(alpha). Hence for EVERY individual primitive alpha:

  alpha is algebraic on X  <=>  B(alpha) is algebraic on Y.

This is a pointwise correspondence of ACTUAL Chow classes and Betti
classes, not an invented 'algebraicity' marker in an abstract vector
space, and DOES NOT assume inverse Hard Lefschetz to be algebraic.

### Stronger bijective primitive-fiber theorem

The rational projective-bundle/Kunneth formula uniquely writes ANY
middle rational (q,q) Hodge class b of Y, q=p+m, as
  b=sum_{j=0}^m pi_X^*(b_j) t^(m-j),
where b_j has rational Hodge type (p+j,p+j) on X.
If H*b=0 then its coefficients obey:
  b_(j+1)=-h*b_j (j=0,...,m-1), and h*b_m=0.
Therefore b_j=(-1)^j h^j*b_0 and h^(m+1)*b_0=0.
The top-fiber coefficient b_0=pi_{X*} b is primitive.
Thus B and pi_{X*} are explicit MUTUAL INVERSES

  Prim^{p,p}_Q(X,h)  <==>  Prim^{p+m,p+m}_Q(X x P^m,h+t).

This holds for ALL smooth projective complex X and ALL p in 2p<=d,
without a dimension/rank bound or algebraic cycle assumption.

The verified Lean source GSTAllDimensionProjectivePrimitiveCycles.lean
proves the arbitrary-module signed recursion, boundary cancellation,
recovered source coefficient, inverse unique primitive classification,
and bidirectional primitive condition. Both targeted GitHub CI runs are
GREEN: 38916032821 (source-to-middle) and 38916436720 (both directions).
These are Lean kernel checks of exact rational coefficient algebra. The actual projective-bundle ring,
Hodge functoriality and Chow naturality are independent classical
geometric inputs not constructed inside that Lean module. Do not
mistake a coefficient theorem for complete Lean formalization of
analytification or Chow cohomology.

### Why this cuts down the quantifiers but DOES NOT end Hodge

The usual rational Hard Lefschetz decomposition expresses each
low-degree Hodge class as sums of ample powers of primitive rational
Hodge classes. High-degree classes are ample powers of low-degree
Hodge classes, by rational Hard Lefschetz. Therefore ALL rational
Hodge classes on ALL smooth projective X would be algebraic if,
and only if, EVERY rational primitive MIDDLE Hodge class on EVERY
even-dimensional smooth projective Y were algebraic.

This removes nonmiddle primitive geometry from the universal target
but does NOT establish middle primitive algebraicity on arbitrary Y.
In particular X x P^m is generally NONCELLULAR whenever X is;
no existing GST cellular, CM/NM orbit, or calibrated-current theorem
supplies the missing Chow representative automatically.

### Independent attack: finite projections lose primitive data

For a finite morphism f:X->P^d, let h=f^*H. If 2p<=d and p>=1,
alpha is primitive with h^(d-2p+1)alpha=0, then
f_*alpha = c H^p for rational c. By projection formula,
 c=int_{P^d}(f_*alpha)*H^(d-p)
  =int_X alpha*h^(d-p)
  =int_X (h^(d-2p+1)alpha)*h^(p-1)=0.
Hence f_*alpha=0 for EVERY primitive alpha.
Consequently finite Noether-normalization maps to cellular P^d
erase, rather than realize, the missing primitive Hodge directions.
This is a structural obstruction to using projective cellular
targets alone; it does not contradict Hodge on X.

**Exact unresolved existence obligation:** For each arbitrary
even-dimensional Y and primitive rational middle Hodge class b,
construct an actual algebraic middle-dimensional cycle W on Y
with [W]=b, WITHOUT assuming b already lies in the native image.
Only this new geometric input can promote the reduction to a
solution of the full conjecture.


## 2026-10-16 Mathbox: source-birth GST and rational-host primitive propagation

The proof goal remains construction of genuine algebraic-cycle representatives
of every rational primitive Hodge class on arbitrary smooth projective complex
varieties. GST graph V2 has now been strengthened within its own original
self-expanding world cosmology, not replaced by an alternate theory.

NEW INTERNAL GST THEOREMS in GSTGraphV2SelfExpandingCosmology.lean:
* TwoSourceBirth carries rational-native cycles and genuine rational Hodge
  cohomology for a parent world, independent source world, and a born world,
  with actual native transport, cycle-class compatibility and a genuine
  cohomological two-source decomposition (no native preimage of the target).
* every_newborn_hodge_class_has_native_cycle constructs an explicit native
  newborn cycle from source representatives.
* exceptional_native_birth_creates_new_hodge_direction detects an independent
  exceptional native cycle outside the whole parent Hodge image.
* SplitTwoSourceBirth adds actual native/Hodge retracts;
  split_world_birth_hodge_complete_iff_sources proves that completeness of
  the born world is equivalent to completeness of both source worlds.
* source_missing_direction_survives_birth, its exceptional counterpart,
  and algebraic_host_complete_iff_exceptional_complete characterize
  the inherited defect and the exceptional sector on a complete base.

The first two upgrades passed GitHub CI runs 38919599650 and 38920157401.
The specialized exceptional host theorem is separately run as 38920606718.
CI proves the GST algebraic birth calculus, not Chow blowup compatibility
on an arbitrary genuine scheme.

GEOMETRIC ALL-X HOSTING:
For any smooth projective X of dimension d, choose a closed embedding
X -> P^N with codimension c>=2. Let Y be the smooth projective blowup
Bl_X(P^N), a rational variety. The genuine blowup Chow and rational Hodge
formulas give compatible decompositions:
  Hdg^p(Y)=Hdg^p(P^N) (+) SUM_{j=1}^{c-1} Hdg^{p-j}(X)(-j),
  CH^p(Y)_Q=CH^p(P^N)_Q (+) SUM_{j=1}^{c-1} CH^{p-j}(X)_Q.
They instantiate the GST source-birth packet with source B equal to
the exceptional direct sum. Because P^N is Hodge-complete,
  all rational Hodge classes algebraic on Y (all p)
    IFF all rational Hodge classes algebraic on X (all p).
The unknown Hodge directions of an arbitrary X are thus faithfully
hosted as exceptional geometry INSIDE rational projective blowups.
This is not a proof that the host is automatically algebraic.

UNCONDITIONAL GEOMETRY FAMILY 1 (ALL DIMENSIONS):
Every smooth projective complex UNIRATIONAL variety X has algebraic
rational Hodge (2,2) classes. Resolve a dominant generically finite
rational map P^n --> X as smooth blowups of P^n followed by f:Y->X.
In degree four, the exceptional Hodge contributions for a blowup of
a smooth center Z are only H^2(Z)(-1) and H^0(Z)(-2).
They are genuine divisor and component classes, algebraic on every Z,
regardless of its dimension. Thus codimension-two Hodge algebraicity
passes through every blowup. Given any rational Hodge (2,2) alpha on
X, f^*alpha has an algebraic native representative on Y, and the
projection formula f_* f^* alpha=(deg f)*alpha gives a rational
algebraic representative on X. Hard Lefschetz gives the corresponding
codimension n-2 classes as ample powers when n>=4.

UNCONDITIONAL GEOMETRY FAMILY 2:
All rational Hodge classes on every smooth projective UNIRATIONAL
variety of dimension n<=5 are algebraic. In that range, blowup
centers on the resolution of P^n have dimension <=3, and ALL
rational Hodge classes on smooth projective centers of dimension
<=3 are algebraic by the Lefschetz (1,1) and Hard Lefschetz theorems.
The full Chow blowup decomposition and generically finite descent
finish this family.

The two families are rigorous arguments using genuine algebraic
geometric blowup and pushforward theorems; those SCHEME-level theorems
have NOT been formalized in the GST Lean module. New GST Lean theorems
certify source-birth logic, while these genuine geometric families
are mathematical instantiations, not machine-proved schemes.

REMAINING ORIGINAL SOURCE-DISCOVERY OBLIGATION:
Construct enough independent geometric source births for every primitive
Hodge class of arbitrary nonunirational varieties, with genuine
cycle-class compatibility. The actual new GST birth calculus permits
these births without restricting to old CM/NM within-world orbits,
but it does not postulate their universal existence.

## 2026-10-16 Mathbox: unbounded heterogeneous GST births and finite-degree geometric descent

Original target remains genuine algebraic-cycle representatives for every
primitive rational Hodge class on every smooth projective complex variety.
Neither the present world-birth law nor the geometric application claims
that unrestricted statement is proved.

### Stronger internal GST cosmology law

The existing GSTGraphV2SelfExpandingCosmology.lean now contains
GeometricCycleBirthRealization, a genuinely dependent realization where
native cycle/state types and rational Hodge/law types can DIFFER across
arbitrarily many source worlds. An indexed world-birth certificate contains
native assembly, Hodge assembly, exact cycle-class compatibility, and
an independently supplied decomposition of the newborn Hodge fiber.
Every_world_birth_has_native_realization constructs a native cycle for
each newborn Hodge class from native source cycles with no fixed source
cardinality. Generated_worlds_have_native_cycles combines this with the
original impredicative WorldClosure/generation induction: roots with actual
cycle representatives and geometrically complete source births imply the
existence of native representatives in every descendant, at any depth.
The proof has no fixed rank, dimension, or length of world-generation.
Target Chow preimages are NOT assumed, but source geometry packets must
be checked independently for any actual arbitrary X.

GitHub Lean source commit 27d49c7464cb852b8b3df05b85058b1873ee66e7
was checked GREEN by CI run 38922541450. This is abstract dependent
world realization, not a Mathlib Chow blowup instantiation on all X.

### Degree descent: a second independent GST geometric operator

FiniteDegreeNativeDescent.DegreePacket carries two genuine native
cycle-class maps, Hodge pullback, native pushforward, Hodge pushforward,
compatibility cl(f_*Z)=f_*cl(Z), nonzero rational geometric degree e, and
the projection identity f_*f^*(alpha)=e*alpha.
If all rational Hodge classes on source Y are algebraic then for any
rational Hodge alpha on target X choose genuine Z on Y with
cl(Z)=f^*alpha and define Z_X=(1/e)*f_*Z. Its actual target class is
cl(Z_X)=alpha. This is independent of Hodge dimension, rank, or codim.
The Lean theorem is realize_target_via_degree_pushforward, plus the
surjectivity corollary degree_descent_preserves_all_hodge_classes.
The genuine finite-degree descent theorems passed Lean kernel CI run
38923116042 at commit 7317e8180cec31a680f9bfb790b1f719cb27da79.

### New unconditional high-dimensional NONUNIRATIONAL family

Let B be ANY smooth projective complex base with dim_C(B)<=3.
Starting with B, form any finite tower of projectivizations of
algebraic vector bundles, Y_r=P(E_r)->...->Y_1=P(E_1)->B.
Each projective-bundle Chow decomposition and rational Hodge
decomposition are compatible with Chern/hyperplane cycle classes:
Hdg^p(P(E))=SUM_{j=0}^{rank E - 1} xi^j pi^*Hdg^{p-j}(base),
CH^p(P(E))_Q=SUM_{j=0}^{rank E - 1} xi^j pi^*CH^{p-j}(base)_Q.
For dim B<=3, every rational Hodge class on B is algebraic by
Lefschetz (1,1) and rational Hard Lefschetz. The compatible projective
bundle decompositions therefore construct genuine Chow representatives
for EVERY rational Hodge class on every Y_r, at ANY height/dimension.

Now let f:Y_r->X be ANY dominant generically finite morphism to a
smooth projective X. Pull any rational Hodge alpha on X to Y_r,
construct the source Chow cycle from the tower, and push back with
1/deg(f). The cycle-class equality on X holds in every codimension.
This new class includes genuinely NONUNIRATIONAL smooth projective
varieties of arbitrarily large dimension: take B a projective K3
surface or abelian threefold, and an arbitrary high-rank projective
bundle Y=P(E) over B. Its holomorphic 2-forms prevent Y from being
unirational, while all rational Hodge classes are explicitly
algebraic. Smooth generically finite quotients/images of such towers
are included by the degree law.

This family is a rigorous mathematical consequence of genuine classical
projective bundle and Chow pushforward theorems instantiated within the
new GST birth/descent calculus; neither those geometric comparison
theorems nor the full scheme-level Hodge statement are yet formalized
inside the Lean module. This is not claimed as a novel independent
solution of the unrestricted Hodge conjecture.

### Unresolved geometric challenge

Build a GST native-world birth realization FOR EVERY arbitrary smooth
projective X and every primitive Hodge class, using independently
available geometric source cycles. Arbitrary-arity closure cannot
turn an unverified decomposition packet into a geometric theorem.
Find a source construction beyond projective bundle/cellular/blowup
and generically finite-dominance routes, e.g. a genuine new
non-cellular primitive cycle birth with cycle-class comparison.

### Concrete nonunirational tenfold: K3 times P8

Choose any smooth projective K3 surface S over C and take
Y=S x P^8, a smooth projective tenfold. K3 has a nonzero
holomorphic two-form, inherited by Y, so Y is NOT unirational.
Nevertheless EVERY rational Hodge class of Y has a fully explicit
algebraic cycle representative, without a fixed codimension bound.
Let h denote the algebraic P8 hyperplane cycle. The projective
bundle formula and rational Hodge decomposition show that for each
0<=p<=10, every rational Hodge class alpha in H^{2p}(Y,Q) has the
unique form h^p a0 + h^(p-1) a1 + h^(p-2) a2, omitting exponents
outside 0,...,8, where a0 in Hdg^0(S,Q)=Q[1],
a1 in Hdg^1(S,Q)=NS(S)_Q, and a2 in Hdg^2(S,Q)=Q[point].
All three are represented by actual codimension 0,1,2 algebraic
cycles on S. Multiplying their pullbacks by the corresponding
P8 algebraic hyperplane products builds an actual cycle for alpha.

For Picard rank rho(S), the dimension of rational (p,p) Hodge
classes on Y is exactly:
  indicator(0<=p<=8) + rho(S)*indicator(1<=p<=9)
    + indicator(2<=p<=10).
This is a concrete arbitrarily high-dimensional nonunirational
family once P8 is replaced by Pr for any r.

More generally smooth projective generically finite images of
projective-bundle towers over any smooth projective threefold
have rational Hodge algebraicity in every codimension. The
native-degree descent formula is (1/deg f) f_* of an explicitly
constructed source cycle, as encoded in the new GST geometry law.
This broad family is a mathematical corollary of established
projective bundle and Chow formulas. It does NOT settle arbitrary
nonunirational primitive Hodge geometry.

### Further GST construction: unlimited noncellular blowup births from low-dimensional centers

Build a base Y0 by ANY finite projective-bundle tower above ANY smooth
projective B of complex dimension at most 3. It may have arbitrarily
high dimension and nontrivial holomorphic forms. Repeatedly choose
ANY smooth closed center Zi inside Yi, of ANY codimension, but with
dim_C(Zi)<=3, and let Yi+1=Bl_Zi Yi. No common cellular structure
or uniform global dimension bound is required.

The genuine Chow and rational Hodge blowup decompositions are
compatible term by term with algebraic exceptional Gysin maps:
  cl(Z_new) = pullback cl(Z_old)
    + SUM_{j=1}^{c-1} j_* (xi^(j-1)*p^* cl(Z_center,j)).
Here c is center codimension, E=P(N_Z/Y), j:E->Bl_ZY,
p:E->Z, and xi=c1(O_E(1)). The center Hodge classes are
all algebraic because dim Zi<=3; the base is algebraic by
projective-bundle decomposition and the same low-dimensional
Hodge theorem. Thus induction through EVERY such birth
CONSTRUCTS an actual rational Chow representative for EVERY
rational Hodge class on Yi. Rank, number of blowups and
dimension of total spaces are unrestricted.

Then for ANY dominant generically finite morphism f:Yr->X
to a smooth projective X, the explicit actual source cycle Zr
representing f^*alpha descends to (deg f)^(-1)f_*Zr, whose
cycle class is alpha. This combines the GST unbounded world-birth
constructor and native degree-descent constructor in one
cross-world construction chain. The family strictly includes
projective-bundle towers and earlier pure unirational examples.

This establishes full rational Hodge algebraicity in all
codimensions for this nonunirational all-dimensional geometric
family. It is an unconditional consequence of known genuine
blowup/projective-bundle/pushforward formulas; this geometric
instantiation is recorded mathematically, while the current Lean
work verifies the GST abstract assembly and descent compatibility
rather than full Mathlib Chow-blowup realization.

The target of EVERY arbitrary smooth projective X is not covered:
the existence of a dominating source assembled from these
low-dimensional-center births is not established for general X.


### Exact degree-packet composition and defect-persistence audit

Additional existing-file Lean theorems were proved after a genuine
mathematical gluing correction: DegreePacket.compose requires the
EXACT identity P.targetCycle = Q.sourceCycle at the intermediate
world, rather than silently treating unrelated cycle-class maps
as the same. This necessary law was discovered by GitHub Lean CI
run 38923661210; the corrected full laws are in commit
46e89ccf65832e65ff8e93b7037bc8bd364de266.
Composition preserves actual native pushforward naturality and
multiplies geometric degrees precisely d1*d2. The two-stage theorem
proves algebraic target representatives from the far source.
The reverse missing-target theorem proves that an unrepresented
Hodge direction on the target must remain unrepresented after
pullback to the finite-degree source, so a finite cover cannot
conceal the missing primitive Hodge defect. Both passed GitHub
Lean kernel CI run 38924122723.

Next noncellular birth discriminator: all projective-bundle and
low-dimensional-center blowup towers above a base dim<=3 have
H^{4,0}=0 (holomorphic forms are unchanged by bundle and smooth
birational blowup operations). Thus no such tower can dominate
a smooth projective target with H^{4,0} nonzero by a generically
finite morphism: pullback of nonzero top holomorphic forms would
contradict source vanishing. An abelian fourfold supplies such a
target. This proves our current explicit source family cannot
generate ALL smooth projective geometries, and points to the
missing high-holomorphic-degree GST source worlds. It does not
disprove the rational Hodge conjecture on abelian fourfolds.

### GST CM source-world escape: all rational Hodge classes on arbitrary powers of one CM elliptic curve

Choose a genuine complex elliptic curve E with complex multiplication
by an imaginary quadratic field K (for example y^2=x^3-x).
Let A=E^n for ANY n>=1. The CM Hodge group is the norm-one
torus T associated to K. After extension from Q to K,
H^1(A,K) splits into n copies of the CM character chi and
n copies of its inverse. Write x_1,...,x_n for chi-weight
basis and y_1,...,y_n for inverse-chi-weight basis.

A rational Hodge class in degree 2p, extended to K, lies
exactly in the weight-zero part of exterior power 2p.
That invariant subspace is
  (wedge^p K^n) tensor (wedge^p K^n),
dimension choose(n,p)^2, with K-basis monomials
  x_{i1}^...^x_{ip}^y_{j1}^...^y_{jp}.
Every balanced monomial factors, up to sign, into p PAIRS
  (x_{i1}^y_{j1}) ... (x_{ip}^y_{jp}).
These degree-two pairs exhaust the K-linear extension of
the rational (1,1)-Hodge classes. Rational descent works
because invariants commute with extension for this torus;
thus the full rational Hodge invariant algebra on E^n
is generated by its rational degree-two Hodge subspace.
By Lefschetz (1,1), all rational degree-two Hodge classes
are actual rational divisor classes. Therefore EVERY rational
Hodge (p,p) class on E^n is a Q-linear combination of
products of genuine algebraic divisors, for ALL n and ALL p.
Nothing is selected from unknown codimension-p Chow preimages.

Exact independent Wolfram coefficient check for n=6:
  [t^0] ((1+x*t)^6 (1+x/t)^6)
  = 1+36*x^2+225*x^4+400*x^6+225*x^8+36*x^10+x^12.
The symbolic difference from SUM_{p=0}^6 choose(6,p)^2*x^(2p)
evaluated identically to zero. For n=4, the middle (2,2)
rational Hodge subspace has dimension choose(4,2)^2=36,
all generated by products of actual divisor classes.
Finite rank checks test the invariant count, NOT the all-n
conclusion; the matching-pairs factorization proves all n.

IMPORTANT: These are established CM-Hodge invariant-theoretic
and Lefschetz (1,1) facts, here integrated into the user's
GST CM number-manipulation/geometric-source construction.
This actual abelian cycle geometry is not claimed to be
formalized by the current abstract GST world-birth Lean module.
The primary-source theorem attribution/edition was not
independently authenticated in this no-web project session.

NEW unlimited high-holomorphic-form GST source family:
Start with ANY E^n as above, for unrestricted n. Build any
finite tower of projective bundles and smooth blowups along
centers whose own rational Hodge classes are already
algebraic (in particular any center dimension <=3).
The actual Chow and Hodge splitting maps construct all
rational Hodge classes at every birth. A dominant generically
finite morphism from this final tower to any smooth projective
X then constructs all rational Hodge cycles on X via
(1/deg f)*f_*Z_source. Unlike the earlier base-dimension<=3
family, these sources have holomorphic k-forms for ARBITRARILY
large k, taking n>=k. Thus the 4-form non-dominance obstruction
to low-dimensional bases is genuinely overcome for a new
large class of high-dimensional noncellular source worlds.

The unrestricted all-X target still requires a proof that
EVERY arbitrary primitive rational Hodge class can be
represented by a cycle generated from such independent sources.
No such universal source dominance is asserted here.

## 2026-10-16 Mathbox: direct Lean formalization of scheme-typed geometry and CM cycles

The original target remains actual rational algebraic-cycle representatives
for all primitive rational Hodge classes on every smooth projective complex
variety. This checkpoint now has machine-checked NATIVE SCHEME CARRIER
results rather than only rational-vector-space GST world laws.

GSTUniversalChowRetractToTarget.lean was upgraded as follows:

* GeometricMultiSourceChowBirth has a finite dependent family of actual
  smooth-projective source SCHEMES, with separate source codimensions, true
  codimensionCycles carriers, native transfers and exact Betti cycle-class
  comparison. The proof chooses native source cycles and builds a concrete
  finite sum in the TARGET codimensionCycles carrier. Kernel gate GREEN:
  38932725902 at 4939864fd8d0a87486657dfd7cb9ef448ae99cae.
* GeometricSplitGysinPacket strengthens the source expansion from an
  arbitrary existence formula to explicit rational cohomology READOUT maps
  preserving Hodge type, and proves decomposition from a reconstruction
  identity. Its actual-Chow conclusion was kernel verified GREEN:
  38933800121 at ec4394ee0ab52b7777be3924d7a4ae78e0851d9f.
* SchemeProjectiveBundleGysin indexes native source groups by
  CH^(p-j)(B), for each j:Fin r, and proves native Chow representatives
  on the genuine total scheme from projective-bundle Gysin readouts.
* SchemeBlowupGysin indexes ONE base summand plus precisely
  c-1 exceptional center summands, at source codimension p-(j+1).
  The source and target cycle carriers are actual schemes and the
  target is the real native CH^p space of the born world.
* SchemeTypedGSTGeometricTower is an unbounded inductive construction
  over actual smooth-projective carriers, with independently solved
  seeds and arbitrarily deep projective-bundle/blowup births. Theorem
  every_scheme_world_in_GST_tower_has_actual_hodge_cycles proves the
  full all-codim target on every certified descendant. The combined
  new geometric build runs on 38934997492; check its exact verdict
  before claiming these latest constructors are kernel verified.

GSTCMFiniteGeometricDegreeDescent.lean was upgraded as follows:

* CMBalancedCharacterWord records p positive and p negative CM
  characters, with exact canonical degree-two pairing.
* CMNativeProductRealization uses actual codimensionCycles of a
  specified smooth projective scheme at every degree, a native unit,
  true native divisors, genuine native products, rational Betti
  multiplication, and true cycle-class naturality.
* cm_native_word_cycleClass constructs an actual p-divisor product
  and proves its exact rational Betti class by structural induction
  on p. CI GREEN: 38933352554.
* cm_balanced_divisor_words_are_rational_hodge proves all these
  resulting classes have type (p,p) in the ACTUAL HodgeBigrading;
  this uses independently supplied rational Hodge cup compatibility.
* hodge_on_target_of_cm_character_products_and_geometric_degree
  composes a source CM word expansion, actual native divisor products
  and genuine finite-degree pullback/pushforward into an
  all-codimension target Hodge statement. CM CI GREEN for both
  full-descent integration (38934026412) and explicit Hodge
  type of native products (38934361836).

CRITICAL FORMAL BOUNDARIES:

1. The actual scheme-type names and codimension cycle spaces are fixed,
   but HodgeBigradedBettiData.cycleClass is STILL a supplied rational
   linear map in GSTGeometricRealizationStage2G.lean. Its identification
   with the analytically defined geometric cycle-class map is not
   established automatically by using the same field name.
2. The true projective bundle pullbacks, exceptional Gysin maps,
   rational Hodge decomposition and reconstruction from an actual
   Mathlib blowup scheme are DATA required by the geometric packets.
   The packets do not secretly instantiate those maps for arbitrary X.
3. CMActualHodgeCharacterExpansion is the exact remaining theorem
   of the genuine CM Hodge torus representation; the cycle-product
   constructor does not itself establish that every rational Hodge
   class of E^n has a balanced character expansion.
4. The unrestricted all-X primitive algebraic representative still
   requires independently constructed new geometric source directions.
   Compilation of any conditional constructor is not a proof of that
   missing universal existence assertion.

## Mathbox 2026-10-16: norm-one CM invariant semigroup theorem, no numerical rank cutoff

Goal: turn the CM Hodge representation of an ACTUAL E^n into
actual Chow divisor products and ultimately reach arbitrary primitive
rational Hodge directions on arbitrary projective varieties.

Inside the EXISTING GSTCMFiniteGeometricDegreeDescent.lean, new
cmCharacterWeight records integral norm-one CM torus weight as
(number of positive characters)-(number of negative characters).
cm_weight_zero_iff_balanced proves weight zero iff counts equal
for every n and arbitrarily long character lists.
cmQuadraticPairs is an explicit constructive matching algorithm;
cm_torus_invariant_factorizes_quadratically reconstructs BOTH
positive and negative weight lists exactly for every weight-zero
monomial, including the zero-length boundary.

CMInvariantCharacterMonomial n is the subtype of all weight-zero
characters represented by two index lists. The actual character
semigroup generation theorem
cm_invariant_semigroup_generated_by_quadratics proves a SURJECTION
from arbitrary lists of degree-two positive-negative generator
pairs onto ALL invariant monomials, uniformly over every n.
This proves the full Hilbert generating law for the abstract
norm-one torus MONOMIAL semigroup, not merely a finite rank count.

cmNativeCycleFromTorusWeight then uses REAL scheme-typed native
Chow divisor multiplication to construct a cycle from the
quadratic generator word. The theorem
cm_zero_weight_character_has_actual_algebraic_hodge_cycle
proves its true cycle-class equality, rational (p,p) type and
exact reconstruction of BOTH character lists using the
independently certified CMNativeProductRealization packet.

The no-cutoff character pairing proof passed GitHub Actions
38936622219 at 54c5296c680dbaf08f0aa17347e122b8eac5fe98.
The integrated constructor is at commit
2d68e3e800c8d59b90d0cbbb1376738161170825.
The new semigroup surjectivity was first attempted at commit
348b92cc0342d2ee248dd30a40aac5b40cba1a2c;
run 38937229168 failed on the reserved Lean parser identifier `rec`,
not on the mathematical statement. The correction is commit
0d54eedea4364e17a73e6946ad725917e565ed82.
Full CM kernel gate 38937754946 then PASSED with no sorryAx.

SEMANTIC BORDER: the exterior cohomology algebra uses Koszul
anticommutation signs. Its identification with the monomial
torus semigroup needs the exterior wedge ordering and sign
comparison. More decisively, the ACTUAL Hodge representation
of CM elliptic power E^n and its diagonal CM Hodge group
have not been connected to this weight-zero character model
by an unconditional Lean scheme/analytic comparison.
The signed character pairing theorem DOES NOT assume the
algebraicity of any arbitrary target Hodge class, but the
model-to-actual-Hodge expansion is still required.

ORIGINAL UNIVERSAL HODGE STATUS: not established.
Even a complete E^n CM proof would not establish a genuine
finite-degree cycle-complete source dominating every arbitrary
smooth projective variety; such a dominance claim must not
be smuggled into the GST cosmology's world-birth packet.


The integrated CM native constructor from signed zero-weight lists,
`cm_zero_weight_character_has_actual_algebraic_hodge_cycle`, is also
included in the successful kernel build 38937754946. It produces a
true `codimensionCycles S.X p` using actual native divisor products,
not a Hodge-class-to-Chow choice. The exact source product and Hodge
comparison are separately checked fields of `CMNativeProductRealization`.


## 16 October 2026 Mathbox: mixed-world CM field descent and unbounded multicharge frontier

**Exact target unchanged.** For every smooth projective complex variety
X and every primitive rational Hodge class alpha of degree 2p,
construct an actual codimension-p rational algebraic cycle with
geometric cycle class exactly alpha. Replacing alpha with a
CM/General-Space world address or a chosen linear map does not count.

**Base branch checkpoint:** 379382064524cbf7ff15887d1a7d989b14b533a2.
**Genuine improvement:** a rational primitive Hodge target on an
arbitrary X can now be reached from independently constructed native
cycles on *different source varieties of different codimensions*,
with expansion coefficients in ANY field extension K/Q. Actual
cross-carrier transfers land in CH^p(X), while the normalized
Q-linear coefficient projector constructs a rational native cycle.
The built theorem is
GSTClassicalHodgeCMNativeRationalDescent.
native_target_cycle_of_multisource_CM_field_spanning.
The required K-linear Betti equality is a geometric source-spanning
input and MUST be derived from actual correspondences/eigenperiods:
it is not automatic for every alpha. Kernel run 38948869754 SUCCESS
at workflow repair commit 00dc1380610a57197fcf6e939fef911d02e01be6.
Earlier run 38948520559 failed solely because the Chow source
module had not been registered in the Lake library roots.

The original CM rank-one norm-one torus law now also provides
GSTCMFiniteGeometricDegreeDescent.
native_rational_cm_cycle_of_geometric_field_expansion.
The input may have coefficients in K, no longer necessarily Q,
and the output is a true rational Chow cycle. Kernel run
38947942065 SUCCESS at 01dc8fe16395ca10b44d2decd8b1d686b208793e.
Remaining E^n geometric leaf: identify the actual rational
Hodge realization with the Hodge-group character decomposition,
verify exterior/Koszul signs, and show the geometric divisor
word classes map to the quadratic eigencharacter generators.
Formal semigroup generation is not a substitute for that leaf.

**Cross-GST general-space computation:** In
GSTGeneralSpaceCohomology.lean theorems
algebraicity_iff_reversible_general_space_transport and
missing_native_direction_persists_recoordination now derive from
strict native-cohomological path naturality. They hold across
arbitrary reversible paths in the original GST General Space
geometry, so reversible CM/NM/cosmology *recoordination* cannot
independently generate a previously absent algebraic Hodge
direction. To advance universal existence, one needs a GENUINELY
new native cycle from an irreversible birth/source, or independent
geometric existence input. Kernel run 38947843787 SUCCESS.

**Higher CM-charge route, substantially beyond the old
one-dimensional norm-one Hodge torus:** Integral torus characters
may have multi-charge vectors. Wolfram exact finite checks:
  rank-two charges (1,0),(0,1),(-1,-1)
form a minimal zero-sum triplet with no zero-sum pair.
An even-degree, Hodge-relevant candidate has
  (1,0),(0,1),(-1,2),(0,-3).
The total weight is zero; none of the 14 nonempty proper
subsets is weight zero, and no pair (16 ordered options) or
triple (64 ordered options) of the four weights has zero
weight, *even allowing repetition*. The latter checks were
computed with Wolfram exact integer arithmetic, no sampling.

**Uniform all-codimension strengthening:** For arbitrary N>=2,
weights a=(1,0), b=(0,1), c=(-N,-1) make the word a^N b c
zero weight. Any subword has m copies of a, u/v in {0,1}
copies of b/c. The two character equations
    m-N*v = 0,  u-v=0
force either m=u=v=0 (empty) or m=N,u=v=1 (whole).
With N=2p-2, this yields a primitive *formal* multi-charge
torus invariant in every even degree 2p for all p>=2.
Thus, across arbitrary character lattices, a universal
constant bound on the degree of zero-weight generators
cannot exist. Lean definitions/theorems in
GSTUniversalCMArithmeticObstruction.lean:
cubic_CM_atom_requires_new_generator,
quartic_CM_higher_generator_necessary,
CM_multicharge_zero_sum_atom_all_lengths,
CM_unbounded_even_degree_primitive_atom.
The combined cubic/quartic/unbounded-all-even-degrees Lean kernel gate
38949836999 PASSED at repaired commit
1f6a31528fdcc24cd5a2a5e40e6bfca860dfa23b with no sorryAx.
Earlier gate 38949280580 failed only because the Fin 2 arithmetic
simplifier left two small conditional-expression goals; both were
repaired by kernel `decide`, without changing the mathematical claim.

**Critical semantic firewall:** An integer torus character
zero-sum, EVEN at degree 2p, is NOT automatically a (p,p)
rational Hodge class in any genuine smooth projective
complex variety; nor is there a Chow preimage of that class.
To convert the new higher-charge GST invariant atoms into
actual algebraic geometry, one must independently
(1) exhibit a Hodge representation whose rational Hodge
subspace contains the given character invariant and
(2) construct a genuine native cycle with matching
Betti class. This is the active genuinely new cycle-birth
problem; the abstract zero-sum calculation does not
fill either geometric step.

**Next discriminating construction:** On actual smooth
projective higher-rank CM abelian fourfolds, compute
the true Mumford-Tate/Hodge-group weights, identify any
primitive rational (2,2) invariant not generated by
divisor pairs, and test an explicit algebraic
surface/correspondence against its period. One
verified such cycle would add a NEW native GST generator,
rather than rearranging existing correspondences.
The unrestricted target on all X is **unproved**.

## Mathbox 2026-10-17: exact all-X rational-blowup exceptional Hodge reduction

Original universal target unchanged: for EVERY smooth projective complex X,
each p and every rational primitive Hodge (p,p) class alpha, produce
a genuine algebraic codimension-p rational cycle with class alpha.

GEOMETRIC ALL-X CONSTRUCTION: embed arbitrary X as a smooth closed center
of codimension c>=2 in P^N, with N enlarged as necessary. Set
Y=Bl_X(P^N). Then Y is a smooth projective RATIONAL variety, regardless
of the original X geometry. The genuine Chow and Hodge blowup formulas
give the matching decompositions (Tate shifts implicit in Hdg):
  CH^q(Y)_Q = CH^q(P^N)_Q (+) ⊕_{j=1}^{c-1} CH^(q-j)(X)_Q,
  Hdg^q(Y) = Hdg^q(P^N) (+) ⊕_{j=1}^{c-1} Hdg^(q-j)(X)(-j).
Thus each Hodge alpha ∈ Hdg^p(X) occurs faithfully in the first
exceptional Hodge summand of Hdg^(p+1)(Y).

NEW LEAN mathematics in existing GSTUniversalChowRetractToTarget.lean
at commit 7bb7f6c542c4c7aa3a7b4f108f028905a2d7c696:
SchemeExceptionalCenterRetract has the ACTUAL scheme codimensionCycle
maps (center p to blowup p+1 and vice versa), their genuine rational
Betti maps, both cycle-class compatibility squares, a Betti left
inverse and Hodge type preservation. It contains NO requested
target-cycle preimage or assumed Hodge surjectivity.
algebraic_center_iff_exceptional_blowup_class then proves EXACTLY:
  alpha is a native algebraic cycle-class on X
    IFF exceptionalBetti(alpha) is a native algebraic cycle-class on Y.
missing_center_direction_survives_exceptional_birth transports
unrepresented arbitrary-X rational Hodge directions to Y.
hodge_on_arbitrary_center_of_solved_blowup explicitly constructs
the center cycle from a verified blowup source Chow cycle.

KNOWN MATHEMATICAL CONSEQUENCE, not an independently solved conjecture:
rational Hodge conjecture on ALL smooth projective varieties
  IFF rational Hodge conjecture on ALL smooth projective RATIONAL
varieties. The reverse direction follows because every X can be
faithfully embedded into exceptional geometry on rational Y.
Crucially, Y being rational DOES NOT mean its exceptional Hodge
classes are algebraic. Any missing primitive class survives.

Lean gate 38990448496 verifies the new center transfer separately;
check its completed conclusion before declaring GREEN. The actual
scheme blowup, Gysin Chow/Betti and canonical geometric cycle-class
instantiations remain separate external geometry obligations.
Next: derive the first exceptional source directly from the existing
SchemeBlowupGysin packet and verify its native Chow recovery projection;
this will reduce free geometry interfaces and narrow the missing leaf.

FULL UNIVERSAL EXISTENCE STATUS: UNPROVED; the reduction is faithful
but does not independently construct the missing primitive cycles.

### 2026-10-17: exact middle-Hodge reduction on rational stabilized blowups

All-varieties, all-codimension strengthening in EXISTING Lean file
GSTUniversalChowRetractToTarget.lean, commit
047397c6e4ef86f60a7331df0ccdb81156232ed1.

Every smooth projective X of dimension d admits a smooth closed
embedding X->P^N of codimension at least 2, and N can be increased
arbitrarily. Let Y=Bl_X(P^N), a smooth rational projective variety.
An arbitrary rational Hodge class alpha in Hdg^p(X) embeds as
the first exceptional class e(alpha) in Hdg^(p+1)(Y). The exact
native Chow/Betti Gysin forward and backward naturality laws
from SchemeExceptionalCenterRetract give:
  alpha algebraic on X IFF e(alpha) algebraic on Y.

Choose N>=2(p+1), set q=p+1, and r=N-2q>=0.
Let M=Y x P^r. Then M is smooth projective rational and
  dim(M)=N+r=2(q+r).
The stabilized class sigma=e(alpha) x h^r is a rational Hodge
class in the MIDDLE cohomological degree of M.
The projective-bundle formula provides actual Chow cycle maps
z -> pr_Y^* z . h^r, and recovery pr_Y*; their cohomology
comparisons are encoded by SchemeProjectiveMiddleStabilization.
Lean theorem projective_stabilization_hits_middle_degree proves
the integer midpoint formula for EVERY N,q with 2q<=N.
Lean theorem algebraic_iff_projectively_stabilized_class proves
an ACTUAL native cycle class is algebraic exactly if its
stabilized class is algebraic on M. Lean theorem
algebraic_iff_rational_blowup_middle_class composes BOTH two-sided
schematic Chow/Betti recovery maps and proves for EVERY alpha:
  alpha algebraic on X IFF sigma algebraic in middle degree on M.
arbitrary_variety_hodge_from_rational_middle_world constructs
representatives on X using solved middle Hodge classes on M.

MATHEMATICAL IMPLICATION: the rational Hodge conjecture for ALL
smooth projective complex varieties is equivalent to that for
middle Hodge classes on ALL smooth projective RATIONAL varieties
(indeed a cofinal restricted family of stabilized rational blowups).
The equivalence uses the established geometric Chow and blowup
formulas; its scheme/analytic realization from Mathlib blowup
morphisms is still a separate certificate obligation.

This is a faithful reduction, NOT a proof of algebraicity of the
transferred middle Hodge class. The missing primitive rational
Hodge directions survive transport without becoming algebraic.
GitHub Lean run 38990448496 PASSED for the exact exceptional-center
algebraicity equivalence. The subsequent middle-stabilized theorem
was committed at 047397c6e4ef86f60a7331df0ccdb81156232ed1;
run 38990917471 was superseded by a further Lean edit and CANCELLED.
The latest run 38991205384 checks the final explicit native Chow
cycle constructor; its conclusion must be verified separately.


EXPLICIT NATIVE CONSTRUCTION added in commit
a6c16df0f0aece3943ec3a1e84a6ef10d7611830:
nativeCenterFromRationalMiddleCycle E S Z is exactly
E.centerRecoverNative (S.nativeRecover Z), an actual codimension-p
rational Chow cycle on the ORIGINAL arbitrary X whenever Z is an
actual middle-dimensional cycle on the stabilized rational blowup.
The theorem nativeCenterFromRationalMiddleCycle_correct proves
its Betti cycle class equals the requested alpha under the
concrete cohomological class equality for Z. This does NOT
manufacture the missing middle algebraic cycle Z; it certifies
the complete source-to-X Chow recovery without hidden selectors.

## Mathbox 2026-10-17: genuine arbitrary-center Hodge (2,2) births and independent exceptional cycles

Target remains EVERY rational primitive Hodge direction on EVERY
smooth projective complex variety, not merely a transported class.
New existing-file mathematics in GSTUniversalChowRetractToTarget.lean:

1. HodgeAtWeight V H p is the exact given-weight true scheme-cycle
   surjectivity Hdg^p(V) <= range(cycleClass_V^p).
2. hodge_at_fixed_weight_of_geometric_birth constructs an ACTUAL
   codimension-p target Chow cycle from native source cycles at
   ONLY the codimensions actually used by the Gysin splitting;
   previous construction assumed FULL all-weight Hodge algebraicity
   for every independent source scheme, unnecessarily.
3. geometric_blowup_from_strictly_lower_center_weights proves
   that Hdg^p blowup classes are algebraic whenever Hdg^p base
   classes and center Hdg^q for q<p are algebraic. This uses
   the actual blowup source weights p-(j+1), j>=0.
4. geometric_blowup_codimension_two_from_center_divisors proves
   every rational (2,2) class on a genuine smooth blowup is
   algebraic assuming only source base Hdg^2 plus CENTER Hdg^0
   and Hdg^1. The latter follow from the fundamental class
   and Lefschetz (1,1) on every smooth projective center.
   There is NO assumption about Hdg^2, Hdg^3 or any higher
   primitive class of the center.
5. SchemeTypedGSTCodimensionTwoBlowupTower allows any finite
   sequence of smooth blowups, with smooth centers of ARBITRARY
   dimension and any Hodge-theoretic complexity, and theorem
   unrestricted_center_blowup_tower_hodge_two constructs
   genuine native rational codimension-2 representatives
   at every born world, by induction over tower depth.

On a concrete Y=Bl_X(P^N) with smooth X ANY dimension and center
codimension c>=3, the actual Chow decomposition gives
   CH^2(Y)_Q = CH^2(P^N)_Q (+) CH^1(X)_Q (+) CH^0(X)_Q.
The rational Hodge cohomology splitting is identical in type.
Every direct summand is algebraic: ambient linear planes,
center divisors, and center components. In particular the
first UNKNOWN primitive Hodge obstruction of X in Hdg^2(X)
appears only in Hdg^3(Y), not in Hdg^2(Y). A rational ambient
host does not automatically solve Hodge in higher weights.

6. exceptional_hodge_embedding_injective proves the true
   exceptional class map is injective using its geometric
   Betti recovery left inverse.
7. exceptional_native_cycle_new_beyond_ambient starts from a
   specific nonzero genuine native cycle Z on arbitrary X and
   constructs its actual exceptional Gysin cycle on Y. The
   output is proved OUTSIDE THE ENTIRE AMBIENT Betti image
   when the geometric recovery kills that ambient summand.
   Thus this is a genuinely NEW algebraic source direction,
   not a reversible recoordination of old projective cycles.
   Projective positive-dimensional X has an ample divisor
   with nonzero Betti class, supplying the source for p=1.

LEAN EVIDENCE: codimension-two tower commit
8d6fb63af9e68b4a2d68f7eafd5a092b01e19236; independent
exceptional native-cycle commit
5a02ef2304477d84eb5f0806d3f4cee6b49fcf34.
Combined all-center Hodge and exceptional-native geometry gate
38992433801 COMPLETED SUCCESSFULLY after the Lean documentation
placement repair at commit f8d1fb1adc903af19f61d12afcf198b7db492561.
Both the unrestricted-center codim-two blowup tower and the new
ambient-independent exceptional native cycle are KERNEL-VERIFIED.
The older all-varieties Chow middle-recovery run 38991205384
has a confirmed SUCCESS conclusion.

IMPORTANT BOUNDARY: the Lean scheme-typed Gysin packet still
requires independent construction of the blowup, its true
native Chow/Betti Gysin maps, and cycle-class comparison,
and HodgeBigradedBettiData.cycleClass is a supplied map.
The known true geometric formulas justify a mathematical
instantiation, but the current file does not construct
their analytic or scheme-level Mathlib realizations.
These upgrades DO NOT yet construct a representative for
an arbitrary Hdg^p(X) primitive class when p>=2.

### 2026-10-17: all-center exceptional nonzero primitive codimension-two cycles

NEW substantive GST GEOMETRIC CYCLE CONSTRUCTION beyond conditional
full Hodge transfers: For ANY positive-dimensional smooth projective
complex center X, embed X in P^N with N large enough that
c=codim(X,P^N)>=3 and N>=4, and let Y=Bl_X(P^N).
Y is a smooth projective RATIONAL variety.

Let A be the ambient hyperplane class on Y and E the exceptional
divisor. The actual Chow blowup formula in codimension two is
  CH^2(Y)_Q= CH^2(P^N)_Q + CH^1(X)_Q + CH^0(X)_Q.
The three classes A^2, A*E, E^2 have independent rational
Betti cohomology sectors because the first exceptional
cohomology is H^2(X), the second exceptional H^0(X), and
the ambient sector is H^4(P^N). Here A*E is the actual
exceptional Gysin image of the ample divisor h=A|X, and
cl(h) is nonzero because dim(X)>=1 and h is ample.

Choose a rational ample polarization L=A-t*E with t!=0.
The image under multiplication by L of the divisor class
x*A+y*E has coordinates in the (A²,A*E,E²) sector
  (x, y-t*x, -t*y).
The genuinely algebraic class A*E has coordinates (0,1,0).
No choice of x,y can produce those three coordinates:
x=0 and -t*y=0 force y=0, contradicting the middle 1.
Equivalently, Wolfram evaluated the exact determinant of
columns (1,-t,0), (0,1,-t), (0,1,0) as t, nonzero.

Therefore A*E lies OUTSIDE the entire Lefschetz divisor cup
image, independently of the dimension or the primitive
Hodge algebraicity of the center X. GST's already-verified
codim-two native primitive projector then constructs
an ACTUAL rational algebraic codimension-two cycle W on Y
whose Hodge class is both nonzero and primitive.
One may write W = A*E - L*D, where D is a rational
divisor whose class is selected by the inverse Hard
Lefschetz pairing. Lefschetz (1,1) makes D algebraic.

FORMAL LEAN: In existing GSTPrimitiveTransverseCycleExtraction.lean
new GenuineBlowupThreeSectorPrimitivePacket encodes the
actual native exceptional cycle, three independently
geometric cohomological readouts, and the polarizing
cup-product coordinate law. The theorem
blowup_exceptional_cycle_transverse_to_divisor_cup proves
the exact three-coordinate obstruction by rational algebra.
actual_nonzero_primitive_cycle_of_three_sector_blowup
composes that transverse source cycle with GST's genuine
native primitive correction. This constructs nonzero
primitive classes on the ACTUAL smooth-projective scheme
carrier rather than mere abstract torus charge tokens.
Dedicated Lean CI 38992782278 PASSED with no sorryAx.
The independent whole-file Chow/Gysin CI 38992837014 also PASSED.

IMPORTANT: The three-sector packet still needs genuine
Mathlib scheme-level blowup cohomology/Gysin realization;
its abstract record alone does not certify a given Y is
a blowup nor supply all its actual coordinate maps.
The standard geometric blowup formulas establish the
mathematical instantiation for smooth projective centers.
This construction gives a NEW nonzero primitive cycle on
the host Y for every positive-dimensional center X,
NOT algebraic representatives of EVERY prescribed
primitive Hodge class on that arbitrary center X.

Further native exceptional independence is proved in
GSTUniversalChowRetractToTarget.lean:
exceptional_hodge_embedding_injective and
exceptional_native_cycle_new_beyond_ambient construct
center-sourced algebraic cycles on the born world
and prove they cannot lie in the ambient Betti image
when true exceptional recovery kills that ambient sector.
The fixed-weight and unrestricted-center codim-two
tower declarations in the same file are checked by
CI 38992837014; check its exact verdict before marking
the combined file green.


## 2026-10-17 Mathbox: full-rank Picard primitive birth and arbitrary-Hodge-defect preservation

**Research goal (unchanged).** For every smooth projective complex
variety X, every p, and every rational Hodge (p,p) class alpha,
produce an actual codimension-p rational algebraic cycle Z with
the CANONICAL geometric class cl(Z)=alpha. The unrestricted
primitive case remains an unsolved construction obligation.
The results below are proved consequences of independent
geometric certificates, not a replacement of this target.

### The positive all-X center construction: Picard rank becomes primitive rank

Let X be ANY connected, smooth, positive-dimensional projective
complex variety. Embed X smoothly into P^N with N>=4 and
codimension c>=3 (a larger projective embedding can always
arrange this). Form the smooth projective RATIONAL blowup
    Y = Bl_X(P^N).
Write A for the pullback of the ambient hyperplane divisor
and E for the actual exceptional divisor.
Choose a rational polarization L=A-tE with t>0 sufficiently small.

The TRUE rational Chow and rational Hodge blowup decompositions
at codimensions 1 and 2 are:
  Hdg^1(Y,Q) = Q[A] (+) Q[E],
  Hdg^2(Y,Q) = Q[A²] (+) Hdg^1(X,Q)(-1) (+) Q[exceptional²].
Here Hdg^1(X,Q)=NS(X)_Q by Lefschetz (1,1). Let
rho=rank_Q NS(X)_Q. Thus
  dim Hdg^1(Y,Q)=2,  dim Hdg^2(Y,Q)=rho+2.

Let D∈NS(X)_Q be a genuine divisor class. Its actual Chow
Gysin pushforward from the exceptional projective bundle
E -> X defines a genuine codimension-two cycle
    Z_D = j_*(pi^*D) ∈ CH²(Y)_Q.
Its rational Betti class has ambient coordinate zero,
first-exceptional coordinate D and second-exceptional
coordinate zero. The linear native map D↦Z_D has EXACT
first-exceptional cohomology readout D.

For beta=x A+y E∈Hdg^1(Y), multiplication by L has:
  ambient coordinate x,
  center first-exceptional coordinate an explicit linear
    combination (y-t*x)h_X + y*k_X,
  second-exceptional coordinate -t*y.
The actual scalar field k_X is a fixed Chern/polarization
dependent rational divisor class; its precise value is
irrelevant to injectivity. If cl(Z_D)=L cup beta, the
ambient and second-exceptional coordinates force
  x=0 and t*y=0 ⇒ y=0,
and the first-exceptional coordinate forces D=0.
Therefore the whole linear subspace
    cl(Z_D),  D∈NS(X)_Q
meets L cup Hdg^1(Y,Q) ONLY in zero. This holds at
ARBITRARY Picard rank rho: not merely one ample divisor.

By rational Hard Lefschetz and Lefschetz (1,1), the canonical
primitive projection on Hdg²(Y,Q) is the rational linear map
    Pr(alpha) = alpha -
      L cup (L^(N-2)|Hdg¹(Y))^-1 (L^(N-3) cup alpha).
Every correction term is the class of an ACTUAL algebraic
divisor intersected with the actual hyperplane/polarization
cycle. Hence Pr(cl(Z_D)) is represented by the ACTUAL native
rational Chow cycle
    W_D = Z_D - L cup D_corr(D) ∈ CH²(Y)_Q.
Hard Lefschetz makes the cohomological correction UNIQUE,
so Pr is LINEAR despite possible nonlinear/noncomputable
choices of individual Chow divisor representatives.
The preceding trivial-intersection calculation makes
    NS(X)_Q -> Hdg²_prim(Y,Q), D↦Pr(cl(Z_D))
a rational LINEAR INJECTION with GENUINE native cycle
representatives for its entire image.

Furthermore rational Hard Lefschetz shows
L cup : Hdg¹(Y,Q) -> Hdg²(Y,Q) is injective
for dim(Y)=N>=4. The primitive decomposition gives
    dim_Q Hdg²_prim(Y,Q)
       = dim_Q Hdg²(Y,Q) - dim_Q Hdg¹(Y,Q)
       = (rho+2)-2 = rho.
Thus the constructed injection is in fact a VECTOR-SPACE
ISOMORPHISM ON THIS PARTICULAR RATIONAL BLOWUP HOST:
the full primitive rational Hodge codimension-two space
is algebraic, and generated by actual corrected center
divisor classes. The dimension equality is a mathematical
consequence of the standard genuine Chow/Hodge blowup and
Hard Lefschetz formulas; the current Lean module proves
the constituent linear embedding with certified geometry
rather than independently constructing all analytic
scheme-level blowup certificates or formalizing this
dimension count.

### Executable GST formalization (existing Lean module)

File GSTPrimitiveTransverseCycleExtraction.lean now contains:
- GenuineBlowupPicardPrimitivePacket (all-rank actual native
  center divisor cycles and independent three-sector readouts)
- exceptional_picard_class_in_Lefschetz_forces_zero (exact
  all-rank geometric transversality calculation)
- nonzero_primitive_cycle_of_any_center_divisor
- primitive_center_divisor_directions_are_distinct
- primitive_hodge_remainder_add and ..._smul
- primitiveHodgeProjectionLinear
- picardToNativePrimitiveLinear_injective
- picardToNativePrimitiveKernelLinear and ..._injective
- every_picard_primitive_vector_has_native_chow_cycle
These declarations do NOT use sorryAx or custom axioms.
The first full-rank/linearity gate 38994779386 SUCCESS;
the primitive-kernel gate 38994999959 SUCCESS;
the final explicit Chow-witness gate 38995216976 PASSED,
verifying every_picard_primitive_vector_has_native_chow_cycle
at commit 8e8ad2248bca4e07f2445ef9f006dba8e5d0fbac. All three
new primitive-cycle Lean checkpoints are GREEN.
The symbolic full-coordinate independence determinant
for rho=1,...,5 was checked using Wolfram over Q[t] and equals
(-1)^(rho+1)*t. The Lean argument itself has no rank cutoff.

### Universal defect channel survives both GST births

The existing GSTUniversalChowRetractToTarget.lean now defines
NativeDefectIndependent for a finite family alpha_i of classes
on ANY smooth projective X: if a rational combination of the
alpha_i is in the image of the original native codimension-p
cycleClass map, all its coefficients must be zero.

Two new LEAN theorems:
  exceptional_blowup_preserves_native_defect_independence
  middle_rational_world_preserves_native_defect_independence
transport EVERY such independent defect family through
the first exceptional class embedding and through further
projective middle stabilization. They preserve *all*
rational linear relations modulo genuine cycle-class images,
not just nonalgebraicity of a single class.
GitHub kernel gate 38994918540 PASSED.

This proves a sharp limitation on how the newly created
primitive rank can address the ORIGINAL universal target.
The new rho-dimensional primitive sector of Y comes from
Hdg^1(X), which is already algebraic by Lefschetz (1,1).
An unknown primitive alpha∈Hdg^p(X), p>=2, appears instead
at exceptional codimension p+1 in Y. Its entire deficiency
modulo native algebraic cycles persists by the defect theorem.
So the new primitive cycles on Y do NOT constitute algebraic
representatives of arbitrary unknown alpha on the ORIGINAL X.

### Exact remaining original-theorem obligation

We still need a genuinely new geometric construction which, for
EVERY X,p and every rational primitive Hodge alpha, produces an
ACTUAL codimension-p cycle with canonical analytic cycle class
alpha. Options such as geometric correspondences, GST world
births, N cohomology, CM/NM, generalized cosmology, tautology,
Lefschetz and blowup operations must supply an independently
proved image-surjectivity mechanism; composition, coordinate
changes, and rationality of a blowup are mathematically
insufficient on their own. Also the GST HodgeBigradedBettiData
structure currently allows a freely SUPPLIED cycleClass field;
the proof must connect it to the canonical geometric map.
No claim of the unrestricted universal Hodge conjecture is
supported by the existing Lean compilers.


## 2026-10-17 Mathbox: pinned all-varieties target and finite-degree positive construction

**Fixed exact target:** for EVERY smooth projective complex X, EVERY p,
EVERY rational primitive (p,p) Hodge class alpha in H^{2p}(X,Q),
produce an actual rational codimension-p algebraic cycle Z whose
CANONICAL Betti cycle class is alpha. Assumed source algebraicity,
abstract Hodge operators, chosen target cycle, a supplied free
cycleClass map, or a proof of a mere equivalent reduction are NOT a
discharge of the target.

**A positive non-universal route was executed.**
Existing GSTUniversalChowRetractToTarget.lean gains
SchemeFiniteDominantTwoTransfer, constructNative,
constructNative_correct, and
hodge_two_of_resolved_projective_domination. Let f:Y->X be an actual
proper generically finite morphism of nonzero degree d, with Y
obtained by a finite resolution tower of smooth blowups of a
projective source. For alpha in Hdg^2(X,Q), take the REAL Chow
cycle Z_Y with class f^*(alpha) supplied by the verified source
blowup theorem (the exceptional centers need only their known
Hodge degrees zero and one). Then the explicit target cycle is
  Z_X = d^{-1} f_*(Z_Y) ∈ CH^2(X)_Q.
Its class is d^{-1} f_*f^*(alpha)=alpha. In geometry, this
applies to EVERY smooth projective UNIRATIONAL target X in
EVERY dimension, after resolution of the dominant rational map
from projective space, the standard projective-space Hodge basis,
the trace degree identity, and Chow/Betti compatibility.

**Scope firewall:** this is NOT a universal all-X result.
For instance a positive-dimensional abelian variety is not
unirational; there is no generically finite rational
parametrization by P^n. The universal target therefore still
requires independent cycle construction in arbitrary primitive
middle Hodge directions not dominated by a known cycle-complete
source. The canonical analytic cycleClass semantics must still
be constructed/identified instead of relying solely on the
free HodgeBigradedBettiData.cycleClass field.

**Verification:** initial GitHub run 38996949600 failed on a local
Lean let-binding normalization in the explicit target-cycle term,
not a mathematical counterexample. The fix at
1cafea733a1a779e20498ba5d0ae641a90049090 is running as
GitHub run 38997316168; verify its terminal conclusion before
calling the new theorem kernel-certified.

**Next original-theorem attack:** independent algebraic
representatives of trace-zero primitive rational Hodge
directions of arbitrary non-unirational varieties, with a
proof that their classes span the TRUE Hodge subspace.
No existing GST matrix-unit/CM/NM/cosmology theorem establishes
this universal geometric construction yet.


## 2026-10-17 Mathbox: all-X finite projection trace-zero target, not just unirational

UNALTERED ORIGINAL TARGET: for every smooth projective complex X,
every codimension p, every rational primitive Hodge class alpha,
construct an ACTUAL rational Chow/algebraic codimension-p cycle
whose CANONICAL analytic cycle class equals alpha.

NEW ALL-X GEOMETRIC INPUT: for any connected pure-dimensional
smooth projective complex X of dimension d, generic linear
projection after projective embedding gives a finite surjective
morphism g:X->P^d of nonzero degree e. This exists EVEN when X is
of general type, abelian, or non-unirational: crucially the map
is X->P^d, not a rational parametrization P^d->X.

Since Hdg^p(P^d,Q) is generated by the actual linear intersection
cycle h^p, the trace g_*(alpha) is algebraically represented.
Pull back and divide by degree to CONSTRUCT a genuine algebraic
codimension-p cycle Zambient(alpha) on the ORIGINAL X, with
  cl(Zambient(alpha)) = e^{-1} g^* g_* alpha.
The actual leftover on X
  r(alpha)=alpha-cl(Zambient(alpha))
is a rational (p,p) Hodge class and satisfies
  g_*(r(alpha))=0
EXACTLY. These facts are all-rank, all-codimension, on arbitrary
X and require no guessed algebraic representative of alpha.
What remains is to CONSTRUCT a genuine codimension-p cycle for
each rational (p,p) class in ker(g_*), in particular the
primitive trace-zero classes.

Code at b3041ab995fc8f7fd8cf64d43bb82cd7defe64e9:
GSTActualXHodgeResidualProjection.lean, structure
ActualXFiniteProjectiveTrace, definitions ambientNativeCycle,
traceZeroResidual, and theorems traceZeroResidual_push_zero
and traceZeroResidual_is_hodge. Dedicated kernel CI
38997776672 PASSED.

The exact target equivalence was subsequently written at commit
dcaba90de3224a0bb3b737be771f66a0714e3eeb:
ActualXFiniteProjectiveTrace.full_hodge_iff_trace_zero_hodge
plus explicit constructFromTraceZero native Chow sum and its
cycle-class correctness. It proves ALL Hodge classes are
algebraic on X iff all trace-zero Hodge classes on X are
algebraic, by using the already constructed ambient Chow
cycle. The second kernel run 38998155909 PASSED. The exact all-X
Hodge / trace-zero Hodge equivalence and the explicit Chow
assembly from a trace-zero representative are kernel-verified.

FIRST POSITIVE CONSTRUCTION on genuinely dominated targets:
At fixed codimension 2 a proper generically finite morphism
f:Y->X from a resolved projective blowup tower gives the explicit
cycle d^{-1} f_*(Z_Y), with cl(Z_Y)=f^*(alpha).
This covers the smooth projective UNIRATIONAL subclass.
Existing-file theorem
hodge_two_of_resolved_projective_domination at commit
1cafea733a1a779e20498ba5d0ae641a90049090,
GitHub Lean CI 38997316168 GREEN (prior run 38996949600
failed on a corrected Lean normalization detail).

DECISIVE REMAINING ALL-X OBSTRUCTION: the rational Hodge
subspace ker(g_*) need not vanish. No current GST cohomology,
cosmology, CM/NM, finite correspondence matrix-unit,
positive residual-energy, or formal tautology supplies a
geometric algebraic representative for EVERY primitive
trace-zero class on arbitrary X. An endomorphism on Hodge
cohomology is not a Chow correspondence unless independently
realized; projection of an abstract Hodge basis is not an
algebraic-cycle construction. The Mathlib Stage-2G Hodge
cycleClass is still a supplied map, not an automatically
constructed canonical analytic map.

NEXT PREFERRED RESEARCH ROUTE: find an independent scheme
construction (e.g. cycles on non-unirational finite covers of
projective space, with geometric Galois/ramification/monodromy
sources) proving full rank on the TRUE rational Hodge trace-zero
subspace. Prove canonical geometric cycle-class compatibility
and test nonzero trace-zero primitive examples before claiming
a universal proof. No claim that this leaf is already solved.


**All-X actual trace-zero native Chow GENERATOR.**
In existing GSTActualXHodgeResidualProjection.lean, the new
ActualXFiniteProjectiveNativeTrace extends the finite projection
with genuine Chow pushforward and the geometric degree formula
g_*g^*=e id on rational Chow cycles, plus the exact Chow/Betti
cycle-class compatibility square.
For ANY actual native codimension-p algebraic cycle Z on X:
  Z^0 := Z - e^{-1} g^*(g_*Z) ∈ CH^p(X)_Q.
Theorems traceZeroNative_push_zero and
traceZeroNative_cycleClass establish:
  g_*Z^0 = 0  in rational native Chow, AND
  cl(Z^0)=cl(Z)-e^{-1}g^*g_*cl(Z).
A further theorem traceZeroNative_nonzero_of_new_class shows
cl(Z^0) != 0 whenever cl(Z) lies OUTSIDE
range(g^*:H^{2p}(P^d,Q)->H^{2p}(X,Q)).
Thus this constructs genuinely new, nonzero, native
trace-zero algebraic directions on arbitrary varieties
from independently known nonambient algebraic cycles,
without choosing Hodge-cycle preimages.
Commit dcc840739a9381a8c1aa26f3dd3f4364b809390f;
CI run 38998529171 must pass before this latest proof is
marked Lean-certified.
The hard universal step is to establish that these and
additional NEW geometric native trace-zero cycles span
every trace-zero rational primitive (p,p) class on every X.
No such spanning law is assumed or claimed.


## 2026-10-17 Mathbox: exact Chow trace kernel and fused primitive cycle birth

**Authoritative universal target remains unchanged:** For EVERY smooth
projective complex variety X and EVERY rational primitive (p,p) Hodge
class alpha, construct an ACTUAL rational codimension-p algebraic
cycle with its CANONICAL Betti class exactly alpha. All current
formalizations operate relative to HodgeBigradedBettiData, whose
cycleClass field is still supplied; identifying this with the
canonical geometric cycle class is another required foundation step.

The finite-projective trace operation is now formalized as an
ACTUAL rational-linear native algebraic cycle projector on X:
  Pi_native = id - (degree g)^(-1) g^* g_*
It satisfies:
  Pi_native^2 = Pi_native;
  im(Pi_native) = ker(g_*:codimensionCycles X p -> codimensionCycles P p);
  (g_* Z=0) => Pi_native Z=Z;
  g_* Pi_native Z=0;
  cl(Pi_native Z) = cl(Z) - (degree g)^(-1)g^*g_*cl(Z).
For ANY trace-zero rational Hodge alpha already represented
by some genuine native Z, the specific class Pi_native Z gives
a genuine representative with ZERO Chow pushforward.
Thus there are no hidden problems lifting a KNOWN algebraic
cohomological trace-zero class to a trace-zero native cycle.

Existing file: GSTActualXHodgeResidualProjection.lean; new theorems
range_projector_eq_kernel_push, traceZeroNative_idempotent,
exact_native_trace_zero_witness, and
hodge_trace_zero_iff_native_kernel.
GitHub Lean kernel run 38999124663 PASSED at commit
677ceb14bd03f676fca0f2e31626d1aaf989c20d.

**Next fused all-X primitive native construction**, committed
at 145a94111928f2af453b30c611cc5f02999c9d4f:
1. GeometricHigherLefschetzData on the ORIGINAL X defines true
   p=2 primitiveTest on the rational Hodge fiber. Hard Lefschetz
   and Lefschetz (1,1) give a NATIVE algebraic primitive correction
   for any already known non-Lefschetz codimension-two cycle Z.
2. For a genuine finite projective projection g:X->P^d with
   dim(X)=d>=4, projection formula gives
     integral_X alpha cup h^(d-2) =
     integral_P (g_*alpha) cup H^(d-2).
   The primitive condition is h^(d-3)alpha=0; multiplying by h
   makes the left side ZERO. H^4(P^d,Q) is rank-one, detected by
   the projective period. Thus EVERY (2,2) primitive alpha on X
   has g_*alpha=0.
3. ActualXPrimitiveProjectiveTraceComparison encodes the true
   projection formula, true primitive integration and rank-one
   projective period map; its derived theorem primitive_push_zero
   proves the trace vanishing from these geometric certificates.
4. Start with any genuine algebraic Z with class outside the
   Lefschetz Hdg^1(X) cup image. The established GST primitive
   correction builds a genuine algebraic W0 with
   primitiveTest(cl(W0))=0 and cl(W0)!=0. Project W0 using the
   native Chow trace projector. Since g_*cl(W0)=0, its Betti
   class is UNCHANGED while the true Chow pushforward vanishes.
   Output W therefore satisfies SIMULTANEOUSLY:
     g_*W=0 in native algebraic cycles;
     cl(W)!=0;
     primitiveTest(cl(W))=0.
   This is an actual geometric-cycle creation mechanism on the
   ORIGINAL X, including non-unirational X, when the known
   non-Lefschetz source and true geometric certificates are supplied.

Run 38999466852 must report SUCCESS before this fused theorem
is considered kernel-verified. It does NOT assert that a source
Z outside the divisor-Lefschetz image must exist whenever the
TRUE primitive Hodge space is nonzero. That unrestricted source
generation is precisely the original Hodge existence challenge,
not a conclusion from a coordinate argument.


## 2026-10-17 Mathbox: nonambient Picard classes give exact Chow trace-zero rank

Original theorem contract unchanged: every smooth projective complex X,
every p, every rational primitive Hodge alpha, construct a rational
codimension-p algebraic cycle with genuine canonical class alpha.

**New actual-X geometric construction (not a primitive existence theorem).**
Let X be connected smooth projective of dimension d>=3 and
g:X->P^d a finite surjective generic linear projection of degree e>0.
Set h=g^*c1(O(1)), an ample divisor class. Let NS(X)_Q denote
the genuine rational algebraic divisor class space (Picard rank rho).
For every native divisor D define the native codimension-two cycle
  W_D = h*D - e^(-1) g^*(g_*(h*D)).
This is REAL algebraic Chow geometry on X. The exact Chow
push-pull formula gives g_*W_D=0 in CH^2(P^d)_Q. Its class is
  cl(W_D) = h cup cl(D) - e^(-1)g^*g_*(h cup cl(D)).
Because H^4(P^d,Q)=Q H^2 for d>=2, the second term is
some rational scalar times h^2. If cl(W_D)=0,
  h cup (cl(D)-c*h)=0.
Hard Lefschetz for d>=3 makes cup h:H^2(X,Q)->H^4(X,Q)
INJECTIVE: if h*x=0, then h^(d-2)*x=0 and Hard Lefschetz
H^2 -> H^(2d-2) is an isomorphism. Hence cl(D)=c*h.

Conversely cl(D)=c*h implies cl(W_D)=0 by the degree
push-pull formula g_*g^*=e on projective cohomology.
Therefore the induced rational linear map
  NS(X)_Q / (Q*h)
     -> Hdg^2(X,Q) cap ker(g_*)
is INJECTIVE and its entire image is algebraic.
Its image has dimension rho(X)-1, in EVERY ambient
dimension d>=3. When rho>1, this produces genuinely
NONZERO independent trace-zero rational algebraic cycle
classes on non-unirational X as well. No codimension-two
Hodge conjecture or primitive representative is assumed.

The existing Lean file GSTActualXHodgeResidualProjection.lean
now defines the native linear construction
ActualXFiniteProjectiveNativeTrace.picardTraceZeroLinear
and proves existence/nonvanishing for each divisor class
outside the hyperplane line via
nonambient_divisor_generates_nonzero_trace_zero_chow_two
(commit 4fedf4cec9915ca91f12948db6e7e6181c6aa70e).
The full rank rho-1 is a mathematical corollary of
Hard Lefschetz plus the true finite-projection formula,
NOT YET a kernel-checked FiniteDimensional rank theorem.

**Critical non-circularity warning:**
classes W_D built from h*D lie in the LEFSCHETZ
divisor-cup image. Their primitive projections can be ZERO.
In fact on P^2 x P^2 with h=a+b, the trace-zero
class a^2-b^2=h*(a-b) is NOT primitive:
h*(a^2-b^2)=a^2*b-a*b^2 != 0.
The distinct class a^2-a*b+b^2 is primitive and
trace-zero. Wolfram exact arithmetic verified these
cup and trace calculations. Hence divisor-born trace-zero
classes cannot themselves discharge arbitrary primitive
Hodge existence. The new primitive+trace-zero Lean route
must start with independently produced non-Lefschetz
native algebraic cycles, not simply divisor products.

**Cross-codimension formal target:**
New ActualXAllCodimensionPrimitiveTraceComparison
and theorems primitive_algebraic_class_has_true_chow_trace_zero_cycle
and all_primitive_hodge_iff_native_trace_kernel_spans
were committed at f87eaf5ee54577351515841b4a1a9943d7b5e30f.
They explicitly require the true primitive-vs-projective
trace projection formula and the *genuine* Chow/Betti maps;
no target algebraicity is assumed. Check latest GitHub
Actions before declaring kernel verification.
The unrestricted all-varieties all-Hodge target is NOT closed.


### Uniform all-codimension extension: rho(X)-1 trace-zero native classes

For any connected smooth projective complex d-fold X, any
1<=p<=d-1, any finite linear projection g:X->P^d of
nonzero degree e, and h=g^*H, define on rational
divisor classes D the actual codimension-p cycle
  W_{p,D}:= h^(p-1)*D - e^(-1)g^*g_*(h^(p-1)*D).
The Chow projection formula proves g_*W_{p,D}=0.
The cycle class of W_{p,D} lies in the rational
(p,p) trace-zero Hodge subspace on X.

Claim with complete algebraic-geometric derivation:
the kernel of D↦cl(W_{p,D}) on NS(X)_Q is exactly Q*h.
The forward implication follows since
H^{2p}(P^d,Q) is one-dimensional, so if W class
is zero, h^(p-1)*(D-c*h)=0 for some c∈Q.
Multiplying by h^(d-p-1) (a NONNEGATIVE exponent
since p<=d-1) gives h^(d-2)*(D-c*h)=0.
Hard Lefschetz L^(d-2):H²(X,Q)->H^(2d-2)(X,Q)
is injective, hence D=c*h. Conversely if D=c*h,
the degree trace identity g_*g^*=e implies W=0
already in the rational Chow group.

Consequently for EVERY 1<=p<=d-1 there is a
rational algebraic trace-zero Hodge subspace of
dimension EXACTLY rho(X)-1 generated by these
explicit known Chow cycles on the ORIGINAL X,
including non-unirational X. The p=2 positive
direction has a specific scheme-typed Lean theorem
committed as
nonambient_divisor_generates_nonzero_trace_zero_chow_two.
The ALL-p statement above is mathematically derived
using classical cycle and Hard Lefschetz geometry;
a general-p native hyperplane-power Lean comparison
and a kernel-checked rank theorem have NOT been
added. Do not confuse these decomposable h^(p-1)D
classes with primitive classes: their primitive
projections can vanish. The unrestricted primitive
Hodge class existence target remains unproved.

**Exact finite sanity audit: 125 truncated projective-product rings.** In the independent exact rational calculation
on X=P^m x P^n, m,n∈{1,2,3,4,5}, every
p=1,...,m+n-1 was tested (total 125 cases). The
truncated cohomology ring Q[a,b]/(a^(m+1),b^(n+1))
and hyperplane class h=a+b were used to form the exact
trace-zero projector
  h^(p-1) D - (integral_X h^(p-1)D h^(d-p) /
                 integral_X h^d) h^p
for D=a,b. The rank was 1 in all 125 cases as predicted
by rho=2. For m=n=2,p=2 the image columns are
(-1/2,0,1/2) and (1/2,0,-1/2) in basis (a²,ab,b²).
No floating point or sample-based universal inference is used.
The full arbitrary-X proof is Hard Lefschetz, not this finite sweep.

## 2026-10-17: primitive rank of the finite-projective trace construction

**Original goal remains unproved:** for every smooth projective complex
variety X and every rational primitive Hodge direction, construct enough
independent non-Lefschetz algebraic cycles to span the primitive Hodge
space, and identify their classes through the canonical geometric
cycle-class map. No conditional landing theorem counts as this result.

Base checkpoint: branch `mathbox/residual-zero-direct-audit-20261015`,
commit `5b76211e394944deba22bab22bccf60e2b2dcff2`.
The branch was identified using all remote branch-head commit dates and
the recent commit/workflow history; the default branch was older.
The complete 865-file tree was indexed (690 Lean files). The central
proof paths were read in detail; this is not a claim that every proof
body in the repository was fully reviewed.

### New exact GST result, in the existing Lean module

Let Q_native(Z)=Z-e^(-1)g^*g_*Z be the existing trace projector,
and let pi be the existing codimension-two primitive Hodge projector.
Under the existing geometric comparison data:

    pi(cl(Q_native(Z))) = pi(cl(Z))       for EVERY native cycle Z.

Proof: the projective degree-four pullback image consists of multiples
of h^2. Thus cl(Q_native(Z))=cl(Z)-e^(-1)c(h cup h) for some c in Q.
The existing GST primitive projector is rational-linear and kills
the entire h-cup-divisor image. Applying it proves the equality.
No representative of an unknown primitive Hodge class is assumed.

For any indexed source family, its primitive classes are therefore
pointwise unchanged by Q_native. Their span and independence relations
are unchanged as well; taking more trace-normalized sources cannot
increase their primitive rank.

Apply this to Z=h*D. Since pi(cl(h*D))=0 for EVERY divisor D:

    pi(cl(picardTraceZeroLinear(D))) = 0.

This sharpens the earlier wording "can vanish": under these
comparison data, the primitive projection of every cycle in this
specific Picard trace construction ALWAYS vanishes. Its nonzero
trace-zero rank rho-1 therefore contributes primitive rank ZERO.
This does not concern arbitrary products of divisor classes;
it concerns the specific h*D constructor already defined here.

Existing file `GSTActualXHodgeResidualProjection.lean` was extended with:

* `traceZeroNative_preserves_primitive_projection`;
* `picardTraceZero_has_zero_primitive_projection`.

Proof commit: `549bfb0c82ff9932e0281bca5b7d11ff31401379`.
GitHub Actions run: `39007462036`, SUCCESS on the exact proof commit
above (completed 2026-10-17 06:08 UTC). The kernel compilation and
the workflow's `sorryAx` scan passed. Both new axiom receipts are
exactly `[propext, Classical.choice, Quot.sound]`; the build log has
zero `sorryAx` occurrences. The downloaded artifact ZIP matches
SHA256 `e4a7ad5c926e7b3b94d8f588cbd8d990fbf2212a44f6096f97c5ed873d9fc6dd`.
The changed declarations contain no proof escape.
These are route-discrimination theorems, not the requested universal
geometric cycle construction.

### Current route checks against the code and prior research records

The trace-projector proof is new in this checkpoint. The other route
entries reconstruct existing arguments and their first unresolved
implications; their historical proof campaigns were not rerun here.

| Route | Established information | Remaining geometric input |
|---|---|---|
| Finite-projective trace and Picard sources | Trace correction preserves primitive projection; the h*D source family has primitive rank zero. | Independently construct source cycles outside the full Lefschetz divisor image, with enough independent primitive classes. |
| GST correspondence / CM-NM operators | The existing native naturality laws preserve the actual algebraic class image; nonzero commutators can give a rank gain, but the recorded four-coordinate model prevents inferring arbitrary full rank. | A genuinely realized geometric operator or source family with proved spanning on every original X. |
| Exceptional blowup sources and product stabilization | The existing three-sector readouts give transverse algebraic classes on the auxiliary host. The true center-recovery theorem also preserves any hypothetical missing-center defect. | Geometric representatives in the marked arbitrary-X sector; auxiliary-host rank does not itself supply them. |
| Fixed integral homology and calibrated currents | The recorded GST surgery examples preserve integer homology in their stated product models; pointwise complex-tangent projection fails closedness. | A fixed-class, integral, boundary-preserving geometric replacement with absolute calibration defect tending to zero for every X. |

The final three routes remain open at their stated geometric inputs;
this checkpoint does not assert that the full mechanisms are exhausted.
The first route cannot create primitive rank from its h*D source family.
Any continuation must change that source family, not repeat its trace
normalization or increase the number of Picard directions.

### Canonical geometric class certification

`HodgeBigradedBettiData.cycleClass` is still a supplied linear-map field.
The analytification topology and Hodge bigrading are also supplied data;
they must be instantiated for the actual variety in a complete landing.
`GeometricCycleClassSpine` alone does not identify it canonically: the
existing `zeroCycleClassSpine` theorem supplies a formal countermodel
to that inference. This is not a geometric Hodge counterexample.

`GSTClassicalHodgeGeometricCycleClassPointRigidity.lean` constructs
the unique extension of point fundamental-class data and proves
`suppliedCycleClass_eq_geometric`. It still requires an independently
constructed fundamental-class assignment and its pointwise comparison.
Those requirements must be discharged for the canonical map in any
eventual all-varieties solution; naming a supplied field "true" or
"actual" does not discharge them.

### Exact computations and their scope

Wolfram exact arithmetic reproduced the P^2 x P^2 multiplication
matrix L=[[1,1,0],[0,1,1]] in basis (a^2,ab,b^2). The primitive
kernel is spanned by (1,-1,1). The two Picard trace columns
(-1/2,0,1/2) and (1/2,0,-1/2) have rank one but nonzero
L-images, in agreement with the new universal relative theorem.
An independent exact three-sector quotient check gives determinant t
for columns (1,-t,0), (0,1,-t), (0,1,0), confirming transversality
when t is nonzero. Neither finite calculation constructs the missing
arbitrary-X geometry or authenticates an unspecified comparison map.

Next required research step: construct new native algebraic sources
on the original arbitrary X with independent primitive classes beyond
the known Lefschetz image, and prove the fundamental-class comparison.
Their universal existence is not established at this checkpoint.

## 2026-10-17: component selection as an additional source operation

Base checkpoint: `158b349037d069c45bb6db794297b3d3830527f1` on
`mathbox/residual-zero-direct-audit-20261015`. The requested universal
construction and its canonical geometric cycle-class certification remain
UNPROVED. This continuation does not replace that goal by generation of
only the already algebraic subspace.

### What the existing cut code actually constructs

The following source files were read in this continuation:

* `GSTClassicalHodgeProjectivePrincipalSection.lean` constructs a genuine
  reduced principal subscheme and pulls it back through the projective
  embedding. Its general `principalSection V f` accepts an equation; its
  selected separator is chosen to avoid the source point.
* `GSTClassicalHodgeProperCutCodimensionOne.lean` proves finiteness of the
  coheight-one locus of a proper closed cut.
* `GSTClassicalHodgePointClosureRelativeCut.lean` constructs the finite
  relative coheight-one successor locus on the source closure.
* `GSTClassicalHodgePrincipalCutSuccessorOperator.lean` sums the selected
  successor atoms, retaining the exact ambient codimension stratum.
* `GSTClassicalHodgeRelativeSuccessorExactStratum.lean` and
  `GSTClassicalHodgeExactVerticalCutRay.lean` certify positive native
  coefficients and native nonvanishing for surviving branches.
* `GSTClassicalHodgeProjectiveSeparatorSuccessorPoint.lean` and
  `GSTClassicalHodgeSeparatorRelativeCover.lean` construct a genuine
  selected projective successor and its relative cover relation.

Native nonvanishing here is not nonvanishing of the primitive Betti class.
The constructors also do not establish that their selected equation or
selected minimal prime reaches a prescribed Hodge direction.

### Distinction from the trace-projector obstruction

Selecting an irreducible component of a geometric cut is a different native
source operation from applying a cohomological projector to the TOTAL cut.
For a cut cycle C=sum_i m_i[Z_i], rational linearity gives

    pi(cl(C)) = sum_i m_i pi(cl([Z_i])).

Thus a zero primitive projection of the total only gives a linear relation
among the component projections. It does not make each projection zero.
The preceding trace theorem remains valid on every individual component;
it does not forbid obtaining new source directions by separating components
before applying primitive normalization.

In codimension two, the existing native correction constructs, for each
already obtained component Z_i,

    W_i = [Z_i] - algebraicLefschetzCorrection(cl([Z_i])),
    cl(W_i) = pi(cl([Z_i])).

Its primitivity and exact class formula are the existing theorems
`primitiveizeNativeMiddleCycle_primitive` and
`native_primitive_projection_cycleClass`. The geometric comparison data
and divisor theorem in those declarations remain explicit inputs. This
observation neither proves a new arbitrary-codimension normalizer nor
instantiates those data canonically for every variety.

### Exact component-cancellation experiment

Wolfram Language exact arithmetic was applied to the existing
`GSTCubicFourfoldPlanePrimitive.lean` intersection model, with Gram matrix
G=[[3,1],[1,3]], H=(1,0), P=(0,1), and R=H-P. Define
pi(v)=v-((H.G.v)/(H.G.H))*H. The returned values were:

    P+R = (1,0)
    pi(P+R) = (0,0)
    pi(P) = (-1/3,1)
    pi(R) = (1/3,-1)
    rank_Q {pi(P),pi(R)} = 1
    3*pi(P) = (-1,3)
    (3*pi(P)).G.(3*pi(P)) = 24
    degrees(P,R) = (1,2).

This is an exact finite lattice calculation. It establishes neither the
scheme-theoretic realization of a residual component nor a cycle-class
comparison for an arbitrary X. The existing Lean lattice model is not a
formal construction of those schemes. No new Lean verification is claimed
for this computation or for the requested universal theorem.

### First unresolved step and route state

The source-operation route is OPEN, with no universal spanning result.
One possible geometric continuation is to vary the equations and selected
minimal primes, rather than reuse the single chosen cut at each source.
The current cut declarations do not prove the proposed target-directed
exhaustion by such paths. Even an exhaustion of ALL native point cycles
would still leave the following distinct assertion unproved:

    span_Q { pi(cl([Z])) : Z irreducible of codimension p in X }
      = every rational primitive (p,p) Hodge direction of X.

The point-normal-form and point-rigidity results identify the left side
with the primitive algebraic image. They do not identify it with the full
primitive Hodge fiber. Likewise, choosing a maximal independent finite
family in that image does not prove equality with the target fiber.

No discriminant, period detector, GST operator realization, or geometric
construction proving this equality on every original X was obtained in
this continuation. The separate construction of canonical point
fundamental classes and its comparison with Stage-2G also remains open.
The previous successful Lean run `39007462036` certifies the previous
trace lemmas, not a new universal construction in this checkpoint.

Resume this route when a concrete equation/component construction has a
proved nonzero pairing with an arbitrary missing primitive direction, or
when an independent GST argument proves the displayed span equality.
Testing additional ambient total classes without examining components
would not discriminate this route. An exact finite example alone cannot
discharge the universal quantifier.
