# Mathbox — universal primitive Hodge residual zero-energy research attempt

**Date:** 2026-10-15  
**Research head initially inspected:** \`538d94806299f42165a39fe2aed55c4f5157a533\`  
**Target:** For every smooth projective complex X, integer p with 2p <= dim_C X, every primitive rational Hodge class alpha, let A=im(cl_p) intersect the rational primitive Hodge subspace, let Z_alpha be its Q-polarized orthogonal projection via actual rational algebraic cycle representatives, and define r_alpha=alpha-cl(Z_alpha). Prove Q(r_alpha,r_alpha)=0 by independent geometry, hence r_alpha=0 and full rational Hodge algebraicity by Lefschetz decomposition and hard Lefschetz.

## Verdict at this checkpoint

**Original universal zero-norm theorem: INCOMPLETE / NOT PROVED.**
No independent geometric identity forcing Q(r_alpha,r_alpha)=0 for every X has been established. The new algebraic complementary correspondence is real geometric progress, but its rational Hodge fixed part is precisely what must be controlled.

The statements \`forall X,p,alpha: Q(r_alpha,r_alpha)=0\` and \`forall X,p,alpha: r_alpha=0\` are equivalent under the Hodge–Riemann positive-definite polarization on primitive rational (p,p) classes. Because Z_alpha is algebraic, the latter is the primitive rational Hodge conjecture itself. Consequently, ANY proof of zero-norm for all X,p,alpha is already a proof of the original outstanding theorem, not a consequence of positivity alone.

## Route A — direct positivity + already verified GST duality: invalid as complete proof

The existing green sources \`GSTUniversalHodgeResidualProjection.lean\`,
\`GSTActualXHodgeResidualProjection.lean\`,
\`GSTPolarizedHodgeResidualEnergy.lean\`, and
\`GSTCanonicalPolarizedHodgeGhost.lean\` establish:

    alpha = cl(Z_alpha) + r_alpha
    Q(cl(Z_alpha), r_alpha) = 0
    Q(alpha,alpha) = Q(cl(Z_alpha),cl(Z_alpha)) + Q(r_alpha,r_alpha)
    Q(r_alpha,r_alpha) >= 0
    r_alpha != 0 => Q(r_alpha,r_alpha) > 0.

There is no second independently established inequality forcing
Q(r_alpha,r_alpha)<=0, nor an identity Q(r_alpha,r_alpha)=0.
Attempting to use the ghost's vanishing against algebraic classes to infer
vanishing against r_alpha is precisely the missing step: r_alpha is not known
algebraic and cannot be substituted into an algebraic-cycle-only incidence theorem.

**Exact rational logical test, Lean:** \`GSTResidualZeroLogicalCountermodel.lean\`.

Set V=Q², N=Q, cl(z)=(z,0), algebraic generator cl(1)=(1,0),
dual detector ell(x,y)=x, alpha=(0,1), Q(v,v)=v_1²+v_2².
Then all existing rational linear duality/orthogonality identities hold,
yet Z_alpha=0, r_alpha=(0,1), Q(r_alpha,r_alpha)=1.

**Evidence boundary:** The test is a countermodel to DERIVABILITY from
the algebraic-linear axioms. It is NOT a genuine smooth projective
variety and does NOT refute the Hodge conjecture. It proves the
approach needs further geometric input not encoded by those axioms.

GitHub Actions exact run **38763793573**: SUCCESS.

## Route B — new actual algebraic diagonal-minus-Gram correspondence

There is a genuine geometric advance available for arbitrary X.
Let d=dim_C X, p<=d/2, and choose finitely many actual algebraic
codimension-p cycles Z_i such that a_i=cl(Z_i) form a rational basis of
A=im(cl_p) intersect the primitive rational Hodge subspace.
The polarization

   Q_p(u,v)=(-1)^p int_X u cup v cup h^(d-2p)

is rational and positive definite on that space, so its Gram
G_ij=Q_p(a_i,a_j) is invertible over Q.

Define actual algebraic cycles
   W_i=(-1)^p Z_i cup h^(d-2p) in CH^(d-p)(X)_Q.
The genuine algebraic correspondence of codimension d on X×X is

   Pi_A = sum_(i,j) (G^-1)_ij (W_i × Z_j).

This cycle is constructed from algebraic cycles independent of
the unknown primitive target alpha. By the honest exterior-product,
projection, cycle-class and Gysin formulas,

   Pi_A,*(v) = sum_(i,j) (G^-1)_ij Q_p(v,a_i) a_j
             = cl(Z_v)      for primitive v of Hodge type (p,p).

Thus the geometric correspondence Pi_A acts as the Q-orthogonal
projection onto A, and its cohomological action satisfies Pi_A,*²=Pi_A,*.

The diagonal cycle Delta_X is algebraic, and hence

   Pi_perp = Delta_X - Pi_A in CH^d(X×X)_Q

is an ACTUAL algebraic correspondence, whose cohomological action on
primitive (p,p) is the residual map v -> r_v.
It is cohomologically idempotent, with image equal to the primitive
orthogonal complement of A. **No Chow-level idempotence modulo rational
equivalence is claimed.**

Lean \`GSTPrimitiveAlgebraicMotiveProjector.lean\` checks the abstract
rational cohomological projector algebra for arbitrary finite rank:
Pi_A²=Pi_A, Pi_perp²=Pi_perp, Pi_perp kills known generators and fixes
every detector-orthogonal class. The existence of the actual Chow
correspondence Pi_A is justified mathematically above by product/Gysin
geometry, but the Mathlib product cycle and Betti comparison are NOT
instantiated in this standalone Lean file.

This geometric construction is nontrivial, but cannot establish
Pi_perp(r_alpha)=0: it establishes the OPPOSITE for any residual,
namely Pi_perp(r_alpha)=r_alpha.

### Crucial genuine geometric discriminating example (not a Hodge counterexample)

Let S be a projective K3 surface of Picard rank rho.
By the Lefschetz (1,1) theorem all rational (1,1) classes on S are
algebraic, so the primitive residual rational Hodge space is ZERO.
However, on rational cohomology H²(S,Q), the transcendental
complementary correspondence Delta_S-Pi_NS has rank 22-rho>0.
For example at Picard rank 1 its H² trace is 21.

Therefore a simple total-Betti-trace = 0 argument for the
algebraic complement is false EVEN IN A GEOMETRIC FAMILY WHERE
THE HODGE CONJECTURE HOLDS. The missing target is the RATIONAL
(p,p)-fixed part of the complementary Hodge structure, not all
Betti eigenvectors and not the complex H^{p,p} vector dimension.
A cohomologically nonzero algebraic correspondence may project
onto a nonzero transcendental Hodge structure with no rational
Hodge (p,p) vectors.

## Route C — intrinsic GST ghost common-carrier strike

\`GSTClassicalHodgeCommonClassPlaneReduction.lean\` formally proves
\`ghostSeedTargetStrictPacket_isEmpty\`: if a genuine target Hodge
ghost exists and an appropriate algebraic source seed is given,
the exact strict geometric source-to-ghost carrier cannot exist.

The original GST intrinsic branch construction is NOT automatically
such a strict correspondence: it has no independent Chow/betti
incidence realizing the ghost-chosen sheet as an actual cycle.

The new canonical ghost gamma_alpha(v)=Q_p(r_alpha,v) is preferable
to an arbitrary quotient-dual ghost, because it has the explicit
positive readout gamma_alpha(alpha)=Q_p(r_alpha,r_alpha)>0 and
kills all actual algebraic native sources.

But the verified common-carrier trace contradiction is still
CONDITIONAL on constructing a genuine strict source-to-target
correspondence packet. Building one for arbitrary hypothetical
ghosts is exactly the missing universal geometry. The known
diagonal-minus-Gram complement is an actual algebraic
correspondence but does not provide such a strict packet:
its action on r_alpha is r_alpha, not an algebraic target
representative constructed from an algebraic seed.

## Valid independent geometric directions

1. **Motivic/monodromy geometry:** Prove the rational (p,p) Hodge
   invariants of the algebraic complement motive (X,Pi_perp)
   vanish by a geometric symmetry, deformation or Mumford–Tate
   computation, without assuming the desired class has a native
   cycle. This works in some well-controlled families, but no
   all-varieties monodromy theorem is available from current GST laws.
2. **Cycle support/coniveau:** Independently show any primitive
   rational Hodge residual is supported on a closed algebraic
   subset of codimension p; purity/resolution and Gysin yield
   a native algebraic cycle, then orthogonality and positivity
   kill it. The universal support assertion at this degree is
   itself a very strong geometric problem; no such construction
   for arbitrary X was found here.
3. **Ghost-target correspondence:** Construct the strict
   common-carrier, normalized finite trace and point-cycle
   compatibility for the SPECIFIC canonical polarized residual
   ghost, using actual projective geometry and no target-native
   witness or ghost-exclusion field. Existing GST machinery then
   yields the required contradiction. This precise construction
   remains UNPROVED.

## Mathematical integrity contract

- Do not claim that Q(r,r)>=0 and Q(r,A)=0 imply Q(r,r)=0.
- Do not identify a cohomological projector with a Chow projector
  without checking rational equivalence.
- Do not use a diagonal class on X×X to contract an unknown r
  into an algebraic cycle unless its target-dependent contraction
  is independently algebraic.
- Do not infer zero rational (p,p) residual from vanishing or
  positivity of a total Betti/cohomological trace.
- Do not replace a geometric source-to-ghost strict carrier by an
  abstract GST branch or matrix unit.
- Do not promote a Lean gate for conditional linear algebra
  to the all-X Hodge conjecture.

**Next exact research obligation:** An independently geometric
argument eliminating rational (p,p) fixed classes of
Delta_X - Pi_A for EVERY smooth projective X and all p, or a
genuine source-to-canonical-ghost strict carrier in the original GST
geometry. Either achievement would prove the original Hodge target;
neither was supplied by the current branch.



## Exact Hodge-theoretic identification: residual Tate factors

The primitive rational Hodge classes of degree 2p are precisely the
Hodge morphisms

    Hom_HS(Q(-p), P^{2p}(X,Q)).

With the explicit algebraic correspondence Pi_perp above, the
primitive residual target is

    Hom_HS(Q(-p), im(Pi_perp,* | P^{2p}(X,Q))).

The zero-norm theorem requested by the user is therefore equivalent
to proving that the **algebraic complementary cohomological motive**
has no rational Tate Hodge subobject. This is stronger than showing
its Betti realization is nonzero, pure, polarized, or semisimple.

In particular, polarizability and semisimplicity of rational Hodge
structures do not algebraize a Tate summand automatically: they give
a Hodge-theoretic projector. To construct an actual rational
algebraic cycle on X one still needs a genuine cycle or a genuine
algebraic correspondence from a Tate motive with nonzero image.
An abstract Hodge matrix unit or type-correct GST branch is not
that correspondence.

A candidate rank-one rational Hodge projector onto a residual r!=0 is

   T_r(v) = Q_p(v,r)/Q_p(r,r) · r.

It is an idempotent MORPHISM of rational Hodge structures when
r is a rational (p,p) class, but its algebraic-correspondence
realization is not established by its Hodge type. Converting that
Hodge projector to a strict algebraic Tate source/target pair is
one precise new-mathematics task with a falsifiable output:
a codimension-p native cycle on X whose class has nonzero
Q-pairing with the canonical residual ghost.

The earlier GST ghost theorem proves NO SUCH GEOMETRIC CYCLE EXISTS
if the residual is genuinely outside all algebraic classes.
Therefore constructing it independently would close Hodge by
contradiction; merely positing the correspondence would rename
the missing implication.


## Unconditional geometric zero-norm sanity check: codimension one and co-one

There IS a fully independent geometric proof of zero residual norm
for ALL smooth projective complex varieties in weights p=1 and p=d-1,
but it does not prove arbitrary middle codimension.

**Codimension one.** If alpha∈H²(X,Q) has Hodge type (1,1),
choose m>0 with m alpha integral modulo torsion. The analytic
exponential sequence

   0 -> Z -> O_X -> O_X^× -> 1

has obstruction H²(X,Z)->H²(X,O_X)=H^{0,2}(X).
Because alpha is (1,1), its obstruction vanishes, so m alpha=c1(L)
for a holomorphic line bundle L (modulo torsion). Projectivity/GAGA
makes L algebraic; therefore alpha is an algebraic divisor class.
The maximal algebraic residual is already 0, hence its Q norm is 0.
This uses an independently known genuine geometric theorem
(Lefschetz (1,1)), not GST ghost exclusion.

**Co-one on a d-fold.** For d>=2, Hard Lefschetz gives
L^{d-2}:H²(X,Q)->H^{2d-2}(X,Q) an isomorphism of rational
Hodge structures of the appropriate Tate twist. Every rational
(d-1,d-1) class comes from a rational (1,1) class, hence is
the intersection of an algebraic divisor with d-2 hyperplanes.
Its residual norm is again zero.

For d<=3 these codimensions, together with the unit/fundamental
classes, exhaust the Hodge target; hence the classical Hodge
conjecture is established in these low dimensions.

For d>=4, primitive codimension two is the first genuinely
new all-varieties case. The exponential-sequence argument
does NOT extend automatically to higher Chow/codimension
cycles: higher Deligne-class obstructions do not supply an
algebraic cycle from merely rational Hodge type (p,p).

**Verification status:** The above is a standard mathematical
argument using Lefschetz (1,1), GAGA and Hard Lefschetz. It is
NOT a new all-dimensional Lean formalization of those external
theorems; the current standalone Lean CI gates verify only their
displayed rational-linear projector consequences.
