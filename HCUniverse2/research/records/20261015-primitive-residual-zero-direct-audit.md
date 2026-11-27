# Mathbox direct proof attempt: universal primitive Hodge residual zero norm
**Date:** 2026-10-15
**Source branch:** research/mathbox-k3-diagonal-primitive-20261015
**Inspected exact head:** 4f66490f2636b10e5719ca16ea36b2e90e3b0a68
**Work branch:** mathbox/residual-zero-direct-audit-20261015

## Original goal (no substituted conclusion)
Let X range over all smooth projective complex varieties, p over every
primitive cohomological codimension, alpha over every rational primitive
Hodge (p,p) class, A_X,p over the full actual algebraic primitive image,
Z_alpha over the algebraic cycle obtained by Q-orthogonal projection to
A_X,p, and r_alpha=alpha-cl(Z_alpha).

**Prove unconditionally Q(r_alpha,r_alpha)=0 for every X,p,alpha,
from independent geometric arguments.**

### Verdict
**NOT PROVED.** The closest valid result is the exact equivalence
of universal residual zero norm and the original primitive rational
Hodge conjecture (for the same genuine cycle-class map). No independent
geometric argument producing universal zero norm was found.

This should not be presented to the user as completion of the goal.

## Exact proof, checked in Lean
Source: GSTResidualNormZeroExactHodgeEquivalence.lean
Dedicated GitHub Actions:
https://github.com/kyo-oo/HC-PROOF/actions/runs/38767273820
Status: SUCCESS.

Let V be the primitive rational (p,p) Hodge fiber, N the actual rational
native cycles mapping to V, c:N->V the true cycle-class map, and Q a
positive definite rational Hodge--Riemann polarization.
Let a_i=c(Z_i) be a rational basis of the whole EXISTING algebraic
image A=im c. Because Q|_A is positive definite, its Gram inverse
defines exact intersection-dual functionals ell_i with
ell_i(a_j)=delta_ij.

Define
  Z_alpha = sum_i ell_i(alpha) Z_i
  r_alpha = alpha - c(Z_alpha).

1. Duality implies c(Z_alpha) is the Q-orthogonal projector onto A.
2. If alpha is ALREADY algebraic then alpha belongs to A, so the
   projector fixes alpha and r_alpha=0.
3. Conversely if Q(r_alpha,r_alpha)=0, positive definiteness
   yields r_alpha=0, so alpha=c(Z_alpha), an actual rational
   algebraic-cycle representative.
4. Therefore for EACH alpha,

      Q(r_alpha,r_alpha)=0  <=>  alpha in im(c).

   Taking all alpha yields:

      (forall alpha, Q(r_alpha,r_alpha)=0)
         <=>
      (forall alpha, exists Z algebraic with cl(Z)=alpha).

The exact equality in 4, not just the forward direction, is
machine-checked under the displayed geometric-polarization
and existing-image basis data.

The finite basis of A exists independently of Hodge surjectivity
because rational Betti cohomology is finite dimensional and
the restriction of Q to A is nondegenerate. The theorem never
assumes A=V, nor asserts existence of that identification.

## Independent geometric argument attempts, tested against existing GST

**Polarization-only / orthogonal ghost.**
The decomposition Q(alpha,alpha)=Q(c(Z_alpha),c(Z_alpha))+
Q(r_alpha,r_alpha) only gives Q(r_alpha,r_alpha)>=0.
It supplies NO Q(r_alpha,r_alpha)<=0. The preexisting
GSTResidualZeroLogicalCountermodel.lean is a rigorously verified
rational example V=Q^2,N=Q,c(z)=(z,0),alpha=(0,1),
Q(x,x)=x_1^2+x_2^2 with residual norm 1. Thus the
needed zero-norm implication does not follow from the
existing abstract positivity/duality equations.
This is NOT a smooth-projective Hodge counterexample.

**Explicit geometric algebraic complement projector.**
The genuine cycle Pi_perp=Delta_X-Pi_A is algebraic as a
correspondence; its Betti action on the rational primitive
Hodge fiber is the residual orthogonal projector R.
Existing green GSTPrimitiveAlgebraicMotiveProjector.lean proves
R^2=R and R(r_alpha)=r_alpha.
These equations preserve, not annihilate, a hypothetical
nonzero residual. Algebraicity of a correspondence does not
make each cohomology vector in its image an algebraic class.

**GST strict common-class geometric ghost carrier.**
The canonical ghost gamma(v)=Q(r_alpha,v) vanishes on every
class represented by actual algebraic cycles and detects
alpha by gamma(alpha)=Q(r_alpha,r_alpha)>0 when residual
is nonzero. Existing GST strict source/target trace contradiction
would eliminate gamma only if a REAL strict finite algebraic
correspondence carries an already algebraic source seed to
the ghost-selected missing target sheet with the required
Betti pullback and native-cycle incidence identities.
The current modules establish this implication, but do
not unconditionally produce such a carrier for arbitrary X.
Using a formal Hodge matrix unit would be circular.

**K3 and low-codimension calibration.**
Lefschetz (1,1) (via the holomorphic exponential sequence and GAGA)
independently establishes zero residual for p=1, and Hard Lefschetz
extends it to p=d-1. All classes are algebraic in dimensions d<=3.
For d>=4, universal middle primitive codimension p>=2
remains the unsolved case. These verified special cases
do not imply a uniform all-X zero-norm theorem.

## Why the missing step cannot be bypassed syntactically
An algebraic correspondence acting on an algebraic source class
has algebraic image by genuine cycle-class naturality.
The diagonal acts as the identity on *every* Betti class, including
transcendental classes; its algebraicity does not turn its
nonalgebraic cohomological arguments into cycles.
Hence the ghost-target strict-carrier construction would need
a geometric source not generated solely by the existing
algebraic image if the sought alpha lies outside it.

Any unconditional proof that genuinely supplies either
(1) a zero-energy identity independent of Hodge surjectivity,
or (2) an algebraic native cycle with nonzero gamma pairing
for a hypothetical missing residual, would settle this exact goal.
Neither was obtained in this execution.

**Evidence label:** target incomplete; equivalence proved
as written (GitHub Actions SUCCESS); formal linear positive-residual
countermodel proved but not a geometric counterexample.
No accepted all-varieties Hodge proof claimed.
