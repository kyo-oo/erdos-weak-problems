# Mathbox + Wolfram — universal fixed-homology calibrated-current attack through GST N-channels
**Date**: 2026-10-16
**Original, unchanged target**: For every smooth projective complex X, every rational Hodge (p,p) class alpha, produce integers m>0, M>=0, beta=m alpha+M h^p integral and a sequence of closed integer-rectifiable currents T_n in PD(beta) with absolute Wirtinger calibration defect tending to zero. This would prove algebraicity and the user's universal primitive Hodge residual-zero theorem.

**Outcome of this execution**: The original all-X theorem has NOT been proved. The N-channel ample-shift obstruction has been repaired, a genuinely geometric calibrated-current construction is explicit for all products of projective spaces in all dimensions/codimensions, and a new independent all-X route through rational topological K-theory has been tested through its first geometric lifting obstruction.

## Route A: the overlooked effect of the allowed ample shift (fixed finite N-model)

Previous GREEN code GSTNIntegralCalibrationGap.lean proved a calibration defect >=4 for integral cycles in period class 1 of the two-channel weighted lattice:
  period(a,b)=2a+3b; mass(a,b)=2|a|+3|b|.
This is correct in the *unshifted* class, but NOT an obstruction to the user's target, which explicitly allows an ample shift.

New code GSTNAmpleShiftIntegralRealization.lean constructs, for ANY n in Z:
  a(n)=-n+3|n| >=0
  b(n)=n+2|n| >=0
  period(a(n),b(n))=n+12|n|
  defect(a(n),b(n))=0.

Thus a constant sequence of genuine INTEGER cycles has exactly zero calibration defect in the shifted model, for every original integer class n. The shift period 12 is in the interior of the two-channel cone: 12=2*3+3*2. This does not realize cycles on an actual arbitrary X, but it decisively corrects the prior finite integrality analysis.

Wolfram Language independently checked the smaller period-one family:
  beta_M=1+6M.
M=0: integer signed representative (-1,1), defect 4.
M>=1: nonnegative integer representative (a,b)=(3M-1,1),
       period=beta_M and defect=0.
Exact computation returned M=0..7 with defects {4,0,0,0,0,0,0,0}.

### General finite semigroup saturation mechanism

Let v_1,...,v_r be actual generators of an additive lattice L over Z, let
h=sum_i b_i v_i with b_i>=1 INTEGERS, and let x=sum_i a_i v_i
with integers a_i of either sign. For sufficiently large integer M,
each a_i+M b_i>=0, so
    x+M h=sum_i (a_i+M b_i) v_i
belongs to the effective semigroup. This is an unconditional theorem
once both decompositions into ACTUAL geometric generators are supplied.
A full-rank finite cone with a rational-interior ample direction admits
a positive representation after replacing h by an integer multiple.

What is not given by GST N-channel readout independence is a map from
its abstract integer vectors to actual algebraic cycle classes that is
surjective on H^{p,p}(X,Q) for arbitrary X. Inventing such a map as a
field would assume the conclusion. The finite semigroup theorem
removes an integrality issue *after* that map exists, not the
geometry needed to make it exist.

## Route B: a universal-in-dimension genuine projective construction

The construction works for every variety in the family
  X = product_{j=1}^r P^{d_j}_C
with arbitrary positive integer r, arbitrary dimensions d_j and
every codimension 0<=p<=d=sum_j d_j.

Let H_j be the hyperplane class on factor j and h=sum_j H_j.
The Chow ring (and entire rational even Betti ring, by the cellular
Kunneth structure) is
  Q[H_1,...,H_r]/(H_1^{d_1+1},...,H_r^{d_r+1}).
Every rational (p,p) Hodge class alpha has a UNIQUE expansion
  alpha = sum_{k: sum k_j=p; 0<=k_j<=d_j} a_k H_1^{k_1}...H_r^{k_r}
with a_k in Q.

Choose m>0 clearing all denominators and write
  c_k = m a_k in Z.
The degree-p ample power is
  h^p = sum_k binomial(p;k_1,...,k_r) H^k,
with every coefficient B_k=p!/product_j(k_j!) a POSITIVE INTEGER.

Choose an INTEGER M>=0 with
  c_k+M B_k >= 0 for ALL finitely many k.
This is always possible explicitly; e.g. M=sum_k |c_k| works
because B_k>=1. Then
  beta=m alpha+M h^p
      =sum_k (c_k+M B_k) H^k
has an EFFECTIVE algebraic representative: take products Y_k of
generic linear subspaces of codimension k_j in each P^{d_j},
and set
  T=sum_k (c_k+M B_k)[Y_k].

This T is a positive integer holomorphic 2(d-p)-cycle,
is closed, lies in exactly PD(beta), and is CALIBRATED:
  Mass(T) = T(omega^{d-p}/(d-p)!).
Therefore the explicitly given CONSTANT integral sequence T_n=T
has defect identically zero for ALL rational Hodge alpha on
ALL products of projective spaces, in ALL dimensions and degrees.

This IS genuine actual smooth projective geometry, not merely
finite channel arithmetic. It proves a long-known Hodge case by
a concrete cycle-by-cycle calibrated-current construction.
It does NOT cover arbitrary smooth projective X.

### Wolfram computation for a nontrivial five-dimensional example

X=P^2 x P^2 x P^1, dimension d=5, codimension p=2;
write (a,b,c) for factor hyperplane classes and h=a+b+c.
Choose an integral Hodge class
  alpha=-5a^2-3b^2+7ab-4ac+2bc.
Wolfram Language computed all permitted p=2 monomials:
  {bc,b^2,ac,ab,a^2}
and coefficients after shifting by M=5:
  {12,2,6,17,0}.
Every coefficient is a NONNEGATIVE INTEGER. Consequently
  T=12[Y_bc]+2[Y_b^2]+6[Y_ac]+17[Y_ab]
is a closed, integer-multiplicity calibrated 6-dimensional
(real dimension) current with class alpha+5h^2.
The constant sequence T_n=T has defect zero.
This example is projective geometry, not an all-X proof.

## Route C: attempt to create arbitrary-X geometric carriers from topological K-theory

For any compact smooth X, the rational Chern character is an
isomorphism K^0_top(X)⊗Q ≅ H^{even}(X,Q).
An arbitrary rational degree-2p Hodge class alpha therefore
is the pure-degree Chern character of a VIRTUAL topological
complex vector bundle after rationalization. Clearing
denominators supplies a signed topological bundle class, and
generic *smooth* degeneracy-locus constructions recover
characteristic homology classes by smooth geometric cycles.

This approach constructs topological data independent of existing
algebraic Chow representatives. However, generic smooth
degeneracy loci are not complex-analytic, and their tangent
planes are not necessarily Kähler-calibrated.

To make the route construct an *integral calibrated* current,
one needs integrable holomorphic bundle/section data giving
a genuinely holomorphic degeneracy locus, or a uniformly
mass-decreasing integral isotopy/flow approaching one in
the SAME homology class. The rational Hodge condition on
ch_p does not, by itself, produce an F^{0,2}=0 holomorphic
bundle connection or a holomorphic section. The known
codimension-one exponential-sequence argument is a special
positive case. In arbitrary higher codimension no universal
such construction has been established here.

This is a tested route, not a geometric counterexample.

## Final evidence boundaries

* Lean V3 independent N-hole coordinates: GitHub Actions 38843813429 GREEN.
* Original unshifted integer defect gap: 38845762815 GREEN.
* Actual GST native cycle / N-mass bridge: 38846681250 GREEN.
* Shifted integer zero-defect model: GSTNAmpleShiftIntegralRealization.lean; GitHub Actions 38850483241 SUCCESS, Lean kernel verified.
* Wolfram two-channel shifts and P^2 x P^2 x P^1 coefficient calculations: exact integer arithmetic verified, inputs displayed above.
* Actual every-product-projective calibrated construction: rigorous projective geometry using the Chow/Kunneth basis, complete intersections and the Wirtinger calibration.
* Missing to solve the user's ORIGINAL all-X Hodge problem: a geometric effective-cycle generation theorem spanning arbitrary rational Hodge classes of arbitrary smooth projective complex X, or an independently geometric integral current flow proving inf Defect=0 in an ample-shift class. No new GST channel identity, positivity calculation, virtual topological bundle, or compiled conditional proof supplies this by itself.

**The universal fixed-homology sequence was NOT produced; no unconditional Hodge proof is claimed.**


## Route D: exact stationary noncalibrated representative in an AMPLE rational Hodge class

This is a genuine projective-complex-variety test against any claim
that generic GST mass descent / mean-curvature flow from arbitrary
integral representatives must converge to the Kähler calibration cone.

Let E=C/(Z+i Z) be the square projective elliptic curve,
X=E x E with global real coordinates x,y,u,v mod 1,
complex coordinates z1=x+i y and z2=u+i v, Euclidean product
metric and integral Kähler form
    omega=dx wedge dy+du wedge dv.
It is a smooth projective complex abelian surface.

Take three real two-tori with the natural orientations:

  T_xu = {y=v=0}, tangent (e_x,e_u), area 1,
          int_T_xu omega=0 (Lagrangian);
  T_yv = {x=u=0}, tangent (e_y,e_v), area 1,
          int_T_yv omega=0 (Lagrangian);
  G_i  = {z2=i z1}, tangent (e_x+e_v,e_y-e_u), area 2,
          int_G_i omega=2 (holomorphic).

Every component is a flat totally geodesic torus; the integral
current
  T_bad=[T_xu]+[T_yv]+[G_i]
is closed and its underlying integral varifold is stationary.
All intersections between the sheets have 2-dimensional measure
zero, so
  Mass(T_bad)=1+1+2=4,
  T_bad(omega)=0+0+2=2,
  absolute calibration defect=2.

Compute integral Poincare duals, with X orientation dx dy du dv.
Define the cross (1,1) class
  A=dx wedge du+dy wedge dv.
Then
  PD(T_xu)=-dy wedge dv,
  PD(T_yv)=-dx wedge du,
  PD(G_i)=omega+A.
So
  PD(T_bad)=(-A)+(omega+A)=omega.
In particular, T_bad lies in the SAME **AMPLE INTEGRAL HODGE
HOMOLOGY CLASS** as the standard effective holomorphic divisor
  T_good=[E x {0}]+[{0} x E].
The latter is also a closed integer rectifiable 2-current:
  Mass(T_good)=2,  T_good(omega)=2, defect=0.

Thus we have TWO EXPLICIT integral representatives in EXACTLY THE
SAME positive ample class:
  T_bad: stationary (as integral varifold), defect 2;
  T_good: Kähler-calibrated, defect 0.

Wolfram Language verified ALL finite tensor identities exactly:
  (a) J^T PD(G_i) J = PD(G_i) (type (1,1));
  (b) PD(T_xu)+PD(T_yv)+PD(G_i)=omega;
  (c) omega(e_x+e_v,e_y-e_u)=2;
  (d) Euclidean area of G_i unit square =2;
  (e) mass/period/defect triplet of T_bad = {4,2,2}.

This defeats the PROPOSED inference that any stationary/minimal
integral representative of a rational Hodge class must already
be calibrated. Even in an ample class where a holomorphic cycle
is immediately available, a distinct stationary noncalibrated
integral representative exists. A Brakke-type mean curvature flow
can stay stationary at this varifold, so mean curvature alone
cannot guarantee global calibrated realization.

This is NOT a counterexample to the Hodge conjecture; the
exact SAME class explicitly has the holomorphic T_good.

### The all-X implication actually needed

A successful GST geometric process must include a genuinely
global method to select/surger/replace among homologous integral
cycles, together with an independently proved terminality
criterion forcing defect zero for arbitrary (p,p) rational
homology classes. Finite N-cohomology identities, stationarity,
and the existence of positive diffuse (p,p) currents do not
by themselves supply such a selection mechanism.

Neither the all-X sequence nor a proof of Hodge has been supplied.


## Verification checkpoint

All verification at the pinned commit named by its own GitHub Actions run. The dedicated shifted N-channel integer-sequence check 38850483241 completed SUCCESS with no reported errors. The earlier missing-olean failure in 38850122415 was a workflow root/dependency-registration error, fixed by adding waves.GSTNCohomologyV3 as a library root; it was not a mathematical counterexample. No run checks analytic currents or establishes Hodge for all X. The explicit abelian-surface matrices were computed using Wolfram exact integer arithmetic, not claimed Lean formalized.
