# Mathbox + Wolfram: direct all-variety fixed-homology calibration attack via K-theoretic degeneracy cycles
**2026-10-16 · Original goal unchanged · new geometric construction, NOT an all-X Hodge proof**

## The exact target

For EVERY smooth projective complex d-fold X, every 0<=p<=d and
rational alpha of Hodge type (p,p), construct fixed integers m>0, M>=0
and a sequence T_n of CLOSED INTEGRAL RECTIFIABLE 2(d-p)-currents
with SAME integral homology class beta satisfying

    [T_n] = PD(beta),  beta_Q = m alpha + M h^p,
    D(T_n) = Mass(T_n)-T_n(omega^(d-p)/(d-p)!) --> 0.

This would yield a holomorphic integral cycle by compactness and
Kähler calibration regularity; subtracting M h^p then proves
alpha algebraic and the user's GST zero-residual norm theorem.
No conditional 'Hodge finale' is accepted as completion.

### Important: what has NOW been constructed for every X

A smooth topological complex bundle E and an explicit integral
degeneracy current T(k) with the exact shifted homology class
c_p(E tensor L^k)=m alpha+binom(r,p) k^p h^p.
This upgrades the previous all-X generic triangulation construction
to a geometric stable-complex/characteristic-cycle construction.
It proves CLOSED, INTEGRAL, RIGHT CLASS for every X,p,alpha.

What it has NOT proved: D(T(k))=0 or a sequence with D-->0 for
any ONE FIXED k on arbitrary X. Its geometry need not be holomorphic.

The p=0 case is separately trivial: multiples of the fundamental
cycle of X are already holomorphic, integral and calibrated.

## Construction I: rational K-theory to true integral degeneracy cycles

1. X is a finite CW complex. The rational Chern character is an
   isomorphism K_top^0(X) tensor Q -> H^{even}(X,Q).

2. Choose y in K_top^0(X) tensor Q whose Chern character is pure
   degree 2p:

       ch(y) = (-1)^(p-1) alpha/(p-1)!.

   Choose positive m clearing all denominators, so m y comes from
   integral topological K theory. On compact X, a K-theory element
   plus enough trivial bundle classes is represented by an ACTUAL
   finite-rank smooth complex bundle E, rank r>=p, with

       ch(E) = r + (-1)^(p-1) m alpha/(p-1)!.

   All positive-degree Chern character components EXCEPT degree 2p
   vanish in rational cohomology.

3. Newton's polynomial identities give

       c_j(E)=0 for 1<=j<p,   c_p(E)=m alpha

   as RATIONAL cohomology classes. Integral torsion can remain; it
   is harmless to a rational Hodge target and must not be silently
   called zero in integral cohomology.

4. Take an ample holomorphic line bundle L on X, h=c1(L).
   For each positive integer k, define smooth complex bundle

       F_k=E tensor L^k.

   By the splitting principle, with r formal Chern roots x_i:

       c_p(F_k)
         = sum_{j=0}^p binom(r-j,p-j) (k h)^(p-j)c_j(E).

   Since all lower c_j(E) vanish rationally:

       c_p(F_k) = m alpha + binom(r,p) k^p h^p        (*)

   in H^{2p}(X,Q). The LEFT side is automatically INTEGRAL.
   For fixed k, its integral Poincaré dual beta_k is unambiguous
   even if alpha has torsion-lift ambiguities.

5. Smooth bundles have smooth global sections. A generic smooth
   bundle map

       phi_k : C^(r-p+1) -> F_k

   is transverse to determinantal rank strata. The locus
   D_k={x: rank(phi_k(x)) < r-p+1} has generic real codimension 2p.
   Its complex normal orientation on the top stratum, with
   lower strata of higher codimension, defines a CLOSED integral
   rectifiable current of dimension 2(d-p).
   The smooth Thom--Porteous degeneracy formula gives

       [D_k] = PD(c_p(F_k)) = PD(beta_k).

   Thus a TRUE integral cycle representing (*) is produced for
   every rational cohomology class, even WITHOUT Hodge type.
   The existence of a smooth complex normal structure DOES NOT
   establish that D_k is holomorphic in X's FIXED complex structure.

**Source-dependency scope:** K-theory Chern isomorphism, realization
of virtual K classes by actual stabilized bundles, generic
determinantal transversality, and smooth Thom--Porteous formula
are standard named inputs used here; a project-local authenticated
primary-source verification has NOT been completed. This record
is a detailed mathematical construction, not a Lean formalization
of these external geometric theorems.

## Wolfram exact Chern-polynomial verification

With r variables x_i, let e_j be elementary symmetric polynomials.
For rank r, codimension p, compare

  Coefficient[Product[1+z*(x_i+t),{i,1,r}],z,p]

against

  Sum[Binomial[r-j,p-j]*t^(p-j)*e_j,{j,0,p}].

The exact Wolfram Language kernel returned zero difference for ALL
10 pairs (r,p) with 3<=r<=6 and 2<=p<=min(4,r).

For (r,p)=(5,3) it computed, before lower Chern class reduction,

   c_3(F) = 10t^3 + 6t^2 c_1(E) + 3t c_2(E) + c_3(E).

Under c_1=c_2=0, this is c_3(E)+10t^3, as claimed.

For a fourfold X, p=2 is the FIRST general unresolved rational
Hodge codimension (codim 1 and codim d-1 have known divisorial
proofs). For a rank-5 bundle with c1(E)=0:

   c_2(E tensor L^k) = m alpha + 10 k^2 h^2.

A real oriented integral 4-current representing this class is
constructed from smooth rank-drop geometry for every alpha.

## Construction II: why growing twist k does NOT solve fixed-homology

Suppose one develops an asymptotically complex section theory
producing better Kähler angles as k increases and D(D_k) small
RELATIVE to the degree of beta_k.

This alone cannot finish the fixed-beta statement: beta_k changes
by binom(r,p)(k^p-k0^p)h^p with k.

A natural attempt is to correct homology with an ACTUAL holomorphic
complete-intersection current H of class h^p:

   S_k=[D_k] - A_k [H],
   A_k=binom(r,p)(k^p-k0^p) >=0.

Then [S_k]=beta_k0 exactly. However for generic proper intersections
(no positive 2(d-p)-dimensional mass overlap), geometric mass
is additive on the positive and negatively oriented sheets. With
H calibrated,

   D(S_k)
     = D(D_k) + 2 A_k Mass(H)            (**)

because reversing the orientation of a calibrated sheet changes
its contribution from defect 0 to defect 2*mass. The right side
DIVERGES like k^p, even when D(D_k) approaches zero!
Cancellation only at actual overlapping components could change this.

Wolfram computed, for (r,p,k0)=(5,2,1),
   (k, A_k, 2 A_k) for k=1..6:
   (1,0,0), (2,30,60), (3,80,160), (4,150,300),
   (5,240,480), (6,350,700).
The third coordinate uses Mass(H)=1 units.

Therefore high twisting and subtraction is not a mass-compatible
path back into ONE fixed integral homology class.
This is a decisive check on the otherwise promising K route.

## Construction III: what Kähler-angle control must add

On the rectifiable regular locus of the oriented degeneracy cycle
write xi(x) for its unit tangent 2q-vector, q=d-p.
The calibration inequality is exact:

  D(D_k)= integral_{D_k} [1-<omega^q/q!,xi(x)>] dMass.

The (p,p) condition on the COHOMOLOGY class does NOT force
the integrand to vanish on the particular representative D_k.

To establish a fixed-k zero-defect SEQUENCE one must produce
bundle maps phi_{k,n} at one single k such that:

   (a) all their degeneracy cycles have class c_p(F_k);
   (b) their total masses are uniformly bounded; and
   (c) their L^1 tangent-plane failure of Kähler calibration
       tends to ZERO absolutely.

A sufficient concrete condition would be
   integral_{D(phi_{k,n})} [1-<calibration,xi_n>] dMass -> 0.
This is the original integral current target written in geometric
coordinates, not an independently supplied lemma.

For p=1 a Hodge integral class is c1 of a HOLOMORPHIC line bundle,
by the exponential sequence. A large ample twist admits a
holomorphic nonzero section; its divisor gives a TRUE calibrated
integral cycle. For p=d-1, Hard Lefschetz reduces alpha to
a rational (1,1) class. Twisting the latter by an ample class
and intersecting the resulting effective divisor with (d-2)
general hyperplane divisors constructs the required effective
1-cycle. Thus these outer codimensions are genuinely solved
by a constructive constant sequence T_n=T.

For general p>=2 away from d-1, an arbitrary smooth bundle E
need not admit a holomorphic structure compatible with X, and
the topological Chern construction has no universal fixed-k
complex-tangency convergence theorem. Merely assuming that such
phi_{k,n} exist would import the original Hodge conjecture.

## Direct interface with GST N-cohomology

waves/GSTNCohomologyV3.lean carries independent rational hole
coordinates; GSTNAllChannelAmpleSaturation.lean proves an explicit
integer shift achieving absolute defect zero in EVERY FINITE
N-channel model with positive integer ample coefficients.
It does NOT create the required algebraic basis vectors for X.

The current K-theory step gives actual smooth topological cycles
for arbitrary X in the CORRECT homology classes; thus it removes
the basic geometric **integral class realization** obstruction.
It does not turn N's algebraic generators into calibrated
holomorphic cycles. N finite integer positivity cannot replace
the differential geometric Kähler-angle estimate.

## Adversarial audit of proof status

- Finite N positive ample shifts: constructive algebraic formula,
  committed to GSTNAllChannelAmpleSaturation.lean, pending Lean CI.
- Actual arbitrary-X integral characteristic cycles: construction
  relying on the named standard K-theory / Thom--Porteous results.
- Absolute vanishing of calibration defect in one fixed class for
  ALL rational Hodge alpha: NOT PROVED.
- Universal algebraic representative and GST residual zero: NOT PROVED.
- No fake ghost elimination, asserted geometric-section axiom,
  'sorry', arbitrary cycleClass replacement, or claim of Clay proof.

This is the original Hodge target with a new independent geometric
route actually developed to its first decisive failed implication.
