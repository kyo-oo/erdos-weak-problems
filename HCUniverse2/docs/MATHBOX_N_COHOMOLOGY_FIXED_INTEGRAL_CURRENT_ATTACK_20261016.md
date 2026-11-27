# Mathbox + Wolfram: N-cohomology, fixed-homology integral currents, and Hodge zero residual
2026-10-16

## THE ORIGINAL TARGET (unchanged)

For every smooth projective complex X, all p, every rational primitive
(p,p) Hodge class alpha, construct a SINGLE positive shift
    beta = m alpha + M h^p (integral modulo torsion)
and integral rectifiable closed currents T_n representing PD(beta)
with absolute Kähler calibration defects D(T_n) -> 0.

If this succeeds, integer compactness and calibrated-current analyticity
produce an effective algebraic representative of beta. Subtract M h^p
and divide by m to represent alpha; the GST residual r_alpha vanishes
and Q(r_alpha,r_alpha)=0.

**Research verdict for the universal quantifier: unproved.** This file
records the concrete N-cohomology upgrades and explicit geometric
discrimination, not a substituted theorem.

## What was actually upgraded in N-cohomology (Lean-checked)

Original source files:
* waves/GSTNCohomology.lean
* waves/GSTNCohomologyV2.lean

Upgrade, on the independent Mathbox work branch:
* waves/GSTNCohomologyV3.lean
* GitHub Actions run 38843813429 — SUCCESS
* GSTNCurrentCalibrationCompatibility.lean — integrates the upgrade
  with the repository's actual native algebraic-cycle mass; its
  dedicated CI outcome must be checked separately (run 38844187690).

The old V2 canonicalNCohoBasis takes the same value for every index.
This never established linear independence of holes. The new
independentHoleBasis i j = delta_ij on Q^(Fin s.holes) gives:
    sum_i c_i delta_ij = c_j,
and a zero linear combination implies all coefficients zero.

The genuine original tower amplitude,
    waveIIAmplitude R (s.channel i),
is now an actual coordinate vector in that basis, not a declaration of
topological Betti rank in an unrelated complex projective variety.

The second upgrade proves that for any rational-linear
    M: signed native cycles -> Q,
    (forall Z, M Z >= 0) => (forall Z, M Z=0).
For M nonzero there is Z with M Z < 0.
Thus nativeCycleMass from GST classical Hodge cannot equal nonnegative
rectifiable-current mass on all signed cycles. The contradiction is
mathematically structural and verified, not a CI tool issue.

## Wolfram computation: exact middle-dimensional projective geometry

On X = P^2 x P^2, h=A+B, choose primitive r=A^2-AB+B^2.
In the Chow ring Q[A,B]/(A^3,B^3):
    h*r=0; integral_X r*h^2=0; integral_X r^2=3.
Shift r by h^2:
    beta=h^2+r=2A^2+AB+2B^2,
which is effective on this *cellular* X.
Wolfram Language coefficient calculation verifies the above.
It is NOT a universal construction for non-cellular X.

## GENUINE integral-current geometric test: projective abelian surface

Let E=C/(Z+i Z) be the standard square elliptic curve, a projective
complex curve; X=E x E with coordinates (x,y;u,v) mod Z^4,
flat product Kähler form
    omega = dx ^ dy + du ^ dv.
Take C=E x {0}. For a real epsilon, graph the smooth map
    f_epsilon(x,y)=(epsilon sin(2 pi x),0) mod Z^2
to obtain the closed, oriented, integer rectifiable current T_epsilon.

Every graph T_epsilon is HOMOLOGOUS to C: f_epsilon is homotopic
to the constant map by scaling epsilon.
A graph is holomorphic only at epsilon=0 (for these functions).

Its induced Riemannian area element is:
    sqrt(1+4 pi^2 epsilon^2 cos^2(2 pi x)) dx dy.
And its Kähler period is fixed:
    integral_(T_epsilon) omega = 1.

Consequently, for epsilon!=0,
    D(T_epsilon)
      = integral_0^1 (sqrt(1+4 pi^2 epsilon^2 cos^2(2 pi x))-1) dx
      > 0,
but
    0 < D(T_epsilon) <= pi^2 epsilon^2 -> 0.

The upper bound follows from sqrt(1+t)<=1+t/2 and
integral_0^1 cos^2(2 pi x) dx=1/2.
Wolfram Language EXACT Taylor-integral computation returned
    pi^2 epsilon^2 - 3/4 pi^4 epsilon^4
through order epsilon^4.

**Crucial new test result:** Fixed-integral-class current defect is
NOT quantized with any uniform positive lattice spacing even
on a smooth projective complex variety. Therefore the GST N-wave
interference law (integer source multiple of 56) cannot be
substituted directly for calibrated-current defect via a fixed
nonzero rescaling: the graph sequence disproves that identity.
An actual geometry-aware analytic comparison would have to map
the window signal to current tangent geometry and correctly
reproduce its continuous defect behavior.

This is not a counterexample to the Hodge conjecture:
C is an algebraic curve and its class is calibrated by T_0.

## A general geometric criterion, not an automatic existence proof

For a fixed integral homology class beta define
    delta(beta) = inf_{T closed integral, [T]=PD(beta)}
                   (Mass(T) - int_T omega^q/q!).

The calibration inequality gives delta(beta)>=0.
On compact X integral currents in the fixed homology class have a
mass-minimizer by Federer-Fleming compactness (provided the class
has at least one integral current representative).
The calibration integral is fixed, so the infimum of defect is
attained. Thus:
    delta(beta)=0
       if and only if
    beta has an effective holomorphic/analytic cycle representative.
On projective X these are algebraic by Chow's theorem.

So the requested existence of an approximate sequence T_n in one
integral class is already equivalent to effectiveness of THAT shift.
This analytic characterization does NOT prove that every rational
Hodge class admits an effective shift.

For primitive r itself, degree integral_X r*h^(d-p)=0.
In the P^2 x P^2 case, since integral_X r^2=3, choose a smooth closed
4-form psi representing r with finite positive comass C>0. Any
integral 4-cycle T representing PD(r) obeys
    Mass(T) >= |int_T psi| / C = 3/C,
whereas int_T omega^2/2 = 0. Hence its calibration defect has
a strictly positive lower bound: delta(r)>=3/C.
The ample SHIFT is mathematically indispensable.

## Exactly what the N-to-geometric construction would require

N-cohomology now supplies genuinely independent rational coordinate
coefficients and integral tower amplitudes. To construct T_n for an
arbitrary X, however, it must provide actual homological realization
of those coefficients in X with ALL of:
  (i) integral rectifiability and closedness of each current,
  (ii) equal INTEGRAL homology class beta for every n,
  (iii) a nonlinear area/mass estimate causing D(T_n)->0,
  (iv) no assumption that beta already has an algebraic representative.

None of these properties is a consequence of the existing finite
digit-window interference decomposition by itself. No unverified
geometric realization or universal current selector has been inserted
as a Lean axiom. Building it unconditionally would complete the
original goal, but has not been accomplished by this execution.

## Evidence summary

GREEN: independent N-coordinate basis and its linear signed mass theorem
(GitHub Actions 38843813429).
WOLFRAM: exact projective intersection calculation and exact
elliptic-graph area-defect Taylor coefficient.
ACTUAL GEOMETRY: explicit integral cycles at fixed class with continuous,
positive, vanishing calibration defects.
UNRESOLVED: the universal fixed-integral-homology current construction
for EVERY rational (p,p) Hodge class on an arbitrary X.


## Continuation: genuine all-X realization on BOTH sides of the integral-current problem

Let X be a smooth projective complex d-fold, 1<=p<=d, q=d-p,
omega an integral Kähler form, and alpha a rational (p,p) Hodge class.
Clear denominators, choose a smooth real d-closed (p,p) representative
eta of m alpha, and take M so large that

    F = eta + M omega^p

is strictly strongly positive. Such M exists on compact X because
omega^p lies in the interior of the strong-positivity cone pointwise
and eta has uniformly bounded coefficients in local unitary frames.
The cohomology class beta=[F]=m alpha + M h^p is integral modulo
torsion after choosing integral ample omega and m.

### A. All-X POSITIVE diffuse realization is unconditional

Define an order-(0) current of real dimension 2q by

    S_F(phi)= integral_X F wedge phi

for smooth test 2q-forms phi. Since dF=0, boundary(S_F)=0.
Strict strong positivity makes S_F a positive (q,q) current.
Its generalized mass with respect to the standard Kähler
calibration c_q=omega^q/q! equals

    Mass(S_F)=S_F(c_q)= integral_X F wedge omega^q/q!.

Thus its positive-current calibration defect is **exactly ZERO**,
and its real homology class is PD(beta).

This construction works for EVERY X,p,alpha and makes no assumption
that alpha is already algebraic. It is a genuine analytic-geometric
realization, not an internal N-channel formal type.

But for 0<=q<d and F nonzero, the mass measure of S_F is smooth
absolutely continuous with respect to real 2d-dimensional volume.
A nonzero integral 2q-current instead has mass concentrated on a
countably 2q-rectifiable set, which has zero 2d-volume.
Consequently S_F is NOT an integral rectifiable current.
One cannot promote this to an integral-current solution by
renaming the diffuse mass an N-wave integer functional.

### B. All-X FIXED-INTEGRAL-HOMOLOGY realization is unconditional

Any class beta in H_{2q}(X,Z), modulo torsion as appropriate,
has a finite integral singular-cycle representative after taking
a smooth triangulation of compact X. Each oriented simplex defines
a Lipschitz rectifiable current with integer multiplicity;
the signed finite sum T_beta is integral, closed because the
simplicial boundary cancels, and represents beta exactly.

This DOES construct at least one integral rectifiable closed current
for beta on EVERY X. It does not make that T_beta positive or
complex-tangent. In particular its absolute calibration defect
can be strictly positive.

### C. Why weakly approximating the diffuse solution DOES NOT work

Suppose integral cycles T_n in the same beta converge as currents
to the NONZERO smooth diffuse S_F, with uniformly bounded masses
and zero boundaries. Federer--Fleming compactness would produce
a flat-convergent subsequence to an integral rectifiable T.
Flat convergence implies weak convergence, whose limit must be S_F.
But S_F is not integral rectifiable (part A). Contradiction.

Thus uniformly-mass-bounded integer cycles cannot approximate
THIS smooth diffuse S_F weakly, EVEN IF beta already has an
entirely different holomorphic representative.
A successful proof must construct integral cycles converging to
a holomorphic chain, NOT round a diffuse smooth solution.

### D. Quantized N-channel semigroup saturation test (Lean source)

New file GSTNIntegralCalibrationGap.lean has a two-channel integer
homology model

    period(a,b)=2a+3b,    mass(a,b)=2|a|+3|b|.

For period 1:
* an integral signed cycle exists: (a,b)=(-1,1);
* a rational positive calibrated cycle exists: (a,b)=(1/2,0);
* but NO nonnegative INTEGER cycle has period 1, because
  2a+3b is zero or >=2 for a,b nonnegative integers;
* every integer signed cycle representing period 1 has defect
  mass-period >=4, attained by (-1,1).

The inequality is an exact all-integer arithmetic theorem,
not a bounded search. It also excludes integer sequences with
fixed period 1 whose defect tends to zero. This is a deliberately
FINITE analogue of an unsaturated semigroup. It is NOT a
counterexample to the geometric Hodge conjecture on any actual X.

It proves that N-cohomology rational coordinate reconstruction,
integer class periods, and even existence of integer signed cycles
do not, alone, imply existence of integer CALIBRATED representatives.
A new theorem about actual projective geometry is mandatory to
bridge the integral saturated-effective-cone gap.

### E. What remains under the ORIGINAL all-X Hodge goal

We have unconditionally constructed the two genuinely geometric
realizations A and B for every target beta but NOT a joint one.
The original all-X claim asks for a sequence of *one and the
same kind of object*: integral rectifiable closed T_n in a fixed
integral class, with

    Mass(T_n) - T_n(omega^q/q!) -> 0.

This is equivalent to an effective analytic cycle in that fixed
class by integral-current compactness/calibration regularity,
not a consequence of the existence of A and B separately.
A mass nonincrease theorem for a class-preserving integral-cycle
flow that actually converges to the calibrated cone would finish
the Hodge target, but no such all-X flow theorem has been derived.
Do NOT register such a theorem as an axiom or count the existence
of the smooth diffuse S_F as an integral-cycle solution.


### F. Genuine projective test: diffuse Kähler current as limit of rational algebraic cycles

Take X=P^2(C) with the normalized Fubini--Study form omega,
and a projective line L. For every g in U(3) the analytic integral
current [g L] represents the SAME integral class h, has mass one
and Kähler calibration defect zero.

Average all such lines against normalized Haar probability measure:

    S(phi) = integral_{U(3)} [g L](phi) dmu(g).

This S is closed, positive, has class h, and is U(3)-invariant.
By symmetry the invariant positive (1,1) current in this class is
exactly the smooth Fubini--Study current omega: S=omega.

Finite empirical averages
    S_n = (1/n) sum_{j=1}^n [g_{n,j} L]
can converge weakly to S by approximating the Haar measure on the
compact group. Each S_n is a RATIONAL-WEIGHT, CALIBRATED algebraic
cycle with exact rational homology class h, uniform mass one,
and defect zero. However the S_n are generally NOT integer
rectifiable currents because the multiplicity on each distinct
line is 1/n.

There IS a perfectly valid integral calibrated representative,
namely the fixed line [L], since the Hodge conjecture holds
trivially in this case. Yet there cannot be a sequence of
INTEGRAL closed currents of uniformly bounded mass converging
weakly to the DIFFERENT smooth diffuse S=omega; integer compactness
would force omega itself to be integral rectifiable.

This explicit genuine projective example distinguishes three
notions that cannot be merged by an N-cohomology coefficient choice:

    rational effective algebraic cycles -> diffuse positive currents
    existence of an integer calibrated cycle in the SAME class
    approximation of a PARTICULAR diffuse positive current by
          integer cycles in the SAME class

Even in a class where an integer calibrated cycle exists, the
third property fails. The correct universal construction must
find a discrete calibrated representative, not approximate the
diffuse positive current itself.


### G. Geometric ample-complement construction for every ALREADY algebraic cycle

This checks that requiring *some* ample shift of a rational
algebraic class to be effective is a legitimate geometric target,
rather than an inadvertently stronger positivity conjecture.

Fix L very ample with h=c1(L). Let Z be a genuine irreducible
codimension-p subvariety of smooth projective X.
For sufficiently large N, the sheaf I_Z tensor L^N is globally
generated. Choose p general hypersurface sections vanishing on Z.
At Z's generic point, its ideal is the maximal ideal of the
p-dimensional regular local ring O_{X,eta_Z}; p general local
sections have independent linear parts and cut Z with generic
intersection multiplicity exactly one. By generic choices,
their other codimension-p intersection components are effective.
The Chow intersection formula then gives

    N^p h^p = [Z] + [W]       with W effective codimension p.

Equivalently, the *algebraic* class N^p h^p-[Z] has an explicit
effective representative W. For a finite signed algebraic cycle
A = A_plus - sum_i n_i [Z_i] with n_i positive integers, perform
this hypersurface construction separately for each Z_i.
Then

    A + (sum_i n_i N_i^p) h^p
       = A_plus + sum_i n_i W_i

is effective, and it is an explicit finite algebraic cycle.
Clear rational denominators beforehand. This proof is from
genuine projective complete-intersection geometry, not
N-wave rank labels or matrix-unit transport.

Thus ANY class already in the algebraic Chow image has
a sufficiently large effective integral ample shift;
such a shift has a calibrated integral holomorphic current.
Conversely, for a class alpha NOT YET known algebraic, an
effective integral shift m alpha + M h^p would immediately make
alpha algebraic after subtracting M h^p and dividing by m.

This identifies the exact status of the proposed direct
fixed-homology current attack: the existence of the shift
together with arbitrarily small integral calibration defect
is a **sufficient and (using the ample-complement construction)
necessary** geometric realization condition for rational
Hodge algebraicity. The construction of W_i assumes the source
Z_i is ALREADY algebraic; using it on a hypothetical missing
Hodge class would be circular.

No formal Lean implementation of the full Chow moving/Bertini
intersection machinery is claimed in this research record.
