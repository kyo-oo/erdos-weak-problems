# Quantitative fixed-homology Wirtinger calibration gap on a genuine projective abelian surface
2026-10-16 · Mathbox adversarial geometric test · original all-Hodge-class objective preserved

## Why this test is decisive

The new arbitrary-X K-theory degeneracy-locus construction creates
closed INTEGRAL currents in a shifted class even when the initial
rational class is NOT of Hodge type. Therefore no proof relying only
on that construction, positive ample shift and finite GST N-channel
arithmetic can universally make its currents Kähler calibrated:
it would incorrectly make NON-HODGE classes algebraic.

Here is a genuine projective geometric instance with a rigorous
POSITIVE LOWER BOUND ON ABSOLUTE CALIBRATION DEFECT for EVERY
integral current in the SAME fixed integral homology class.
It forces any future successful Hodge-specific route to use
the (p,p) condition in the tangent-plane geometry, not only
to check cohomology labels.

## Actual variety and classes

Let E=C/(Z+iZ), a projective elliptic curve. Set X=E x E,
with real periodic coordinates (x,y,u,v), complex coordinates
z1=x+iy,z2=u+iv and flat product Kähler form

    omega=dx^dy+du^dv.

The orientation is vol=dx^dy^du^dv. Define an INTEGRAL
non-Hodge real 2-class

    a=dx^du-dy^dv=Re(dz1^dz2).

Its nonzero (2,0)+(0,2) component makes a not type (1,1).

For EACH fixed integer M>=0 set

    beta_M = M[omega]+[a] in H^2(X,Z).

Because omega has type (1,1) and a is not (1,1),
beta_M is NOT (1,1) for ANY integer M.

## Exact cohomological pairings

Exterior algebra in H^*(E x E,Z) gives

    integral_X omega^2 = 2,
    integral_X omega^a = 0,
    integral_X a^2 = 2.

Thus any closed integer rectifiable 2-cycle T representing
PD(beta_M) must obey

    T(omega)= integral_X beta_M^omega=2M,
    T(a)= integral_X beta_M^a=2.

Wolfram exact antisymmetric-matrix wedge arithmetic independently
returned the tuple {2,0,2}.

## Wirtinger tangent-plane quantitative rigidity

Let xi be ANY oriented unit simple 2-vector in R^4.
Write

    kappa = omega(xi),
    sigma = a(xi),
    tau = (dx^dv+dy^du)(xi).

The three 2-forms omega,a,dx^dv+dy^du form an orthogonal
self-dual basis (each norm sqrt(2)); because xi is simple
of unit norm its self-dual part has norm 1/sqrt(2).
Hence the exact identity

    kappa^2+sigma^2+tau^2=1.

Since -1<=kappa<=1,

    |a(xi)|^2=sigma^2<=1-kappa^2<=2(1-kappa).

For arbitrary oriented integral rectifiable current T,
integrate against its MASS measure mu_T. The real Kähler
calibration is omega on 2-planes, so

    D(T)=Mass(T)-T(omega)
        =integral (1-kappa) dmu_T >=0.

Cauchy--Schwarz yields

  |T(a)| <= integral |a(xi)| dmu_T
         <= sqrt(2 D(T) Mass(T)).

For T representing beta_M, |T(a)|=2 and
Mass(T)=2M+D(T). Therefore

    4 <= 2 D(T)(2M+D(T)),

hence the EXACT POSITIVE LOWER BOUND

    D(T) >= sqrt(M^2+2)-M >0                       (*)

for EVERY integral cycle in fixed beta_M.

No unproved compactness, flow, or analytic regularity result is
used for this inequality. In fact (*) holds for ANY rectifiable
real-multiplicity cycle of class beta_M with finite mass.

Wolfram gave the lower bounds for M=0..5:
{sqrt(2),sqrt(3)-1,sqrt(6)-2,sqrt(11)-3,
 sqrt(18)-4,sqrt(27)-5};
approx {1.41421,0.73205,0.44949,0.31662,
0.24264,0.19615}.

### The all-X original target is NOT contradicted

Here a is deliberately NOT a (1,1) Hodge class. For actual
rational Hodge alpha the matching non-Hodge probe pairing
T(a) vanishes; the lower-bound argument therefore gives
no contradiction to the user's Hodge claim.

The test proves the precise mathematical need for a NEW
Hodge-specific geometric input beyond stable complex
topological normal bundles and finite GST N-waves.

### Even arbitrary shifts cannot repair a non-Hodge component

The lower bound is positive for EACH FIXED M. As M->infinity,
sqrt(M^2+2)-M ->0, but then beta_M changes with M.
That limit is NOT a sequence in one fixed homology class.
This is the same absolute-versus-relative defect distinction
that earlier attempts to subtract hyperplane cycles missed.

## Source and evidence boundaries

1. X=E x E is a genuine projective complex abelian surface.
2. Pairings are exact integral cohomology wedge arithmetic,
   Wolfram-checked.
3. Unit-plane identity is a four-dimensional pointwise
   linear algebra theorem, proved above from self-dual
   decomposition; the Cauchy inequality is elementary.
4. The lower bound is a universal statement about all
   currents in these *non-Hodge* classes, NOT a counterexample
   to the Hodge conjecture.
5. The user's all-X rational Hodge fixed-homology integral
   calibration sequence remains UNPROVED. No new goal,
   axiom or assumed algebro-geometric realization is inserted.
