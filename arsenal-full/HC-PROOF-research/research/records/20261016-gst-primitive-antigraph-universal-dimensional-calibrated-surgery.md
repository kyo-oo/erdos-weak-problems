# GST middle-primitive antigraph surgery: an actual all-dimensional complex-geometric construction
2026-10-16 · Mathbox research · original all-X Hodge goal unchanged

## A genuine integral-homology preserving calibrated replacement for every P^n x P^n

Fix n>=1, the smooth projective complex 2n-fold
X_n=P^n_C x P^n_C, and factor hyperplane classes a,b, with
integral cohomology Z[a,b]/(a^(n+1),b^(n+1)).
Let h=a+b, and use the normalized product Fubini--Study metric.

Let c:P^n→P^n be the antiholomorphic complex-conjugation
isometry, with c*h=-h. Let Gamma be its smoothly oriented
graph, and Delta the holomorphic diagonal. For 0<=j<=n,
let Y_j be a holomorphic product of linear projective subspaces,
of dimensions j and n-j respectively, so
    PD(Y_j)=a^(n-j)b^j.

**The replacement is an exact INTEGER homology identity:**

    [Gamma]+[Delta] =
       2 sum_(0<=j<=n, n-j even) [Y_j].

### 1. Proof of the integral identity and its GST primitive meaning

For any j, pair the graph class with a^j b^(n-j):

   integral_Gamma a^j b^(n-j)
      = integral_Pn h^j(c*h)^(n-j) = (-1)^(n-j).

Thus the full integral PD classes are

  PD(Gamma)=sum_(j=0)^n (-1)^(n-j)a^(n-j)b^j,
  PD(Delta)=sum_(j=0)^n a^(n-j)b^j.

The first polynomial is exactly the preexisting GST
universal self-product primitive polynomial with SWAPPED
variables: GSTUniversalSelfProductPrimitive.universalPrimitive b a n.
Its product with a+b vanishes by the existing GST telescope and
dimension-truncation theorem. So the antigraph is a genuine
nonzero middle primitive carrier.

Add coefficients in Z, not merely Q:
  1+(-1)^(n-j)=2 if n-j is even, 0 otherwise.

The resulting class is 2sum_(n-j even) a^(n-j)b^j.
Each monomial is the integral class of effective Y_j.
Since the integral cohomology is torsionfree, PD equality gives
identical INTEGRAL homology classes. Consequently the difference
is the boundary of some INTEGRAL (2n+1)-chain B:
  ∂B=[Gamma]+[Delta]-2sum_(n-j even)[Y_j].

This is a genuine homology-preserving integer boundary surgery,
not only a rational GST wave-coordinate operation.

The universal polynomial identity, for ANY commutative ring,
is formalized in GSTUniversalAntigraphDiagonalSurgery.lean,
with explicit n=1 and n=2 tests. Its dedicated Actions workflow
is gst-universal-antigraph-holomorphic-surgery.yml. The
analytic projective-geometry interpretation is proved here,
not claimed to be formalized in Lean.

### 2. Exact geometric MASS and Kähler CALIBRATION proof

Pullback of the ambient Kähler form to Gamma vanishes:
  omega_total|Gamma = omega+c*omega=0.
Thus Gamma is Lagrangian and has calibration period zero.

Both graphs Gamma and Delta have induced Riemannian metric 2g,
where g is Fubini--Study on P^n. Normalize
  volume(P^n)= integral h^n/n! = 1/n!.
Hence each graph has Riemannian volume 2^n/n!.

Gamma and Delta intersect only on the real P^n fixed locus,
a subset of real dimension n < 2n, so their overlap has
zero 2n-dimensional area. Their sum has
  Mass(bad)=2^(n+1)/n!,
  Period(bad)=2^n/n!,
  D(bad)=2^n/n! >0.

Each Y_j is positive holomorphic, hence calibrated, and its
Kähler mass is exactly 1/(j!(n-j)!).
The parity binomial identity for n>=1 gives
  sum_(n-j even) binom(n,j)=2^(n-1),
so the positive integer target has
  Mass(good)
     = 2 sum_(n-j even)1/(j!(n-j)!)
     = 2^n/n!,
  Period(good)=Mass(good),
  D(good)=0.

The ENTIRE original positive absolute defect 2^n/n!
is eliminated, without changing integral homology.
Choose the constant sequence T_k=T_good for this fixed class.

### 3. Nontrivial codimension-two middle primitive case

On X=P²xP²:
  PD(Gamma)=a²-ab+b²;
  (a+b)PD(Gamma)=0.
It is the middle primitive anti-holomorphic graph class.
The diagonal is PD(Delta)=a²+ab+b².
Hence
  Gamma+Delta homologous to 2(P²xpoint)+2(pointxP²).

The actual integer 4-current before surgery has
  Mass=4, Period=2, defect=2.
The holomorphic replacement has
  Mass=2, Period=2, defect=0.
Both represent exactly the SAME integral middle homology class.
This is a higher-codimension geometric surgery, not a
mere P¹-curve arithmetic example.

### 4. Exact independent computation

Wolfram evaluated the polynomial difference
  diag+anti-2sum_(n-j even) a^(n-j)b^j
for ALL n=1,...,9; results were all exactly zero.
It separately evaluated the rational mass sum
  2sum_(n-j even) 1/(j!(n-j)!)
versus 2^n/n! for n=1,...,9; all equalities held exactly.
The proof for arbitrary n is the preceding parity cancellation
and even-binomial identity, not extrapolation from the nine tests.

### 5. Transport through the rest of the GST arsenal

GSTNPrimitiveGeometricSurgery gives the base n=1 integer boundary
relation. GSTUniversalSelfProductPrimitive identifies the full
alternating primitive polynomial on product hyperplane directions.
GSTUniversalAntigraphDiagonalSurgery constructs its all-n
effective homology decomposition.

GSTUniversalExternalProductCurrentSurgery shows that tensoring
the n=1 integer surgery with ANY primitive current S on arbitrary X
gives a homology-preserving current surgery on XxP¹xP¹ but leaves
  D(output)=2D(S).
So this *functorial* extension DOES NOT eliminate the primitive
defect of an arbitrary input S.

GSTComplexTangentProjectionChainObstruction proves a different
shortcut also fails: a pointwise J-invariant projection of a closed
exact form on the projective torus E x E need not be closed; the
projected simple integer tangent bivector is nonsimple/fractional.
A valid all-X GST operation must use nonlocal integral fillings.

Existing GST realized algebraic correspondences, finite N-waves,
world recoordination and ghost annihilator operators act on
rational Hodge/coefficient or already-algebraic states; none
by itself manufactures a new integer homology relation on the
original arbitrary X with a calibrated output.

## Why the original goal remains outstanding

An arbitrary smooth projective X need not have a self-map
c:X→X that is anti-holomorphic, anti-symplectic and an isometry,
nor an effective projective-product basis spanning every rational
primitive (p,p) Hodge class on X. Existence of the above surgery
on P^n x P^n does NOT furnish a holomorphic cycle for a
hypothetically nonalgebraic primitive class on a different X.

The user's EXACT target would require, for every primitive
rational Hodge alpha on arbitrary X, a nonlocal integral filling
B_n whose replacement S+∂B_n has fixed class
m alpha+M h^p and absolute calibration defect tending to zero.
That general construction is still UNPROVED.

The all-n antigraph theorem IS a genuine infinite-family
mathematical and geometric result and an executable model for
what the universal operation would have to do, not a false
assertion that the rational Hodge conjecture is solved.


## Attempted all-X extension through the complex-conjugate variety

For EVERY smooth projective complex X, the conjugate projective
variety Xbar exists. The identity on the underlying real smooth
manifold defines an ANTIHOLOMORPHIC map c:X→Xbar.
Equip X and Xbar with paired Kähler forms omega and omegaBar
so c*omegaBar=-omega. Then the real oriented graph
   Gamma_c ⊂ X x Xbar
is a genuine LAGRANGIAN MIDDLE-DIMENSIONAL integral cycle,
since (omega+omegaBar)|Gamma_c=0.

This supplies a universal primitive-geometry *input* on
X x Xbar, even when X has no real structure. It is a real
geometric construction, not a GST invented morphism.

The crucial P^n×P^n surgery also needed a HOLomorphic diagonal
   Delta ⊂ X×X
and a positive algebraic basis of the middle Künneth class.
On X×Xbar there is in general NO natural holomorphic
diagonal: the identity X→Xbar is antiholomorphic, not
holomorphic. An arbitrary X need not be holomorphically
isomorphic to its complex conjugate Xbar.

Consequently the graph construction on X×Xbar does NOT
automatically produce the needed compensating holomorphic
middle correspondence, nor a decomposition into effective
cycles. The P^n construction relied on a special
antiholomorphic SELF-isometry and a fully algebraic
product-Künneth basis.

This tests the first genuinely all-variety extension of
the GST antigraph surgery. The primitive real input is
available on every X×Xbar; the essential algebraic
compensator/replacement is NOT universally constructed.
No assertion about primitive Hodge completeness follows.


## Upgrade II: all FINITE cellular/Schubert basis geometry, beyond P^n x P^n

The index set {0,...,n} in projective space is incidental. Suppose X
is a smooth complex projective variety for which:
  (1) H*(X,Z) is torsionfree, concentrated in EVEN degrees and has
      a finite integral homogeneous Kunneth/Poincare-dual basis;
  (2) the diagonal PD has a decomposition
       [Delta_X] = sum_i [A_i] x [B_i]
      with EACH product A_i x B_i an EFFECTIVE algebraic cycle,
      and coefficient exactly +1;
  (3) there is an antiholomorphic isometric involution
      c:X->X which is anti-symplectic c*omega=-omega,
      and acts on each H^(2k)(X,Z) as (-1)^k.

For each factor term let m_i be the half-degree on the FIRST
cohomology factor A_i (equivalently d minus the half-degree on
the second cohomology factor B_i). Pairing with the graph shows its integral PD equals
   [Gamma_c] = sum_i (-1)^(m_i)[A_i] x [B_i]
(up to convention on identifying the two Poincare-dual factors:
the parity includes the ambient orientation sign (-1)^d
and therefore equals the half-degree of the FIRST factor).

Therefore the **EXACT INTEGER HOMOLOGY RELATION** is
   [Gamma_c]+[Delta_X]
       =2 sum_{i: m_i even} [A_i] x [B_i].

Each right-hand term is effective holomorphic. The graph is
Lagrangian because omega+c*omega=0. Thus the right side is a
genuine zero-defect replacement of the left side while preserving
the full integral homology class. Its calibration defect drops by
the full strictly positive mass of Gamma_c, provided dim_C X>0
and the two graph currents do not overlap in positive area.
(If c has a fixed locus that has full 2d-dimensional measure,
the mass-overlap assumption must be checked separately.)

These are explicit geometric hypotheses, NOT an assertion they
hold on every projective variety. They hold on projective spaces,
and the Schubert/opposite-Schubert dual bases provide a natural
family of further test cases on split type-A complete flag
varieties and closely related cellular homogeneous spaces.
Verifying the antiholomorphic and Kunneth orientation data
for each such example is a separate geometry obligation.

New formalized theorems are appended to the EXISTING Lean module
GSTUniversalAntigraphDiagonalSurgery.lean:
  full_cellular_antigraph_surgery
  full_cellular_opposite_surgery
  full_cellular_integral_parity_resolution.

Each theorem is universal in arbitrary FINTYPE index and
any commutative coefficient ring, so the original
n-dimensional range is no longer a limitation of the algebraic
coefficient surgery.

Importantly, even all these cellular enhancements do not
construct calibrated primitive carriers for NONCELLULAR X
or for Hodge classes outside algebraic span; the
original rational Hodge conjecture remains unresolved.
