# Mathbox 2026-10-16: GST integer boundary surgery aimed at the universal Hodge geometric replacement
Checkpoint base 9f0c4943f612990eb48bfb77095e4222044b2e63.
Original exact goal: for EVERY smooth projective complex X, EVERY rational (p,p) Hodge class alpha, produce FIXED m>0,M>=0 and closed integral rectifiable currents T_n with [T_n]=PD(m alpha+M h^p) and absolute Wirtinger defect D(T_n)->0. This is equivalent to rational Hodge algebraicity; this route does NOT claim to prove it.

## Existing GST mechanisms genuinely inspected

1. waves/GSTNCohomology.lean, V2, V3: finite tower-hole/window readouts, independent rational coordinates. **These objects are not topological singular chains** and have no integral boundary operator with ∂²=0.
2. GSTNAllChannelAmpleSaturation.lean (CI success 38854324888): all-N ample shifts yield zero "calibration" in an INTEGER-WEIGHTED CHANNEL model. The channel mass is not the current mass on arbitrary X. Its vector coordinates do not carry a cycle-class map with target every Hodge direction.
3. GSTClassicalHodgeProjectivePointTransport.lean: actual scheme pushforward on already algebraic codimension-p point cycles. No action on a nonalgebraic primitive rectifiable current.
4. GSTClassicalHodgeProjectiveDefectTransport.lean: transports a *fibered cycle-class defect* (not Kähler mass minus ω-period), preserves the zero-defect property for suitable projective self-transports, and does NOT construct a method shrinking a positive Kähler calibration defect.
5. GSTClassicalHodgeNativeOperatorCohomologyRealization.lean: the ambient operator is descended from the existing algebraic image, using a rational projection from ambient Betti space onto that image. Under kernel stability it maps existing cycle classes into existing cycle classes. No inverse for an arbitrary Hodge class appears from this extension.
6. GSTClassicalHodgeGeometryFirstGlobalPropagation.lean: the full-Hodge conclusion is conditional on GeometryFirstGlobalPropagation, including native Lefschetz transport and a GeometryFirstTwoGenerator for every Hodge basis pair. These are not constructed on arbitrary X by the inspected file.
7. GSTK3GeometricSourceToArbitraryX.lean: actual K3 source cycles transport to arbitrary X if a Hodge/Chow retract is supplied. The universal existence of such a retract is not derived.

Conclusion: GST is genuinely being used here, but its existing operators do NOT already implement the requested homology-preserving, mass-defect-decreasing geometric current surgery. Creating a meaningful chain-level transport is the active work, not pretending that the earlier fibered defect is Wirtinger calibration.

## GST new geometry: integer N-current boundary surgery

File GSTNPrimitiveGeometricSurgery.lean: an explicit rationally honest, integer-multiplicity model linked to ACTUAL geometric curves on X=P1×P1.

Let A denote the antiholomorphic antipodal graph Γ, D the holomorphic diagonal Δ, F the holomorphic ruling fiber (P1×{pt}). Their integral homology classes, areas, and Kähler periods are:

     current        PD in (A_h,B_h)   mass     ω-period
     Γ               B_h-A_h            2           0
     Δ               A_h+B_h            2           2
     F               B_h                1           1

A geometric cycle with integer multiplicities (a,b,c) in these three directions has integral H_2 coordinates
   homology(a,b,c)=(-a+b, a+b+c),
period
   P(a,b,c)=2b+c,
and for generic distinct sheets (no 2-dimensional overlap)
   Mass(a,b,c)=2|a|+2|b|+|c|.

The fundamental integral geometric relation is

   [Γ]+[Δ]=2[F]  in H_2(X,Z).

Hence, for any integer k, the *actual homology-preserving surgery* is

    R_k(a,b,c)=(a-k,b-k,c+2k).

Exact integer identities:
   homology(R_k T)=homology(T),
   P(R_k T)=P(T).

For nonnegative sheets a,b,c and 0≤k≤min(a,b):
   Mass(R_k T)=Mass(T)-2k,
   D(R_k T)=D(T)-2k.

In particular, if 0≤a≤b and c≥0, choosing k=a eliminates ALL anti-graph contributions:
   D(R_a T)=0
   homology(R_a T)=homology(T).

The concrete replacement is
    T_bad=(1,1,0),   Mass=4, P=2, D=2;
    T_good=(0,0,2),  Mass=2, P=2, D=0.

Both represent PD(2B_h). The output is the sum of two actual positively oriented holomorphic ruling curves, not a symbolic mass coincidence. Since the homology difference is ZERO IN INTEGRAL H_2, it is the boundary of an integral singular 3-chain B. That filling is not explicitly constructed as a current in Lean; only the homology and numerical effect are formalized.

### What the result DOES and DOES NOT do

This is a FAMILY of homology-preserving zero-defect surgeries (not just one triple). It supplies an actual geometric realization for every nonnegative configuration with enough diagonal sheets to cancel anti-graphs on P1×P1. It does NOT supply an analogous null-homologous surgery relation on arbitrary smooth projective X, and no arbitrary nonalgebraic alpha is realized by an algebraic source in the module.

## New all-X positive replacement: global integral mass minimization

Given a compact Riemannian smooth projective X with fixed integral 2q-homology class beta, the set of closed integral rectifiable currents representing beta is nonempty by triangulation. The standard integral-current compactness and homological persistence argument supplies an AREA MINIMIZER T_beta within this single integer homology class.

For every starting primitive-plus-ample current S in beta,
   [T_beta]=[S]=beta,
   Mass(T_beta)≤Mass(S).
Because c=ω^q/q! is closed, the calibration period T(c) depends only on beta, so
   D(T_beta)≤D(S).

This is a genuine all-X, integral-class-preserving, globally mass-nonincreasing GEOMETRIC REPLACEMENT. Unlike a local mean-curvature flow, it may jump through nonlocal fillings and cannot be blocked solely by a stationary initial varifold.

Define the fundamental all-X geometric "integrality gap":
   gamma_X(beta)=Mass(T_beta)-<beta,c>≥0.

Every minimizing current has D=gamma_X(beta). It is calibrated (and algebraic, by calibrated-holomorphic regularity and Chow) IFF gamma_X(beta)=0.

Rational Hodge type supplies a smooth diffuse POSITIVE current with the SAME *real* class whose mass equals <beta,c>; it does NOT imply the integer integral minimizer reaches that real relaxed value. The strict inequality gamma_X(beta)>0 remains logically possible from the present arguments. No theorem in the inspected GST modules excludes it for every Hodge beta.

This yields a direct absolute-defect research target: prove gamma_X(m alpha+M h^p)=0 for some fixed m,M by a new Hodge-specific geometric estimate. Proving precisely that would establish the rational Hodge conjecture.

### Universal monotonicity across ample shifts (new exact property)

Let Z_h be a positive holomorphic complete intersection of p hyperplanes in X, giving a closed integral calibrated current with [Z_h]=PD(h^p). For a fixed m and beta_M=m alpha+M h^p, define gamma_M=gamma_X(beta_M).

For every integer N≥0 and T in beta_M,
   T+N Z_h lies in beta_{M+N}, and by mass subadditivity
   D(T+N Z_h) ≤ D(T)+D(N Z_h)=D(T).

Taking infima:
   0 ≤ gamma_{M+N} ≤ gamma_M.

So the genuine integral absolute-defect optimum is MONOTONE NONINCREASING as the ample-shift coefficient grows. For the P1×P1 example alpha=B_h-A_h, gamma_0>0 (pure primitive has zero ample degree but is nonzero), while gamma_1=0 because beta_1=2B_h is represented by 2F.

**Important quantifier warning:** monotone nonincrease does NOT imply that gamma_M=0 for any finite M. Even gamma_M→0 as M→∞ would be insufficient for a sequence in ONE FIXED homology class. This is a *stronger constraint to exploit*, not the missing universal Hodge theorem itself.

## Three actual routes tested against decisive failures

A. Native GST projective transport, correspondences, matrix units:
   maps existing algebraic cycles to existing algebraic cycles;
   cannot create a primitive class missing from the native image.
   Inspect GSTClassicalHodgeNativeOperatorCohomologyRealization.

B. Local geometric mean curvature descent:
   earlier exact E×E example contains a stationary noncalibrated
   integral varifold IN AN AMPLE HODGE CLASS. Pure MCF can stop at
   the wrong stationary point. Needs NONLOCAL topology-changing surgery.

C. Global integral-current minimization + GST integer boundary surgery:
   fully valid for arbitrary X as homology-preserving replacement,
   with explicit strict zero-defect geometry for a FAMILY on P1×P1.
   Remaining precise gap is independent Hodge-specific proof
   that integral minimizer has gamma_X(beta)=0 for some shift.
   This is NOT yet settled.

## Active next geometric mechanism (not a claim of proof)

Find, for arbitrary primitive middle rational Hodge alpha, a certificate
of a NULL-HOMOLOGOUS INTEGRAL (2q+1)-dimensional surgery B with
    [T+∂B]=[T]=beta,
    Mass(T+∂B) ≤ Mass(T) - eta(T),
where eta(T)>0 for any noncalibrated globally minimizing current
in the target Hodge class, WITHOUT importing algebraicity of alpha.
The existence of this nonlocal move is the first genuinely unproved
geometric implication. A naive uniform descent lemma is inconsistent
with the non-Hodge Kähler-angle lower-bound examples, so the proof
must explicitly use the Hodge condition on alpha.

Before promotion to theorem, reconstruct the actual B, its integer
multiplicities, homology and lower mass against each tangent-plane
angle. DO NOT add a "surgery packet" whose fields already assert
the all-X statement and then claim victory when Lean compiles.

### Verification

N independent rank, integer ample saturation and earlier relative
cohomology modules have green CI at their pinned runs. New
GSTNPrimitiveGeometricSurgery.lean and dedicated CI run
38865178608 were submitted in this turn; their final verification
status must be rechecked before labeling the new Lean theorem GREEN.

**Original all-X rational Hodge fixed-class calibrated-current theorem is not yet proved.**


## Executed finite chain-complex global optimizer

Executable: research/computations/gst_integer_boundary_surgery.py.
The exact source input is an INTEGRAL chain complex with:
  A : C_(2q) -> C_(2q-1), B : C_(2q+1) -> C_(2q),
  A B=0, and an integer homology-signature H with H B=0.
Starting chain z0 has A z0=0.
The Kähler period p obeys p B=0 and geometric face masses w_i
satisfy w_i>=|p_i|>=(nonnegative bound).

Every homologous replacement in the same chosen finite complex is
z=z0+B u with INTEGER u, not merely rational coordinates or a
same-H-signature approximation. The algorithm searches exactly this
integer lattice using Hermite normal forms. Since current mass
  mass(z)=sum_i w_i |z_i|
is positive and the starting mass is finite, every mass-nonincreasing
candidate has |z_i|<=mass(z0)/w_i. There are finitely many such integer
vectors, so exhaustive search and minimizing mass finds the TRUE GLOBAL
MINIMUM within that fixed finite cellular current model; no unproved
continuous numerical tolerance enters its correctness.

Executed finite tests in Python/SymPy:

* P1×P1 geometric packet: A=0, B=(-1,-1,2)^T,
  H=[[-1,1,0],[1,1,1]], w=(2,2,1), p=(0,2,1),
  z0=(1,1,0). Exhaustively scanned 225 integer vectors allowed
  by the initial mass bound; precisely 2 are homologous with
  mass no greater than starting mass. Unique minimum
  z=(0,0,2), original (mass,period,D)=(4,2,2),
  replacement (2,2,0).
* Two-channel N-lattice: A=0, B=(-3,2)^T,
  H=(2,3), w=p=(2,3), z0=(-1,1).
  Exhaustively scanned 15 vectors; exactly one remained in the
  fixed integer class within the initial mass bound. It has
  (mass,period,D)=(5,1,4), so NO zero-defect replacement
  exists in this integer chain complex.

The scripts are a full finite-algorithm proof of EXACT minimum
once a geometric triangulation/chain complex and its integral
boundary maps are supplied. On a compact smooth projective X,
such finite triangulations exist. But proving that the minima
along refinements converge to ZERO for every rational Hodge
class is the SAME unsolved all-X geometric Hodge obligation,
not a consequence of exhaustive finite optimization alone.

## Last verified Lean CI

First run 38865178608 failed only because abs normalization in
surgery_mass_exact_drop left a proof goal.
Repair commit 7b3a0fef87165045624e6e090d99b6cda6acafa7
explicitly rewrote the six absolute values with established
nonnegativity facts.
Replacement Lean GitHub Actions run 38865745138 completed SUCCESS.
The compiled theorem includes exact integer homology preservation,
exact mass and defect drop, and zero-defect end state for the
positive integer surgery family on P1×P1.


## New all-X integral boundary regularized geometric replacement (nonlocal, no stationary traps)

The earlier existence of a mass minimizer was nonconstructive and did
not provide a mathematically explicit surgery functional. Here is a
TRUE global all-X replacement mechanism with ACTUAL integer boundary
currents and a penalty whose minimizers exist.

Let (X,g,ω) be ANY smooth projective compact Kähler d-fold.
Let q=d-p and let T0 be an arbitrary CLOSED INTEGRAL rectifiable
2q-current representing a fixed INTEGRAL homology class beta.
Let c_q=ω^q/q! be its Kähler calibration.

For ANY λ>0 define on finite-mass integral (2q+1)-currents B:

     E_λ(B) = Mass(T0+∂B) + λ Mass(B).

Set B_λ to be a GLOBAL minimizer over the complete class of integer
rectifiable currents B. Define the **GST nonlocal integer surgery**

     R_λ(T0) = T0 + ∂B_λ.

### Step 1: existence of B_λ for EVERY X and EVERY T0

The competitor B=0 gives E_λ<=Mass(T0). Let B_n be a minimizing
sequence with energies <=Mass(T0)+1. Then

     Mass(B_n) <= [Mass(T0)+1]/λ;

also by the triangle inequality,

     Mass(∂B_n)
        <=Mass(T0+∂B_n)+Mass(T0)
        <=2 Mass(T0)+1.

Both mass and boundary mass of the INTEGRAL fillings B_n are
uniformly bounded. Since X is compact, Federer--Fleming integral
current compactness produces a flat-convergent subsequence with
integral limit B_λ. Lower semicontinuity of both terms gives a
GLOBAL minimizer. No holomorphic-cycle premise is required.

### Step 2: exact integral homology and defect nonincrease

R_λ(T0)=T0+∂B_λ is integral, closed, and differs from T0 by an
ACTUAL integer boundary. Therefore it preserves the ORIGINAL
integral homology class beta, not an integer multiple of beta.
The calibration period is unchanged because dc_q=0:

     R_λ(T0)(c_q)=T0(c_q)=P_beta.

Optimality against B=0 gives

     Mass(R_λ(T0)) + λ Mass(B_λ) <= Mass(T0),

hence

     D(R_λ(T0))
      <= D(T0) - λ Mass(B_λ) <=D(T0).

This is a rigorous, quantitative, all-X and homology-preserving
surgery replacement that escapes local stationarity traps because
the minimization ranges over ALL integer fillings B, not only
infinitesimal deformations of T0.

### Step 3: λ->0 convergence to the OPTIMAL integer-current defect

Write
     m_int(beta)=inf{Mass(T): T closed integral, [T]=beta}.

For every competing integral T' in beta, integral homology
equality ensures T'-T0=∂B' for some finite-mass integral filling
B' (using the standard equivalence between integral currents
and singular integral homology on a smooth compact manifold).
Minimizer optimality yields

    m_int(beta) <= Mass(R_λ(T0))
       <= Mass(T') + λ Mass(B').

Taking λ->0, then the infimum over T', gives

    lim_{λ->0} Mass(R_λ(T0)) = m_int(beta),

and since the Kähler calibration period is fixed,

    lim_{λ->0} D(R_λ(T0))
      = gamma_X(beta)
      := m_int(beta)-P_beta >=0.

All replacements belong to ONE FIXED integral class beta,
for every λ. The bounded output masses allow integral flat
subsequence limits as λ->0, which are global mass minimizers.

### Step 4: exact remaining Hodge-specific question

For beta=m alpha+M h^p with rational Hodge alpha, the real
relaxation contains a smooth positive calibrated (p,p) current
of mass P_beta. However the integer optimum m_int(beta) could
be STRICTLY LARGER than that real optimum based on existing
arguments. This is the INTEGRAL CALIBRATION GAP gamma_X(beta).

If one proves gamma_X(beta)=0 for some fixed m,M, the above
CONSTRUCTED T_λ is the user-requested SAME-CLASS integer
sequence with D->0. The integral compactness limit is then
a positive holomorphic chain and the original Hodge class
is algebraic. None of the currently inspected GST laws
implies gamma_X(beta)=0 unconditionally in arbitrary
intermediate codimension, and we have NOT pretended otherwise.

The rigorous all-X statement ESTABLISHED by this route is:
     A closed integer, homology-preserving replacement
     exists for every λ>0; it strictly improves mass unless
     B_λ=0 or improvement is balanced by filling penalty;
     its defect converges exactly to the optimal integral
     calibration gap gamma_X(beta).
It does NOT establish universal vanishing of gamma_X.

### Step 5: exact finite GST surgery instantiation

For the P1×P1 packet T0=(1,1,0) and integer boundary
B(k)=(-k,-k,2k), take filling penalty Mass(B_k)=|k|
in normalized arbitrary units. The exact finite objective is

     E_λ(k) = 4|1-k|+2|k|+λ|k|.

k=0 gives 4, while k=1 gives 2+λ. For all 0<λ<2,
k=1 is globally optimal among integer k, giving actual
integral calibrated replacement (0,0,2) and D=0.

For the unsaturated (2,3) N-integer model with original period
one, NO integer k changes the positive minimum D=4 into zero.
These two exact models distinguish a genuine geometric
boundary surgery from a merely abstract positivity claim.

### Source evidence status

The analytic compactness, lower semicontinuity and current/singular
homology comparison are standard GMT results and are used here
in their stated forms; this execution did not retrieve and pin
a primary-source PDF, so the external-source leaf has not been
independently source-authenticated in the repository. The
integer P1×P1 arithmetic is Lean kernel checked in workflow
38865745138, and the finite exhaustive solver lives in
research/computations/gst_integer_boundary_surgery.py.


## Verified multi-file GST strengthening checkpoint (2026-10-16)

This section records ACTUAL changes to FOUR PREEXISTING Lean source files.
Source baseline: 432b479a41adfd4dfb4135eb4de75c6f5fda52b8.
Verified source revision: cbe9ecd7c6295196885127507f53f4935f8f9626.
No new Lean theorem files created. The files and associated existing CI
workflow definitions were edited in place.

1. GSTNPrimitiveGeometricSurgery.lean
   NEW theorem surgery_orbit_complete:
      homology T = homology U
        iff exists k in Z with surgery T k = U.
   This identifies the ENTIRE integer kernel of the genuine P1xP1
   3-carrier homology signature, not merely one successful move.
   NEW theorem effective_calibrated_replacement_iff:
     given initial nonnegative anti,diagonal,ruling multiplicities,
     existence of a NONNEGATIVE calibrated integer packet in its
     exact homology class is EQUIVALENT to anti<=diagonal.
   An explicit witness is surgery T T.anti, and the necessity
   follows from homology's first coordinate and the exact
   formula defect(T)=2*T.anti for nonnegative packets.
   CI 38881066367 SUCCESS. This is a complete classification
   WITHIN the three actual geometric generator classes,
   not all currents on P1xP1 and not arbitrary X.

2. GSTNAllChannelAmpleSaturation.lean
   NEW theorem defect_zero_iff_all_coordinates_nonnegative:
      for every finite N-shape and strictly positive
      integer channel weights w_i,
        D_w(a)=0 iff all a_i>=0.
   The proof uses exact weighted negative-part decomposition,
   positivity of all terms, and integral mass semantics.
   CI 38879578256 SUCCESS. The coordinate channel basis
   is NOT automatically an algebraic basis on arbitrary X.

3. GSTUniversalSelfProductPrimitive.lean
   NEW theorems universalPrimitive_homogeneous,
   universalPrimitive_natural,
   universalPrimitive_natural_and_primitive:
   the GST degree-n primitive respects ALL commutative-ring
   morphisms (including genuine geometric pullbacks WHEN
   their Chow/cohomology dictionary is supplied), scales
   with homogeneous degree n, and retains primitive
   annihilation after morphism and dimension nilpotence.
   Verified by antigraph integration CI 38879578306 SUCCESS.

4. GSTUniversalAntigraphDiagonalSurgery.lean
   NEW theorems opposite_integer_homology_surgery and
   integer_parity_surgery_resolves_twice_diagonal:
   the entire diagonal splits into TWO integer-effective
   complementary parity packets, for arbitrary dimension n
   and commutative coefficient ring.
   A SECOND extension removes the range-index restriction:
   full_cellular_antigraph_surgery,
   full_cellular_opposite_surgery,
   full_cellular_integral_parity_resolution
   are valid for ANY FINITE CELLULAR INDEX and any graded
   basis coefficients. Applications to real split flag varieties
   require actual effective Schubert dual cycle products,
   a compatible antiholomorphic involution and the
   ambient-orientation-corrected parity action.
   CI 38880573985 SUCCESS. Lean establishes the coefficient
   algebra; realization data are separate geometric claims.

Architecture/performance change:
   GSTNPrimitiveGeometricSurgery.lean no longer imports the
   unrelated very large waves.GSTNCohomologyV3 transitive
   closure. It imports Mathlib directly; the N-wave model is
   independently proved and verified in its own module.
   The original primitive surgery and external product surgery
   workflow root lists were updated to match actual imports.
   Dependency-independent CI 38881066367 and 38881066332
   BOTH SUCCESS, avoiding thousands of unrelated build modules.
   All new theorems were checked with #print axioms and the
   CI log did not report sorryAx.

All four verification gates GREEN at this checkpoint:
   38879578256 N-cone
   38880573985 cellular/antigraph
   38881066367 integer orbit
   38881066332 external product integration

**Original all-X rational Hodge conclusion remains UNPROVED.**
A finite generated geometric packet can be completely classified
without the collection spanning every primitive Hodge fiber.
None of these new laws constructs integral homology relations from
arbitrary primitive rational (p,p) classes to positive algebraic
cycle packets on an arbitrary smooth projective X. That exact
realization map remains the unresolved original objective.
