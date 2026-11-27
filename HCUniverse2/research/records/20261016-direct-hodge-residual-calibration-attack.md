# Mathbox — direct geometric attempt on the universal zero-residual-norm theorem

2026-10-16. **The target is unchanged**: prove Q(r_alpha,r_alpha)=0 independently for every primitive rational (p,p) Hodge residual on every smooth projective complex variety X. This record does not claim the target is proved.

## New mechanism: calibrated integral cycles (not algebraic-correspondence words)

Let d=dim_C X, q=d-p, and h=[omega] an integral ample Kahler class. Let alpha be rational (p,p). Fix m>0 with m alpha integral modulo torsion, and an integer M>0. Define beta=m alpha + M h^p in H^{2p}(X,Z)/torsion. Let c_omega=omega^q/q!, the Wirtinger calibration on oriented real 2q-dimensional tangent planes.

For an integer rectifiable closed current T with integral homology class PD(beta), define its *absolute* calibration defect:

    D(T) = Mass(T) - Integral_T(c_omega) >= 0.

The second term depends only on beta. The analytic proof attempt is to construct integral closed currents T_n, all with the SAME integral homology class PD(beta), and D(T_n) -> 0.

### Rigorous implication of such a construction

Because Integral_{T_n}(c_omega) is constant and D(T_n)->0, the currents have uniformly bounded masses, and zero boundary mass. Federer–Fleming compactness on compact X gives a flat-convergent subsequence of integral cycles with limit T in the same integral homology class. Lower semicontinuity of mass and calibration yield Mass(T)=Integral_T(c_omega), so T is a calibrated integral current. Kahler calibrated integral cycles are positive holomorphic chains (King / Harvey–Shiffman); projectivity and Chow's theorem make T algebraic.

Thus beta has an effective algebraic representative. Subtracting the pre-existing algebraic cycle M h^p, then dividing by m, constructs an actual rational algebraic cycle with class alpha on X. Its canonical algebraic-image residual r_alpha is exactly zero, hence Q(r_alpha,r_alpha)=0. This would close the precise requested theorem if the T_n construction is established for EVERY X,p,alpha.

This route uses no target-native witness hypothesis and genuinely attempts to manufacture an algebraic cycle starting from a topological integral class.

### Tested failure point: Hodge type is not an integral-current construction

Hodge theory supplies a smooth real closed (p,p) representative eta. For large M, M omega^p + m eta is strictly positive and closed, hence defines a diffuse POSITIVE normal current in beta. However, diffuse positive currents are not necessarily integral rectifiable currents. Rationality of the COHOMOLOGY class does not make the representative an integral holomorphic chain.

An approximation of a positive current by rational-weight rectifiable currents with UNBOUNDED denominators does not suffice: scaling to integer currents then changes the integral homology class to m_n beta and can make masses grow. The fixed-beta compactness argument no longer applies.

The needed construction of T_n in the SAME class, with ABSOLUTE defect -> 0, was not obtained from Hodge type. It is an independent geometric/analytic step, not supplied by the existing GST internal matrix units.

## Primitive degree test

For any primitive r in H^{2p}(X,Q), p>=1 and 2p<=d,

    L^{d-2p+1} r = 0

implies

    Integral_X r h^{d-p} = 0.

Every NONZERO effective algebraic codimension-p cycle has strictly positive ample degree. Therefore even an algebraic primitive r cannot be represented by one nonzero effective calibrated cycle: it must be a SIGNED difference. Shifting by M h^p is essential to this proposed route.

### Actual projective arithmetic test (not a model counterexample to Hodge)

X=P^2 x P^2, h=A+B, CH^*(X)_Q=Q[A,B]/(A^3,B^3), with Integral_X A^2 B^2=1.
Take r=A^2-AB+B^2. Exact polynomial arithmetic proves:

    h r = 0 in CH^3(X);
    Integral_X r h^2 = 0;
    Q(r,r)=Integral_X r^2=3.

Set U=A^2+B^2 and V=AB. U and V are EFFECTIVE codimension-2 algebraic surface sums with equal h^2-degree 2, and U-V=r. Both h^2+r=2A^2+AB+2B^2 and h^2-r=3AB are effective with h^2-degree 6.

Thus primitive degree zero plus positive polarization square is compatible with a nonzero SIGNED algebraic class; these conditions alone cannot force a Hodge residual to vanish. In this cellular X, all classes are algebraic, so its canonical residual is zero. Exact results were independently recomputed in SymPy; they test the SIGNED geometry, not the conjecture.

## Alternative proof mechanisms tested, not adopted as new targets

* Genuine algebraic correspondences preserve the native cycle image. GSTClassicalHodgeCorrespondenceInvariantGhost and GSTClassicalHodgeCoherentNativeGhostObstruction already establish the corresponding obstruction; acting only on algebraic seeds cannot reach a hypothetical missing direction.
* Ordinary deformation/monodromy arguments do not cover rational Hodge classes that become Hodge only at special loci. One cannot assert the same (p,p) condition at generic deformation parameters.

**Outcome on original target:** incomplete. This is a mathematical attempt at a new independent geometric source of zero norm, including the exact analytic limiting argument and a genuine middle-dimensional projective falsification test. The fixed-homology integral calibrated approximation remains unproved. No new conditional Lean "finale", unsupported axiom, or claim of universal Hodge has been inserted.
