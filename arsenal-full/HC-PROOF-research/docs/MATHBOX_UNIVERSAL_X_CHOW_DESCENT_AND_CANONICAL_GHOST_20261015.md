# MATHBOX — UNIVERSAL HODGE REPRESENTATION ON X: EXACT DESCENT AND POLARIZED GHOST

Date: 2026-10-15
Pinned base: research/mathbox-k3-diagonal-primitive-20261015 at 1e1c24ed0672f18544ab352947e107d0ec80814e.
Original target: for every smooth projective complex variety X, every p, every rational (p,p) class alpha on X, construct a genuine rational codimension-p algebraic cycle Z on X with cl(Z)=alpha.

**Evidence classification:** The unrestricted Hodge conjecture is NOT proved by this record. We did not replace the original goal with self-product algebraicity, arbitrary Hodge-class cycle selectors, free correspondence matrix units, or a conditional "no ghost" axiom.

## Route A: genuine descent into X, not just geometry on X×X

Let dim_C(X)=d, h=c1(L) for an ample algebraic line bundle, and delta=int_X h^d>0.
For any rational Hodge (p,p) class alpha on X, form

    sigma_p(alpha) = (1/delta) pr1^*alpha cup pr2^*(h^d)
                        in H^{2(p+d)}(X×X,Q).

**Actual geometry:**
- sigma_p(alpha) is a rational (p+d,p+d) Hodge class.
- (pr1)_*sigma_p(alpha)=alpha by the Kunneth/Fubini or projection formula.
- The native Chow operation (pr1)_*:CH^{p+d}(X×X)_Q -> CH^p(X)_Q commutes with rational cycle classes.
- If sigma_p(alpha)=cl(W) for an actual rational codimension-p+d algebraic cycle W on X×X, the explicit actual cycle Z_alpha=(pr1)_*W on X satisfies cl(Z_alpha)=alpha.
- Conversely, if alpha=cl(Z), the genuine algebraic cycle (1/delta) pr1^*Z·pr2^*h^d represents sigma_p(alpha).

Therefore, WITHOUT assuming Hodge, the exact equivalence is

    alpha algebraic on X  <==> sigma_p(alpha) algebraic on X×X.

This is stronger and more economical than assuming every Hodge class on X×X is algebraic: only the **marked Kunneth-section subspace** needs algebraic representatives.

Lean:
- GSTUniversalChowRetractToTarget.lean formalizes native-X descent in actual Stage-2G cycle and Betti types, conditional on genuine Chow/Betti correspondence naturality and a source Hodge lift.
- GSTUniversalSelfProductHodgeEquivalence.lean gives both implications of the exact individual-alpha and all-alpha marked-source equivalence, from genuine external product/projection identities.

The remaining theorem needed is not a new formal map. It is the unconditional construction of an algebraic W for sigma_p(alpha), for every X,p,alpha, without presupposing alpha was algebraic. This is equivalent to original Hodge for X, so merely naming it does not solve the conjecture.

## Why the old universal self-product primitive does NOT complete Route A

The Green theorem GSTUniversalSelfProductPrimitive.lean constructs
  P_d(a,b)=sum_{j=0}^d (-1)^j a^(d-j)b^j
using the two pulled-back ample divisors a=pr1^*h, b=pr2^*h.

Its class is genuinely algebraic and primitive on X×X for EVERY X.
However, an algebraic correspondence applied to a known algebraic source stays in the algebraic image on X. The single P_d source carries no arbitrary Hodge alpha coefficient.

After multiplying P_d by b^d and projecting to X, only its a^d b^d term survives (all other terms contain b^{d+1} or higher). Its descent is a scalar multiple of h^d, not the arbitrary alpha.

**Smallest decisive countertest to this proposed generating mechanism**:
X=P^1×P^1; let A,B be its two divisor/ruling classes and let h=A+B (ample). Rational (1,1) class
  alpha=A-B
is nonzero, primitive (h·alpha=A²-B²=0) and algebraic, yet alpha is not in the one-dimensional degree-two algebra Qh.
Therefore a recipe whose only degree-two input is h cannot produce all classes even on this easy variety.
This refutes the GENERATING MECHANISM, NOT the Hodge conjecture. New independent geometric source classes/correspondences are mandatory.

## Route B: construct the maximal algebraic part of every primitive Hodge target

Fix primitive rational Hodge space
  V=P^{p,p}(X) ∩ H^{2p}(X,Q)
for 2p<=dim X, and let A be its **actual algebraic primitive subspace**, i.e. A=V∩im(cl_p).

The Hodge-Riemann bilinear relations give a positive-definite rational form on V:
  Q_p(x,y)=(-1)^p ∫_X x·y·h^{dim(X)-2p}
with the usual primitive (p,p) sign convention.

This positive-definiteness alone, not the Hodge conjecture, implies the restriction of Q_p to A is nondegenerate. Betti finiteness gives a finite rational basis a_1,...,a_r of A; each a_i=cl(Z_i) has an ACTUAL source cycle Z_i by definition of A. Their rational Gram matrix G_ij=Q_p(a_i,a_j) is invertible.

Define the rational-linear intersection-dual probes
  ell_i(alpha)=sum_j (G^{-1})_{ij} Q_p(alpha,a_j).

Now for EVERY primitive rational Hodge target alpha construct an ACTUAL native algebraic cycle

  Z_alpha=sum_i ell_i(alpha) Z_i.

By exact Gram algebra, for every j,
  Q_p(alpha-cl(Z_alpha),a_j)=0.

Set the canonical residual
  r_alpha=alpha-cl(Z_alpha).
It is a genuine rational primitive (p,p) Hodge class of X.
The exact Pythagorean identity is

  Q_p(alpha,alpha) =
    Q_p(cl(Z_alpha),cl(Z_alpha)) + Q_p(r_alpha,r_alpha).

Since Q_p is positive definite:
  r_alpha=0 iff Q_p(r_alpha,r_alpha)=0.
In that case cl(Z_alpha)=alpha, an honest Hodge proof for that alpha.

Crucial: this does not prove r_alpha=0 universally. It isolates the only remaining primitive rational Hodge component after all already-constructed algebraic directions have been used.

Lean:
- GSTUniversalHodgeResidualProjection.lean formalizes rational-native Z_alpha, dual detection, residual annihilation, exact split, and nonzero residual from a hypothetical missing Hodge class.
- GSTActualXHodgeResidualProjection.lean instantiates the same construction in REAL Stage-2G codimension-p cycles and rational Hodge subspaces of the ORIGINAL X.
- GSTPolarizedHodgeResidualEnergy.lean formalizes exact polarized Hodge Pythagoras and strictly positive energy of any nonzero residual under a genuine positive-definite geometric form.

## Route C: canonical rational Hodge ghost for GST's original common-class strike

If r_alpha!=0, define the canonical RATIONAL linear ghost

    ghost_alpha(v) = Q_p(r_alpha,v).

It annihilates EVERY actual algebraic primitive class a∈A because r_alpha is perpendicular to A. Yet it detects its own target alpha with

    ghost_alpha(alpha)=Q_p(r_alpha,r_alpha)>0.

Thus a hypothetical failure of the Hodge conjecture forces a specific positive-norm **primitive polarization ghost**; it is not merely an arbitrary choice from a quotient dual.

This is an exact, independently checkable witness for the existing GSTClassicalHodgeAtomicAnnihilator and GSTClassicalHodgeOmniversalSeparatorGhostCrown mechanisms.

Lean file GSTCanonicalPolarizedHodgeGhost.lean constructs this functional, proves all finite-source generators are killed, extends this to the entire native image when its finite basis is provided, and proves strict positive detection of an unrepresented target.

**The decisive original missing implication remains**:
For every X and any nonzero primitive rational (p,p) residual r_alpha as above, derive a contradiction FROM INDEPENDENT ALGEBRAIC GEOMETRY (for example a strictly constructed true common-class trace carrier satisfying the GST strict source/target naturality equations), without postulating the carrier or a cycle representative for alpha.

Existing GSTCommonClassPlane machinery proves an implication FROM such strict carriers. It does not yet construct them for all hypothetical ghosts. The Hodge–Riemann energy makes their target and detector canonical; it does not make that strict geometric carrier exist.

## Claims and falsification boundaries

1. "A single self-product hyperplane primitive covers all Hodge classes of X" — REFUTED as a generating method by P^1×P^1.
2. "Chow/BettI correspondence can map represented source classes into actual cycles on X" — PROVED conditionally on independent genuine naturality data. True for standard proper pushforward/external product geometry.
3. "Every rational Hodge alpha on X has a constructed algebraic projection plus canonical residual" — PROVED from a finite algebraic image basis and its intersection duality; that finite basis exists for each primitive Hodge fiber by Hodge–Riemann.
4. "Every canonical residual vanishes" — UNPROVED; this is equivalent to the original primitive Hodge problem.
5. "An arbitrary hypothetical missing Hodge class generates a positive canonical ghost annihilating native classes" — PROVED under Hodge–Riemann positive primitive polarization and the full native algebraic image basis.
6. "GST excludes every canonical ghost for arbitrary X by explicit strict geometry" — NOT ESTABLISHED. This is the exact active mathematics target, not a proof-engineering error.

The original conjecture will count as proved only after point (6) or another genuinely independent unconditional geometric argument yields point (4) for ALL smooth projective X,p and all rational Hodge alpha, with every Hodge source and scheme comparison verified. No partial theorem gets promoted to that status by compiling green.


## Route D: use the previously solved GST K3 source to construct cycles ON a different X

File GSTK3GeometricSourceToArbitraryX.lean directly composes:
- the previously kernel-verified K3 diagonal/divisor middle-Hodge cycle construction under the scalar transcendental Hodge-End and Kunneth conditions; with
- the genuine X-target Chow/Betti correspondence retraction of Route A.

Conclusion: if a target X has an independently verified Hodge-preserving native Chow retract from such a K3-product source Y, then EVERY rational Hodge (p,p) target class on X has an ACTUAL codimension-p rational native algebraic cycle. No target algebraicity hypothesis or arbitrary Hodge-to-cycle selector is used. The geometric retract condition is restrictive and must be demonstrated before applying the theorem.

**Independent rank barrier**: No single fixed K3-product source can be a rational-Hodge retract for every X and all degrees. For instance, the all-algebraic Hodge group H^{2p}((P^1)^n,Q) has dimension binomial(n,p), unbounded as n grows, whereas one fixed source H^4(Y,Q) has finite dimension. Thus GST's universal sources must grow with X or exploit additional genuinely new geometric correspondences; reusing a single fixed K3 constructor, regardless of operator complexity, cannot provide an arbitrary-X surjective Hodge map.

The variable source Y=X×X automatically scales with X, but marked Hodge-section algebraicity for arbitrary X is exactly the original unsolved task, as shown in Route A.

No formal or mathematical assertion has been made that all arbitrary X admit the required K3-source motive retract.

## Scope caution — semantic Stage-2G model

The repository's Stage-2G HodgeBigradedBettiData stores cycleClass as a field. GSTClassicalHodgeStage2GSemanticRigidity.lean constructs a zero-cycleClass countermodel on a nonzero rational Hodge fiber. Therefore universal representation CANNOT be obtained by merely proving a theorem for arbitrary Stage-2G data with no geometric cycle-class constraints. All positive conclusions here explicitly require genuine independently justified Chow/cycleClass, Gysin, Hodge-theory and intersection compatibility for the actual variety. Compiling an interface does not instantiate such geometry from scratch.


## Verified repository execution — exact CI provenance

The following are the replacement successful GitHub Actions proof builds
observed on this research branch. The cited runs verify their *typed statements*,
which explicitly expose the independent geometry needed for arbitrary X:

- Mathbox Universal Hodge Residual Projection — run **38757505573**, SUCCESS.
- GST Actual Universal Target Chow Retract — run **38757582102**, SUCCESS.
- Mathbox Polarized Hodge Residual Energy — run **38758164216**, SUCCESS.
- GST Exact X and Self Product Hodge Equivalence — run **38758647720**, SUCCESS.
- GST Canonical Polarized Hodge Ghost — run **38758997344**, SUCCESS.
- GST Actual X Hodge Residual Projection — run **38759407970**, SUCCESS.
- Original GST K3 Complete No Ghost bridge — run **38755625966**, SUCCESS.

The separate composed K3 source -> arbitrary X module,
GSTK3GeometricSourceToArbitraryX.lean, has its independent
workflow GST K3 Native Source to Arbitrary X, run **38759885729**.
Its result must be read from the workflow, and is not presumed green.

Earlier failures in these newly created modules were Lean elaboration/
reserved-word/finite-index instance problems, repaired on the branch;
they are not evidence for or against the Hodge conjecture itself.

**No unconditional proof of the full all-X all-p Hodge conjecture
has been certified by any of these CI builds.** The remaining
mathematical requirement is the independent construction of enough
actual Chow correspondences or a canonical-ghost contradiction to
force ALL residuals to vanish for arbitrary smooth projective X,
without assuming precisely that geometric availability.
