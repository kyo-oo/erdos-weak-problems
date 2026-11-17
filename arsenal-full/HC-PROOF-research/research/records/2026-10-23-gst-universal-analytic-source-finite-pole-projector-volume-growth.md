# Mathbox: actual all-X analytic Hodge source birth; finite-pole and spatial-volume geometric descent

- **Date:** 2026-10-23 (Asia/Kolkata).
- **Active branch:** `research/gpt6-native-point-primitive-span-20261017`.
- **Start checkpoint:** `49331e8c79106d21ef5379d6924dcc476227d14d`.
- **Original target:** arbitrary smooth projective complex X of dimension d; p∈[1,d]; rational (p,p) alpha; output actual original-X rational Chow cycle Z_alpha with canonical Betti class alpha. No abstract surjectivity or pre-existing Chow representative is accepted.
- **Mathbox skills:** research-program, research-attempt, proof-audit, computation-audit, literature-check. Self-audit (not independent external reviewer). No internet research or local Lean installation.
- **Main substantive new mathematical source:** [full geometry-first LaTeX derivation](../derivations/GST_universal_analytic_degeneracy_cycle_growth_descent_2026-10-23.tex), created commit `a51156ad9b2538fd7ee3566a8e1f6582f4d6beeb`; subsequent finite-pole, projective Nijenhuis, and volume results appended as mathematical proofs, not a change of target.

## Unconditional construction: actual analytic determinantal cycle for EVERY class

Let X⊂P^N be any projective embedding; form the real algebraic affine incidence fold J_N(X)={(x,H):H(x)≠0}, with q:J→X a Zariski locally trivial A^N torsor. J is smooth AFFINE of dimension d+N and q^* identifies ordinary Betti cohomology MHS with that of original X (whole-Hodge structure conserved). Every rational alpha∈H^(2p)(X,Q), even without assuming Hodge type, gives by rational K theory after multiplying m>0 an honest topological bundle E with FULL ch(E)=rank+m alpha and all other positive grades zero. Oka–Grauert on Stein J^an gives a holomorphic lift F of q^*E. Choose a finite topological bundle complement, use Oka also on the complement and the topological trivialization: F is an actual holomorphic direct summand of O^M, hence an HONEST finite global holomorphic projector P_alpha(z)^2=P_alpha(z), constant rank r and ch(im P)=r+m q^*alpha.

Choose s=r-p+1 generic global generating holomorphic sections of F. Their rank-deficiency locus Σ_alpha={rank φ<s} is an ACTUAL closed analytic degeneracy locus of pure complex codimension p (when nonempty), by parametric transversality since the universal evaluation is pointwise onto. The analytic Thom–Porteous theorem and Newton identity give:

`[Σ_alpha]_Betti = c_p(F) = (-1)^(p-1)m(p-1)! q^*alpha` in H^(2p)(J,Q).

If alpha≠0 the cycle is nonempty because q^* injective. This is genuine universal-in-X,p,N analytic spatial SOURCE BIRTH (not an arbitrary Chow map, not a numerical test) and is stronger in scope than Hodge classes: it works for every rational EVEN cohomology class. Analytic does not automatically mean algebraic on noncompact Stein J; the class alone does not establish the original Chow target.

## Independent new theorem: polynomially bounded projectors are regular algebraic

Fix a closed algebraic embedding J⊂A^K. A holomorphic scalar function f on J^an has finite polynomial growth `|f(z)| ≤ C(1+||z||)^k` if and only if f is a REGULAR algebraic function on J. Proof: regular→polynomial growth from the affine coordinate ring; polynomial growth→meromorphic extension across SNC boundary of smooth projective compactification with finite pole order, then projective meromorphic GAGA→rational; no affine poles→regular. This is a genuine geometric finite-growth theorem, not an extrapolation from a finite test.

**Exact constructive class-by-class iff:** original alpha algebraic on original X iff there exists SOME honest holomorphic idempotent P on the actual J with FULL ch(P)=r+m q^*alpha and every matrix entry of finite polynomial growth. Then P is an ALGEBRAIC idempotent projective module and the explicit original-X output is

`Z_alpha=(q^*)^{-1}[(-1)^(p-1)c_p^CH(im P)/(m(p-1)!)]`,

using true Chow affine-bundle homotopy invariance and canonical Betti naturality. Converse: if alpha is algebraic, take algebraic K0 pure Chern class, pull to AFFINE J, clear denominators and choose an honest projective-module free complement to obtain a SINGLE positive-rank algebraic bundle with ch=r+m q^*alpha; represent it as a FINITE regular idempotent matrix. The affine J is crucial: arbitrary projective X need not admit algebraic complements to trivial bundles.

**Uniform spatial pole theorem:** for each fixed X,p,J, the rational Hodge fiber has a finite Q basis; if its members algebraize, positive and negative pure-class modules for those finitely many basis elements can be built and block summed. Therefore ONE finite pole/growth exponent K(X,p,J) suffices for EVERY rational Hodge alpha (allowing arbitrary matrix sizes and coefficient denominators), iff all classes on (X,p) are algebraic. This turns arbitrarily many target classes into a finite set of source-growth complexity bounds.

## Explicit finite algebraic scheme matrix equations, ANY X and N

Take compactification bar J=X×(P^N)^∨ with incidence section s∈H⁰(bar J,L), L=O_X(1)⊠O_D(1). True ring description: `Γ(J,O)=colim_k H⁰(bar J,L^k)` with transition multiplication by s. Any regular projector P has a common finite pole order k and A=s^k P, where each A_ij is an ACTUAL global bihomogeneous section of L^k, and

`A²=s^k A; trace A=r s^k; ch_top(im(A/s^k))=r+m q^*alpha.`

Conversely any such A determines a true original-X source by the displayed formula. The first two equalities are finitely many polynomial equations in coefficients from a finite-dimensional section space; the third is the independent full rational Betti/period compatibility, **not** silently assumed. This is the most precise polynomial scheme-level geometric certificate obtained this turn.

A genuine ambient idempotent `P_amb=x ell^T/(ell.x)` exists for EVERY X,N, with matrix numerator A=x ell^T satisfying A²=sA and trace A=s. Its image is q^*O_X(-1); its ch stays in Q[h], so repeated ambient-only operations cannot produce arbitrary primitive alpha. That fact guards against a false universal source promotion.

## Exact spatial normalized-volume theorem (source-dependent external input)

For the genuine analytic Σ_alpha⊂J⊂C^K of complex dimension s'=d+N-p, let VΣ(R) be its Euclidean volume in radius R. The classical Bishop–Stoll criterion says a closed pure-dimensional analytic variety in affine C^K is algebraic when `VΣ(R)=O(R^(2s'))`; algebraic varieties have this bound. Since genuine J is an affine closed subvariety in C^K, this gives a second EXACT geometry-to-algebraicity iff: alpha algebraic iff there exists a genuine pure-class analytic determinantal source Σ_alpha with finite normalized volume `sup_{R≥1} VΣ(R)/R^(2(d+N-p))<∞`. The resulting original-X cycle is `Z=(-1)^(p-1)/(m(p-1)!) (q^*)^-1[Σ]_Chow`. It is the realized whole-space dimension/volume route the owner intended, as a rigorous geometric criterion. The repo-local theorem applies the named external analytic algebraicity theorem and verifies expected hypotheses; **exact primary-source publication/version not authenticated this turn**, so its external dependency status is conditional until checked. The *polynomial-projector proof* above has an internal geometric argument and no Bishop–Stoll dependency.

## Projective curvature/Nijenhuis attempted independent route

On original compact Kähler X, suppose an honest topological E with pure ch=r+m alpha admits a smooth (0,1)-connection D with traceless projective (0,2)-curvature `F_D^(0,2) - tr(F_D^(0,2))/r Id =0`. Since alpha has type(p,p), c1(E) has no (0,2)-component: it is zero for p≥2 and of type(1,1) for p=1. Bianchi makes the scalar trace η (0,2) ∂bar-closed; its Dolbeault class zero. Solve ∂bar β=η and set D'=D−β Id, obtaining (D')²=0. Koszul–Malgrange and projective GAGA give a TRUE original-X algebraic E and explicit Z=(-1)^(p-1)c_p^CH(E)/(m(p-1)!). This proves a fully typed geometric sufficient theorem (with converse for existing holomorphic E); it does NOT derive traceless curvature vanishing from purity. The projectivized-integrability shortcut is thereby shown not to evade original-X integrability.

Two additional actual geometric no-go facts: if dim X>0 the Stein affine-world torsor q:J^an→X^an has NO holomorphic global section (compact X cannot map nontrivially to Stein). For nonconstant regular f on affine J, the principal analytic divisor `{e^{f(z)}−1=0}` is a real closed analytic divisor of ZERO cohomology class but is not algebraic: its f-image is infinite discrete 2πi Z∩f(J), impossible for the constructible image of an algebraic subvariety by Chevalley. Therefore even pure/zero Hodge class does NOT algebraize arbitrary analytic representative; geometry must select a finite-growth source.

## Exact independent finite computations and Lean

- [Wolfram source](../computations/gst_analytic_fold_projector_determinantal_chern_2026_10_23.wl), final rerun from blob `da00257ae4118fdc42d40b96b0f146c85e0283c0`.
- **7/7** rational homogeneous incidence A²=sA and trace A=s cases for n=2..8 passed; **7/7** normalized idempotent cases passed; **68/68** pure-Chern coefficient identities for 1≤p≤8,p≤d≤12 passed, exact symbolic. Explicit holomorphic gauge-conjugated projector `[[1,−exp(z)],[0,0]]` has identical trivial K-class but no polynomial growth, confirming growth is a property of a selected representative and no bound follows for ALL holomorphic projectors.
- Existing `GSTGraphV2UnboundedHigherCausality.lean` edited surgically at commit `26fed14b546a8996d3de9bafb4e88ac9fbe33df7`. New `CausalFinitePoleIncidence.incidenceNumerator_square` proves all-N exact A²=sA and trace=s for arbitrary n via finite sum and `ring`. `#print axioms` included; [**GitHub Actions run 39911331579**](https://github.com/kyo-oo/HC-PROOF/actions/runs/39911331579) **COMPLETED SUCCESS** at the exact source commit `26fed14b546a8996d3de9bafb4e88ac9fbe33df7`; verified from job logs: Lean passed the prescribed root and the no-`sorryAx` gate. No local Lean compilation. No local Lean install; this is the rational polynomial incidence shadow, not a formalized Oka/Chow analytic theorem.

## Research-program truth boundary and exact remaining mathematics

The previous universal *topological* spatial fold is now connected to a universal ACTUAL analytic cycle for EVERY alpha, and the geometry-to-original-Chow criterion is sharpened to either polynomial growth of an ACTUAL holomorphic projector or critical Euclidean volume growth of an ACTUAL analytic degeneracy cycle. These are proved mathematical statements (volume criterion conditional on exact external theorem). The single remaining universal move is to construct a finite-growth representative for each rational Hodge alpha independently from its type(p,p), or derive an actual counterexample to that finite-growth realization. Hodge-type/purity conservation by itself supplies neither growth bound; the nonalgebraic principal analytic divisor and unbounded-gauge projector explicitly show why. This is the active spatial-geometric route, no elliptic/Weil special-family substitutions, no synthetic Chow selector, and no false final Clay-certificate claim.

## Third substantive mathematical route: full original-X fiber-translation coherence

The Jouanolou morphism q:J→X is not merely an A^N fibration. Its points are splittings of the surjection `(C^(N+1))^*⊗O_X(-1)→O_X`, so it is an actual torsor under the kernel rank-N ALGEBRAIC vector bundle. There is a genuine fiber-addition action `a:V×_X J→J`.

**Proved exact theorem:** for arbitrary original smooth projective X,p and rational alpha, an ACTUAL closed rational analytic codimension-p cycle W in J with canonical analytic Betti class q^*alpha that is invariant AS A CYCLE under every fiber translation (`a^-1W=pr_J^-1W` as analytic cycles) exists **iff** alpha has an original-X rational algebraic Chow cycle. If W is translation-invariant, then in every local holomorphic trivialization J|U≅U×C^N it is the pullback of a unique analytic cycle Z_U on U. The local Z_U glue by translation coherence; on compact projective X a closed analytic cycle is algebraic by Chow/GAGA, and q^* Betti injectivity checks its class equals alpha. Conversely genuine algebraic Z on X pulls back to a translation-invariant analytic W on J.

This distinguishes a *whole-fold CAUSAL SYMMETRY LAW* from purely cohomological symmetry: q^*alpha is automatically cohomologically translation-invariant, but the actual analytic degeneracy representative constructed earlier need not be. Turning an ACTUAL analytic cycle into an actual translation-equivariant analytic cycle is a concrete independent mathematical route (not a requirement that all holomorphic bundles magically be algebraic). It is exactly the mathematically relevant preservation observable.

**Audit:** The symmetry condition is not derived by the topological Chern fold or Oka theorem; no averaging of analytic cycles over the noncompact additive affine group may be invoked without proving analyticity, multiplicities and local finiteness. The equivalence is proved for true analytic cycles; it is not promoted to a universal source constructor.

## Final exact evidence

- Current [source mathematics](../derivations/GST_universal_analytic_degeneracy_cycle_growth_descent_2026-10-23.tex) now includes all-X actual analytic determinantal cycle, finite pole/projector iff, uniform per-(X,p) growth order, externally sourced normalized spatial-volume test, projective traceless-curvature/Nijenhuis test, scheme polynomial equations, and full affine-fiber translation-equivariant descent.
- [Wolfram verified source](../computations/gst_analytic_fold_projector_determinantal_chern_2026_10_23.wl), current blob `da00257ae4118fdc42d40b96b0f146c85e0283c0`: 7/7 finite scheme matrix equations A²=sA, 7/7 normalized idempotence/trace, 68/68 Newton pure-Chern coefficient identities. The original finite matrix test erroneously used matrix-level `Together` that left unsimplified structural comparisons; corrected to exact entrywise `Together` + `PossibleZeroQ` and rerun verbatim, with no failed checks.
- [Lean green run 39911331579](https://github.com/kyo-oo/HC-PROOF/actions/runs/39911331579), exact matching source SHA `26fed14b546a8996d3de9bafb4e88ac9fbe33df7`.
- **Status:** direct analytic geometric SOURCE for ALL X,p,alpha is constructed without a Chow witness. Exact genuine original-X Chow extraction is proved under independently stated *finite geometric growth* or *actual affine-fiber translation coherence*. A uniform mechanism producing either of those two extra geometric properties from the rational (p,p) condition alone has not been derived. No false final Clay proof or counterexample certificate is issued.


## Fourth spatial closure route: actual projective incidence boundary

We also proved the geometrically direct **boundary-extension iff** in the [full source](../derivations/GST_universal_analytic_degeneracy_cycle_growth_descent_2026-10-23.tex): the prescribed alpha is algebraic on ORIGINAL X iff there exists one of the ACTUAL constructed holomorphic determinantal source cycles Σ_alpha on affine J whose cycle extends ANALYTICALLY (including multiplicity) across the incidence boundary D to the compact projective product bar J=X×(P^N)^∨. If such an analytic closure exists, projective Chow's theorem makes it algebraic; restricting to J, applying the genuine Chow affine-space homotopy inverse and dividing by the known Chern coefficient constructs actual original Z_alpha. Conversely any algebraic alpha yields a regular idempotent with algebraic determinantal Sigma, whose projective Zariski closure is analytic.

The sharp dimension check is essential for the user's unlimited N visualization. Complex dim Σ=d+N−p and dim incidence boundary B=d+N−1, so **dim Σ−dim B=1−p for every finite N**. The usual sufficient Remmert–Stein condition dim Σ>dim B is NEVER reached for p≥1 no matter how many emergent complex dimensions the fold adds. This blocks a purported universal proof purely from dimension growth, not the possibility of a growth/compactification theorem based on stronger GST geometry. The actual boundary extension criterion, finite pole projector criterion, full affine translation-coherence criterion, and spatial volume bound are all precise mathematical arrows back to the original target; no inference of cycle algebraicity is made from Hodge purity alone.
