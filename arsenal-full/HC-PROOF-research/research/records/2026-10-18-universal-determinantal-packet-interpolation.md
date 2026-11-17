# Mathbox — every-original-X target-born K-theory/determinantal finite packet

**Date:** 2026-10-18.
**Authoritative base:** branch research/gpt6-native-point-primitive-span-20261017, revision 4bfd8934456f6a27bf4da9fcb8ec61bd382c7dc6, preceding this research checkpoint.
**Fixed exact goal:** on each original smooth projective complex X of dimension n, each p and each rational (p,p) Hodge alpha, construct an algebraic rational codimension-p cycle with canonical Betti class alpha, without assuming a preimage or full rank.
**Verdict:** proved an ALL-X, ALL-p, target-born **smooth topological geometric cycle packet** with the exact prescribed rational homology class. Algebraicity of the individual sheets or a replacement packet remains OPEN. Not a proof of the Hodge conjecture, not a new Lean compile.

## 1. Correct the earlier unstable BU(p) obstacle: construct in stable topological K-theory

Let 1<=p<=n and alpha in H^(2p)(X,Q), not necessarily Hodge. Compact smooth projective X has finite CW type. The rational topological Chern character is an isomorphism:

  ch: K_top^0(X) tensor Q  -> direct-sum_{i>=0} H^(2i)(X,Q).

Choose a rational virtual class eta with ch_0(eta)=p-1, ch_p(eta)=alpha, all other positive-degree ch_i=0. Choose positive N clearing its K-theory denominators. Then correct the rank of N eta by adding (p-1)(1-N) copies of the trivial line as a VIRTUAL K class. This yields an INTEGRAL topological K class xi with

  rank(xi)=p-1, ch_j(xi)=0 for 1<=j<p,
  ch_p(xi)=N alpha.

Represent xi=[F]-[E] by actual smooth complex bundles F,E, and if necessary stabilize both by identical trivial summands to ensure rank(E)=e>=1 and rank(F)=f=e+p-1.

Crucially we did NOT ask for a rank-p bundle with special top Chern class, did NOT presume a holomorphic or algebraic bundle, and did NOT presume an algebraic cycle representing alpha.

Newton/Chern-character identities give the EXACT cohomological identity
\[
 c_p(F-E)=(-1)^{p-1}(p-1)!\,\mathrm{ch}_p(F-E)
          =(-1)^{p-1}(p-1)!\,N\alpha.
\]
The vanishing of all lower Chern characters forces all c_j(F-E)=0 for 1<=j<p. Neither this identity nor the K-theory construction requires alpha to be Hodge: the Hodge condition must enter the later algebraization operation.

## 2. Genuinely geometric original-X rank-drop carriers

Fix a genuine ample holomorphic line L on original X, h=c1(L). For each positive integer k, choose a generic SMOOTH complex bundle map
\[
  \phi_k: E \longrightarrow F\otimes L^{\otimes k}.
\]
Its rank-drop locus D_k={rank(phi_k)<=e-1} has expected REAL codimension 2(f-e+1)=2p. Transversality to rank stratification gives an oriented top stratum; deeper rank-drop strata have higher codimension, so D_k defines a true integral homology/pseudocycle class on original X. Topological maximal-minor Thom–Porteous yields
\[
 \mathrm{PD}[D_k]=c_p(F\otimes L^k-E)\in H^{2p}(X,\mathbb Z).
\]
These smooth determinant-matrix rank-drop loci are genuine source-born GEOMETRIC carriers; they are NOT automatically complex-analytic or algebraic.

For arbitrary fixed F,E, the Chern class
\[
 P(k):=c_p(F\otimes L^k-E)
\]
is a polynomial in k of degree AT MOST p in the rational vector space H^(2p)(X,Q). To see this directly, use Chern roots x_1,...,x_f of F and total formal characteristic polynomial
\[
 c_t(F\otimes L^k-E)
  =\frac{\prod_{i=1}^f(1+(x_i+kh)t)}
         {c_t(E)}.
\]
The coefficient of t^p is polynomial of k degree <=p even without ANY lower-Chern vanishing. Its constant value is P(0)=c_p(F-E).

## 3. Universal finite-difference constructor, ALL dimensions and codimensions

Every polynomial P(k) of degree <=p over a rational vector space satisfies
\[
 P(0)=\sum_{k=1}^{p+1}(-1)^{k-1}\binom{p+1}{k}\,P(k),
\]
because the (p+1)-st forward difference vanishes. Apply this universal integer-coefficient law to the ACTUAL determinantal geometric cycles:
\[
 \boxed{
 \sum_{k=1}^{p+1}(-1)^{k-1}\binom{p+1}{k}\,
       \mathrm{PD}[D_k]
 =(-1)^{p-1}(p-1)!\,N\alpha .
 }
\]
Equivalently the signed oriented geometric packet
\[
 \boxed{
 T_{\alpha}:=\frac{(-1)^{p-1}}{(p-1)!\,N}
     \sum_{k=1}^{p+1}(-1)^{k-1}\binom{p+1}{k}[D_k]
 }
\]
has **exact** rational fundamental class PD(T_alpha)=alpha on the ORIGINAL X, for EVERY alpha (not just Hodge), EVERY 1<=p<=n. No selected Chow witness, irreducibility of geometric correspondences, determinant full-rank assumption, unstable BU(p) lift, or abstract pure Hodge matrix-unit naturality enters the construction.

This is a real finite geometric source construction rather than an equivalence disguised as one. However an arbitrary smooth rank-drop sheet is NOT a subvariety of the complex-algebraic category. Calling T_alpha a Chow cycle would be an error.

**Fresh primitive detection:** if alpha is a nonzero rational primitive Hodge class, its signed packet cannot have all component fundamental classes within an ambient algebraic subspace that excludes alpha, since that subspace is rational-linear and the exact signed sum equals alpha. This means the new SMOOTH carriers really reach the previously missing cohomological primitive direction. It does not make those carriers algebraic.

## 4. Exact independent polynomial checks

At p=2, take f=3,e=2, formal c1(F)=u, c2(F)=v,c1(E)=z. Let h denote the numerical hyperplane variable (set h=1 in the formal coefficient test). The exact Thom-Porteous polynomial is
\[
 P(k)=3k^2+(2u-3z)k+(v-uz+z^2).
\]
Wolfram returned:
  {P(k), 3P(1)-3P(2)+P(3), Boolean equality to P(0), coefficient k^2}
with output
  {3 k^2+2 k u+v-3 k z-u z+z^2, v-u z+z^2, True, 3}.
Here u,v,z are arbitrary symbols: the cancellation removes every unwanted term, not only ambient powers or vanishing lower Chern components.

At p=3, take f=5,e=3 with formal Chern parameters u,v,w for F and z,a,b for E. The exact third Chern polynomial has degree three with all mixed terms. Wolfram returned identically
  4P(1)-6P(2)+4P(3)-P(4)=P(0)
with symbolic difference exactly 0, and computed coefficient-weight moments {1,0,0,0}. The proof for all p is the general finite-difference identity above, not extrapolation from these checks.

## 4b. Arbitrarily POSITIVE twists with INTEGER source-packet coefficients

The initial 1,...,p+1 twist levels are convenient algebraically but may be too small for any approximately holomorphic/positive-curvature transversality theorem. We can solve this coefficient issue EXACTLY.

Fix ANY integer K>=1. At the consecutive twist levels K,K+1,...,K+p define
\[
\boxed{
\lambda_{K,p,j}=(-1)^j
  \binom{K+j-1}{j}\binom{K+p}{p-j},\qquad 0\le j\le p.
}
\]
These are INTEGERS (not merely rational coefficients). Lagrange interpolation at 0 for the p+1 nodes k=K+j gives
\[
\lambda_{K,p,j}
 =\prod_{m\ne j}\frac{-K-m}{j-m}
 =(-1)^j\frac{K(K+1)\cdots(K+p)}
            {(K+j)j!(p-j)!}.
\]
Consequently \(\sum_{j=0}^p\lambda_{K,p,j}(K+j)^m=\delta_{m,0}\) for EVERY 0<=m<=p. Therefore the following exact topological/geometric identity holds on EVERY original X:
\[
\boxed{
\sum_{j=0}^{p}
 \lambda_{K,p,j}\,\mathrm{PD}[D_{K+j}]
 =c_p(F-E)
 =(-1)^{p-1}(p-1)!\,N\alpha .
}
\]
This is the all-p GST finite-channel 'twist annihilation' law: any sufficiently positive twist regime is allowed, while ALL unwanted coefficients (including every mixed Chern term) cancel and the prescribed primitive vector survives exactly. No limit or approximate equality is taken.

At K=2,p=2 the exact integer packet is \(6D_2-8D_3+3D_4\). At K=5,p=3 it is \(56D_5-140D_6+120D_7-35D_8\). Wolfram evaluated exact moment vectors \(\{1,0,\ldots,0\}\) for K in {1,2,5} and p in {2,3,4}, while the displayed Lagrange identity proves ALL integers K>=1 and ALL p.

**Mass warning:** \(|\lambda_{K,p,j}|\) grows polynomially with K, so a compactness argument for the SIGNED geometric packet does NOT follow from separate approximately holomorphic estimates for each D. Precisely because these coefficients are signed, the homological cancellation is legitimate but positivity/mass cannot be assumed to cancel as well. The extra analytic challenge is to construct algebraic *holomorphic* degeneracy sheets at at least one K-regime (or independently algebraize their whole signed packet).

## 4c. Exact signed-mass growth: naive K->infinity compactness is NOT a proof

An attractive but false leap would be to use the arbitrarily positive twists of §4b, let K tend to infinity, and assert the signed packet converges to an analytic/algebraic cycle. The INTEGER cancellation controls homology, NOT total variation of the current.

For a primitive codimension-two alpha on a projective fourfold, take the simplest rational characteristic data f=3,e=2 with lower Chern characters zero, so the determinantal degrees are those of \(P(k)=3k^2 h^2-N\alpha\). Since alpha.h^2=0, the h²-degree of each positive sheet is \(3k^2\deg_h(X)\). The exact integer weights at twists K,K+1,K+2 are
\[
 a_0=(K+1)(K+2)/2,\quad a_1=-K(K+2),\quad
 a_2=K(K+1)/2.
\]
The signed degree cancels identically. However the unsigned weighted degree is
\[
 \sum_{j=0}^2|a_j|\int_XP(K+j)h^2
 =6K(K+1)^2(K+2)\,\deg_h(X)
 \sim 6K^4\deg_h(X).
\]
Wolfram verified both the exact factorization and zero signed degree; for K=1,2,3,4, the inner unsigned quadratic sum was 24,144,480,1200 respectively (multiply by 3*deg_h(X)). No K-uniform mass bound follows. In the general p model the leading total-variation scaling is order K^(2p), due to the K^p interpolation weights multiplying individual order-K^p positive sheet degrees.

Thus the new ALL-X geometric source equality is EXACT in rational homology at each finite K; turning it into algebraic geometry cannot use a bare compactness argument on the signed packets as K grows. It must be a finite-K Hodge-dependent conversion, an integrability result, or a new compensated compactness estimate that actually controls the cancellation at the current level.

## 5. Deep category obstruction: slope-polystable holomorphic bundles are TOO RESTRICTIVE

A tempting repair is to run Hermitian–Yang–Mills/Donaldson–Uhlenbeck–Yau heat flow on the topological K source until all F^(0,2) vanishes, then claim algebraicity. This DOES NOT GENERALLY WORK for a primitive nonzero source with the prescribed Chern-vector normalization.

**Theorem (standard Hermitian–Einstein/Chern–Weil consequence).** Suppose X is smooth projective Kähler and V is a slope-polystable holomorphic bundle with c1(V)=0 rationally. Its Hermitian–Einstein connection is trace-free and primitive. A positive Chern–Weil identity gives
\[
 \int_X c_2(V)\,h^{n-2}
    = C_{n,h}\int_X\lVert F_V\rVert^2\,\mathrm{vol}_h
    \quad(C_{n,h}>0).
\]
Thus if c2(V) h^(n-2) integrates to zero, the curvature is zero, V is unitary flat, and ALL its rational Chern classes vanish.

For a hypothetical topological rank-p bundle with ch_j=0 (j<p) and ch_p=N alpha≠0:
- For p>=3, c1=c2=0 automatically, hence NO such holomorphic bundle can be slope-polystable.
- For p=2 with n>=4 and alpha primitive of degree 4, c1=0 and c2=-N alpha. Primitive implies alpha h^(n-3)=0, so its c2 degree c2 h^(n-2) is zero, likewise ruling out any polystable holomorphic realization.

**Sharp actual original-X test:** on a cubic fourfold containing a plane, alpha=3[P]-h² is primitive and algebraic. Its true intersection data are alpha h²=0 but alpha²=24>0. Thus even for this KNOWN ALGEBRAIC nonzero primitive class, a polystable rank-two holomorphic bundle V with c1=0 and c2=±N alpha would violate the zero-energy Chern–Weil identity: such a V cannot exist. Wolfram independently confirmed the exact pairings {0,24}. The obstacle is not some alleged nonalgebraic class; it rules out a tempting overly rigid analytic carrier despite algebraicity.

**Therefore the correct all-X source birth cannot demand ONE slope-polystable normalized holomorphic bundle.** The original conjecture permits SIGNED Chow cycles. The finite bundle-difference/determinantal packet likewise needs signed, potentially slope-UNSTABLE, or perfect-complex/singular-sheaf geometry. This is a substantive limitation on how GST calibration energy may be used: ordinary HYM positivity kills primitive Chern channels when falsely imposed on a single normalized stable bundle.

The above uses the standard differential-geometric Hermitian–Einstein existence theorem for polystable bundles; the exact analytic external theorem and positivity normalization were NOT checked against a pinned primary-source document in this no-web checkpoint. The Chern-polynomial calculations were verified symbolically; the global differential-geometric claim is given with its mathematical hypotheses, not claimed as a Lean theorem.

## 5b. Second categorical birth: actual COMPLEX-ANALYTIC determinant sheets on one universal affine model

Let the original smooth projective X be embedded in a complex projective space. Its incidence-complement Jouanolou affine-space bundle \(\pi:J(X)\to X\) is a smooth affine algebraic variety, with contractible fibers \(\mathbb C^N\), so its analytification is Stein and its underlying continuous map is a homotopy equivalence. Pull back the topological bundles E,F from §1 to this ACTUAL affine replacement.

**Stein Oka–Grauert step:** every topological complex vector bundle on a Stein manifold admits a compatible holomorphic vector bundle structure, unique up to holomorphic isomorphism for its fixed topological isomorphism class. Therefore the pulled-back smooth E,F acquire genuinely holomorphic structures \(E^{an},F^{an}\) on \(J(X)^{an}\), without claiming they are algebraic.

For each integer k, \(E^{an}\to F^{an}\otimes\pi^*L^k\) is a holomorphic Hom bundle. Holomorphic generation and generic transversality on Stein spaces (Cartan Theorem A, supplemented by the standard holomorphic transversality theorem for sections) permit holomorphic matrix maps whose rank-drop loci \(D_k^{an}\) are closed **complex-analytic** determinantal cycles, with the proper analytic Thom–Porteous/cohomological fundamental class:
\[
 \mathrm{cl}^{an}(D_k^{an})
 =\pi^*c_p(F\otimes L^k-E).
\]
The all-K exact *INTEGER* interpolation then produces an explicitly target-born signed finite COMPLEX-ANALYTIC cycle
\[
 T_{\alpha}^{an}
  =\frac{(-1)^{p-1}}{(p-1)!N}
    \sum_{j=0}^p\lambda_{K,p,j}[D_{K+j}^{an}],
 \quad \mathrm{cl}^{an}(T_{\alpha}^{an})=\pi^*\alpha.
\]
Unlike the symplectic-only route, every sheet here is genuinely **integrable complex-analytic**. The construction is on the affine replacement J(X), not an original-X Chow cycle. The analytic existence/transversality package should be checked against exact primary sources before being formally promoted beyond this project mathematics checkpoint.

**Why this is a sharper and genuinely necessary boundary:** for the ORIGINAL projective X the algebraic Chow pullback \(\pi^*:CH^p(X)\to CH^p(J(X))\) is an isomorphism. If this particular analytic packet can be replaced by a rational **algebraic** cycle on J(X), homotopy invariance descends it unambiguously to a bona fide Chow cycle on original X with canonical class alpha. No unsolved analytic-to-scheme conversion is hidden in the descent itself; the only new birth is converting the target-born holomorphic *analytic* packet to a regular algebraic cycle when alpha has rational (p,p) type.

**Non-Hodge K3 firewall, ruling out automatic Stein algebraization.** Take a projective K3 surface X with Picard rank 1 and choose an integral class \(\beta\in H^2(X,\mathbb Z)\) that is NOT of Hodge type (1,1). Its pullback to the affine Stein Jouanolou J(X) is the Chern class of a topological complex line bundle, hence by Oka of an actual holomorphic line bundle. Cartan Theorem A gives a nonzero holomorphic section, whose zero set is a genuine analytic divisor (because nontrivial c1 prevents nowhere-vanishing). Its Betti class is \(\pi^*\beta\). It CANNOT be an algebraic divisor: otherwise Chow homotopy invariance would descend an algebraic divisor to original X, contradicting the Lefschetz (1,1) necessity on X. Therefore *even a projective-origin integral analytic divisor on an affine J(X) need not be algebraic*. The additional input **must exploit the rational Hodge type condition**. Without it, the proposed algebraization law is outright FALSE already in codimension one.

For Hodge p=1 the correct algebraization uses the original-X exponential-sequence Lefschetz (1,1) theorem, and Stein Oka uniqueness then identifies the holomorphic line bundle with an algebraic pullback. For p>=2 the remaining issue is a new Hodge-conditioned algebraization theorem for finite signed analytic determinantal packets; no such theorem has been established here and it is at least as strong as the desired Gate 3 conclusion in this class of packets. There is no known valid unconditional lift just from projective origin.

**Status:** Steps 1–4 supply actual target-born, finite signed, topological degeneracy packets on every original X. This §5b builds complex-analytic degeneracy packets on its affine Stein replacement using named standard theorems (source verification outstanding). It reaches holomorphic geometry but NOT algebraic Chow, and cannot solve Gate 3 without a genuinely new use of Hodge type.

## 5c. A necessary correction: algebraize the COHOMOLOGY CLASS, not each chosen analytic sheet

The analytic packet in §5b depends on noncanonical holomorphic maps. Its specific analytic zero sets need not be algebraic **even when the corresponding Hodge class is already algebraic**. On any positive-dimensional affine complex variety U with a nonconstant algebraic regular function f:U->C whose image is cofinite, the entire holomorphic function exp(f)-1 has analytic zero divisor
\[
 \bigcup_{m\in\mathbb Z}\{f=2\pi i m\}.
\]
There are infinitely many nonempty distinct algebraic hypersurface fibers, so their whole locally finite analytic union is not a Zariski-closed algebraic divisor of finite type. Yet exp(f)-1 is a globally principal holomorphic function: this nonalgebraic analytic divisor has Chern class 0, which is certainly algebraic (represented by the zero Chow cycle).

Consequently a proposed Hodge-only law demanding that EVERY explicitly chosen analytic determinant D_k be itself algebraic is false even in the easiest class-0 case. The needed geometric feat is **replacement of the target-born signed analytic packet by SOME algebraic rational cycle with the SAME canonical class**, not literal algebraization of the arbitrary holomorphic zero sets. In particular an analytic source being holomorphic is neither sufficient nor, by itself, the correct exact geometric output.

## 5d. Exact GST boundary-order diagnostic: a PURE (1,1) class carried by a HOLomorphic 2-form

We need the correct analytic/de Rham dictionary before applying any "Hodge filter ⇒ algebraic growth" principle to §5b. The project already has an explicit rank-one algebraic idempotent on the affine Jouanolou quadric \(Q_2=J(\mathbb P^1)\):
\[
 Q_2=\{(x,y,z)\in\mathbb A^3_{\mathbb C}:xy=z(1-z)\},\quad
 P=\begin{pmatrix}z&x\\y&1-z\end{pmatrix}.
\]
**Direct Wolfram check:** \(P^2-P=(xy-z(1-z))I_2\), hence P²=P exactly on Q₂. The line im(P) is an ACTUAL algebraic line bundle, with nonzero integral c1 from the projective base. Its Grassmann connection \(\nabla=P\,d\) has Chern curvature trace
\[
\boxed{
 \operatorname{tr}\bigl(P\,dP\wedge dP\bigr)
  =(2z-1)\,dx\wedge dy
    +2x\,dy\wedge dz+2y\,dz\wedge dx
  =-\frac{dx\wedge dz}{x}\quad (x\ne0).
}
\]
The last equality follows by differentiating xy=z(1-z): \(dy=(1-2z)dz/x-z(1-z)dx/x^2\). Wolfram verified its exact scalar coefficient is -1, without numerical approximation. The 2-form is REGULAR on the affine quadric (the polynomial expression proves global regularity) and nowhere vanishing. It represents a nonzero algebraic line-bundle first Chern class, after the usual 1/(2πi) normalization.

**Critical Hodge point:** \(H^2(Q_2,\mathbb Q)\cong H^2(\mathbb P^1,\mathbb Q)\) is a pure (1,1) rational Hodge structure: its Deligne filtration has \(F^2 H^2(Q_2)=0\). Yet the Chern character above is represented by a regular **holomorphic (2,0) differential form** on the affine Q₂. There is NO contradiction: the Hodge filtration of an OPEN algebraic variety is *not* computed by naively truncating its unrestricted regular algebraic de Rham forms. It is computed using a normal-crossing COMPACTIFICATION with logarithmic forms and controlled poles.

Indeed, the natural projective completion is the smooth quadric \(\bar Q_2=\{XY=Z(T-Z)\}\subset\mathbb P^3\), and the infinity divisor D={T=0} is a smooth hyperplane conic. Adjunction gives \(K_{\bar Q_2}=-2H=-2D\). Since the displayed regular holomorphic 2-form is nowhere vanishing on Q₂ and its only divisor lies at infinity, it has a **DOUBLE POLE** along D. It is not a global logarithmic 2-form with at most simple pole. The apparently holomorphic degree-two representative therefore lies in F¹ but not F² of the intrinsic mixed Hodge structure, consistently with its original (1,1) source.

**New practical constraint for Gate 3:** merely converting the arbitrary-X target-born smooth K class into a holomorphic bundle on the affine Jouanolou model, or exhibiting holomorphic Chern-curvature forms, does NOT establish the projective Hodge filtration or algebraicity. One must control boundary growth/pole order and realize the actual rational class by a REGULAR ALGEBRAIC idempotent/projective module, not by a generic Oka holomorphic idempotent with possible essential growth.

On the first nontrivial case Q₂, the polynomial idempotent P supplies this extra finite-growth certificate explicitly. For arbitrary primitive alpha the need is a *target-dependent finite-growth holomorphic projector* (or another actual algebraic coherent complex) without assuming such a projector as input. Proving universal existence of that certificate for exactly the rational (p,p) targets would produce the sought Chow cycle; this project has not proved it. The explicit Q₂ calculation rules out fake Hodge-filtration comparisons in a proposed proof.

## 5e. GST noncommutative ghost: the Hodge trace can vanish while curvature blocks integrability

There is a second all-X structural reason that merely checking scalar Hodge/Chern characters cannot convert the target-born bundle into a holomorphic bundle. In a local complex coordinate chart \(\mathbb C^2\), start on the SMOOTH trivial rank-two bundle with the (0,1)-operator
\[
 D_{\bar 1}=\partial_{\bar z_1}+A,\qquad
 D_{\bar 2}=\partial_{\bar z_2}+B,\quad
 A=\begin{pmatrix}0&1\\0&0\end{pmatrix},\
 B=\begin{pmatrix}0&0\\1&0\end{pmatrix}.
\]
The actual nonabelian Maurer–Cartan curvature is
\[
 [D_{\bar1},D_{\bar2}]=[A,B]
     =\operatorname{diag}(1,-1)\ne0.
\]
Its **scalar first trace vanishes**, \(\mathrm{tr}[A,B]=0\), but its determinant is -1, its two eigenvalues are ±1, its rank is 2, and \(\mathrm{tr}([A,B]^2)=2\). Wolfram verified all five exact assertions. Any putative locally (0,1)-parallel section must satisfy \([A,B]s=0\), hence \(s=0\). There are NO nonzero local flat sections for this fixed operator, despite underlying smooth bundle being topologically trivial and its rational Chern classes vanishing.

Tensoring with the (0,1)-operator of any holomorphic algebraic line bundle changes the connection by a scalar integrable (0,1)-operator, whose extra (0,2)-curvature is zero; the nonabelian commutator remains the same. Therefore even arbitrary positive twists do NOT fix this chosen operator's integrability.

This is NOT a proof that the underlying trivial bundle admits no alternate holomorphic structure: of course it does. It is a decisive obstruction to the **specific attempted solver** "trace/period equations vanish ⇒ the constructed arbitrary connection becomes holomorphic after positive twisting." Scalar Chern-Weil invariants and rational Hodge conditions cannot automatically eliminate a noncommutative End(E)-valued (0,2) curvature ghost. A valid all-X algebraization must vary the full holomorphic structure or use signed coherent/perfect-complex geometry, and must solve the actual Maurer–Cartan equation, not only its trace.

## 6. Honest remaining nonlinear construction challenge

To **solve** the user-requested all-varieties Hodge theorem using the new finite packet, one must construct for each X,p,Hodge-alpha enough HONEST complex-analytic/algebraic determinants A_k on the SAME original X whose canonical classes are the P(k), or build an independent holomorphic/coherent perfect-complex avatar realizing the target-born virtual K-class. The Hodge condition is absent from Steps 1–3 and MUST enter this new map from smooth determinant geometry into complex analyticity. Ordinary smooth transversality cannot provide it, HYM polystability is impossible for nonzero normalized primitive packages, and simply applying the existing algebraic GST orbit to existing algebraic seeds cannot manufacture the missing direction.

The next viable attack is TARGET-DEPENDENT **signed, unstable/coherent determinantal geometry**, not more old-cycle transformations and not a fictitious "zero-calibration" law. The rational class equality has been constructively solved **in homology**, not in Chow. The universal Hodge conjecture remains OPEN.

**Checks:** exact symbolic Wolfram p=2 and p=3 formulas, full all-p finite difference derivation; no local Lean installation and no GitHub Actions workflow was launched. The external analytic and topological transversality theorems should be source-authenticated before any claim of independently kernel-verified implementation.
