# Mathbox — geometric CM isogeny projector onto exceptional Weil Hodge classes in EVERY codimension

**Target remains:** For all smooth projective complex X, all p and all prescribed rational (p,p) Hodge classes alpha, construct a true native algebraic cycle on original X with canonical geometric Betti class alpha. This route attacks an exceptional CM Hodge subspace that ordinary ambient Chern/Adams generators do not reach.

**Date / checkpoint:** 2026-10-17. **Initial SHA:** 0f6d731d0906cb1e2e8768057c94e53f241421f6. **Research branch:** research/gpt6-native-point-primitive-span-20261017.

## Geometric problem and actual objects

Let A be a complex abelian variety of dimension 2p (p>=1), of Weil type for K=Q(i): H¹(A,Q) is free of K-rank 2p and K acts on the complex Hodge H^(1,0) with equal sigma and conjugate sigma multiplicities p,p. Its complexified rational H¹ splits into 2p-dimensional K-eigenspaces W_sigma, W_barsigma; each has Hodge signature (p,p). The genuine rational Weil Hodge space

\[
 W_{\mathrm{Weil},p}\otimes_{\mathbb Q}\mathbb C
   =\bigwedge^{2p}W_\sigma\oplus\bigwedge^{2p}W_{\bar\sigma}
     \subset H^{2p}(A,\mathbb C)
\]
has rational dimension exactly **two**, with both complex lines of Hodge type (p,p).

The CM ring acts by actual algebraic group endomorphisms (isogenies) on A, not abstract formal GST operators. Let f=[2+i]:A→A; on H¹ its eigenvalues are lambda=2+i and mu=2−i. On H^(2p)=wedge^(2p)H¹ the r-th eigen-sector is

\[
 e_r=\lambda^r\mu^{2p-r},\qquad
 \mathrm{multiplicity}\;\binom{2p}r^2,\qquad 0\le r\le 2p.
\]
The pure eigensectors r=0 and 2p are precisely the two Weil Hodge lines. The central sector r=p has eigenvalue 5^p. All sectors are distinguishable because lambda/mu=(3+4i)/5 is **not a root of unity**: its sum with its conjugate is the rational number 6/5, which is not an integer, while a root of unity's rational algebraic-integer trace would be an integer.

## Exact all-p algebraic polynomial projector (constructive CRT)

Let t be a rational polynomial variable, set n=5^(2p), and for 0≤r<p define

\[
 G_r(t)=(t-e_r)(t-e_{2p-r})
       =t^2-2\Re(e_r)t+n\in\mathbb Z[t].
\]
The remaining central factor is t−5^p. Set
\[
 N_p(t)=(t-5^p)\prod_{r=1}^{p-1}G_r(t),\qquad
 G_0(t)=t^2-2a t+n,\; a=\Re(e_0).
\]
Reduce N_p modulo G0: N_p≡A_0+B_0 t. Since all spectral eigenvalues are distinct, this residue is nonzero modulo G0. Define
\[
 D=A_0(A_0+2aB_0)+nB_0^2\ne0
\]
and the **completely explicit rational polynomial**
\[
 \boxed{P_p(t)=
 N_p(t)\frac{A_0+2aB_0-B_0t}{D}.}
\]
The factor in the numerator is the inverse of A_0+B_0t modulo G0, because t²≡2a t−n modulo G0. Consequently P_p(t)≡1 mod G0 and P_p(t)≡0 mod N_p. By CRT, P_p(e_r)=1 for r=0 or r=2p and zero for all other r, and P_p²≡P_p modulo the minimal polynomial G0*N_p of f* on H^(2p).

**Geometric algebraic-correspondence construction:** Every power of the genuine isogeny pullback f* on rational Betti cohomology is realized by the transpose graph of an actual algebraic isogeny f^j. Hence the above rational polynomial P_p(f*) is the cohomological action of a **genuine rational algebraic codimension-2p correspondence on A×A**, with rank exactly two on H^(2p) and image exactly the Weil Hodge subspace. No Hodge class or algebraic preimage was inserted into its construction.

For p=2 there is a smaller formula using f=[1+i]. The normalized action U=f*/4 on H⁴ satisfies U⁴=1, with eigenvalues −1,−i,1,i,−1 and multiplicities 1,16,36,16,1. Its minus-one projector is
\[
 P_{\mathrm W}=\tfrac14(I-U+U²-U³)
             =\tfrac14 I-\tfrac1{16}f^*+\tfrac1{64}(f^*)²-\tfrac1{256}(f^*)³.
\]
This also is an actual algebraic correspondence on A×A. The Lean module GSTUniversalCMArithmeticObstruction.lean contains the ring/field proof of idempotence modulo U⁴−1, the minus-one/plus-one/quadratic eigensector filters, and the dimension census 70→2.

## Exact Wolfram and GitHub certificate

Wolfram determined that for p=2 and f=[2+i],
G0=t²+14t+625 and N=(t−25)(t²−30t+625).
For p=3, G0=t²+234t+15625 and N=(t−125)(t²−150t+15625)(t²+70t+15625).
Using PolynomialExtendedGCD, it found an exact rational polynomial P_p with P_p(e_r)=[1,0,...,0,1] for both p=2 and p=3. The p=2 [1+i] projector polynomial is 1/4−t/16+t²/64−t³/256 and has scalar idempotent factor
(P²−P)=(t⁴−256)(t²−8t+48)/65536.

The repo's pure standard-library exact-rational certificate
research/computations/weil_cm_correspondence_projector.py computes eigenvalues, conjugate quadratic spectral factors, Bezout inverse, rational projector and idempotence remainders for **all p=1,...,8**, and checks dimension C(4p,2p) with rank 2 in each case. [GitHub Actions #39058710211](https://github.com/kyo-oo/HC-PROOF/actions/runs/39058710211) **SUCCESS** at source SHA 061a6087a666e934ac3edc84bdeb70a6a1f09216, with complete pinned Hodge Lean integration and sorryAx check, evidence artifact 12109993388, digest sha256:9d73715797ccb4df084827b4b0b63adc6711dff88e65ddcddfd9efc71cbee34a. Its exact log enumerates p=1..8, rank2 and degree2p projectors; the uniform CRT argument above supplies the all-p proof independently of that finite test.

## What this actually advances and what remains

This explicitly geometrizes the previous GST-CM formal higher-degree Hodge charge atoms using genuine complex abelian varieties and actual algebraic CM isogenies, producing a **canonical algebraic-correspondence projector** whose image is a difficult rational Weil Hodge space in every middle codimension p. This is stronger than the earlier raw character-lattice sums and finite CM trace tests: the sector really exists as a Hodge subspace of smooth projective geometry and has an independently constructed algebraic projector.

**Crucial distinction:** An algebraic correspondence projecting onto a two-dimensional Hodge subspace is not by itself an algebraic representative of either of its Hodge classes. The projector may act as zero on all currently available algebraic source cycles while acting as the identity on the missing Weil classes. Applying the projector to a *prescribed Weil Hodge class* produces the same class cohomologically, not an algebraic cycle. There is no illicit step here claiming that the projector manufactures its own target witnesses.

**Next exact actual-source obligation (Gate 3):** Construct at least two independent genuine algebraic codimension-p source cycles on the original Weil-type A whose projected classes span W_Weil,p, and then extend the source mechanism to arbitrary original X. For a first positive test, take a split Weil-type abelian fourfold built from CM elliptic curves and identify algebraic graph/divisor intersections with nonzero CM projector image; determine which geometric deformation obstruction prevents transfer to an arbitrary Weil-type fourfold. This explicitly tests **source birth**, rather than constructing another representation theorem conditional on source existence.

## BREAKTHROUGH — two genuine exceptional Weil cycles constructed on split CM elliptic powers, every p

**The source-production step is solved outright on the split Weil locus, not assumed.** Let E=C/(Z+iZ), A=E^(2p), and embed Q(i) into End(A) by i on the first p elliptic factors and -i on the last p. This is an actual smooth projective Weil-type 2p-fold of balanced Hodge signature (p,p). In the rational H¹ symplectic basis x_i,y_i of each elliptic factor, define the *genuine mixed algebraic divisor classes*
\[
 D_i=x_i\wedge y_{p+i}-y_i\wedge x_{p+i},\qquad
 C_i=x_i\wedge x_{p+i}+y_i\wedge y_{p+i}
\]
for i=1,...,p. Each D_i is the mixed Poincare/diagonal graph divisor on E_i×E_(p+i), subtracting the two factor classes; C_i is likewise an algebraic graph divisor, because the actual isogeny [1+i] on the first factor and [1−i] on the opposite-K factor satisfies f^*D_i=−2C_i.

Thus the two codimension-p classes
\[
 Z_D=\prod_{i=1}^{p}D_i,\qquad
 Z_C=C_1\prod_{i=2}^{p}D_i
\]
are **honest native rational algebraic cycles on the original A**, with no specified Hodge cycle or K-theory preimage as a premise. Apply the all-p **algebraic** CM projector Π_p=P_p([2+i]^*) constructed above:
\[
  W_D=\Pi_p Z_D,\qquad W_C=\Pi_p Z_C.
\]
These are still actual algebraic cycles, since pullbacks by the actual isogenies [2+i]^k are native algebraic operations and Π_p has rational coefficients.

**Uniform exact nonzero and independent certificate.** On the two genuine complex Weil eigenspaces Ωσ, Ωbarσ, write u=i/2 and -u=-i/2. The mixed divisors decompose into the two pure-eigen components:
\[
 \Pi_p[Z_D]=u^p\Omega_\sigma+(-u)^p\Omega_{\bar\sigma},
 \qquad
 \Pi_p[Z_C]=\tfrac12u^{p-1}\Omega_\sigma+
            \tfrac12(-u)^{p-1}\Omega_{\bar\sigma}.
\]
The determinant of their coefficient matrix is
\[
  \boxed{\det=
    \tfrac12\bigl(u^p(-u)^{p-1}-(-u)^p u^{p-1}\bigr)
    =u^p(-u)^{p-1}
    =\frac{i}{2^{2p-1}}\ne0.}
\]
Therefore **both projected cycles are nonzero and rationally linearly independent**, and since the whole Weil rational Hodge space has rank 2, **they span every exceptional rational Weil class on the split abelian 2p-fold, for every p>=1**. This is a native source construction, not a conditional Gram-rank theorem. It gives a direct geometric realization of the user's GST imaginary-quadratic native-rank forcing method on a genuine family of smooth projective varieties in every codimension.

**Actual existing GST theorem invoked:** GSTCMQuadraticNativeRankForcing.imaginary_quadratic_CM_no_rational_eigenline (and its geometric realization in CM_actual_correspondence_spine_transverse): on the rank-two Weil eigenspace, the actual algebraic isogeny [2+i] has imaginary quadratic minimal polynomial G0(t) with nonreal complex roots. Any nonzero native projected source has a rationally independent algebraic CM translate. This provides a second, independent mathematical proof of rank two once the first native source W_D has been explicitly constructed. The determinant argument also exhibits two explicit sources without appealing to an abstract nonzero witness.

**Independent full rational Betti test at p=2:** In H¹(E^4,Q) with ordered basis (x1,y1,x2,y2,x3,y3,x4,y4), the exact sparse exterior-algebra computation applies
\[
 \Pi_{2}=(I-T/4+T^2/16-T^3/64)/4,\qquad T=[1+i]^*|_{H^4}
\]
to the two actual codimension-two cycle classes D_1D_2 and C_1D_2. Both outputs have eight nonzero rational 4-form coordinates (coefficients ±1/2); their monomial supports are disjoint, so they are independent. The exact T action sends each to -4 times itself and T⁴ acts by 256. The full wedge calculation is auditable in research/computations/split_weil_native_algebraic_sources.py, with no external packages or floating-point approximation.

**Exact machine evidence:** Wolfram independently calculated \(\det=i/2^{2p-1}\) for p=1,..,8; the general determinant identity is an elementary symbolic identity and has been added to GSTUniversalCMArithmeticObstruction.lean as cmWeilSplitSourceDeterminant and _nonzero, for every characteristic-zero field and all p. The pure Python certificate verifies all-p determinant cases p=1,..,12, plus every one of the p=2 exterior coefficients. [GitHub Actions #39059438328](https://github.com/kyo-oo/HC-PROOF/actions/runs/39059438328) is SUCCESS at SHA 20071f46b1a8ce00e5f930315c81b8c2b44254fe, with the complete pinned GST Hodge integration and sorryAx audit. The all-p determinant theorem is now **Lean GREEN** in [Actions #39059702764](https://github.com/kyo-oo/HC-PROOF/actions/runs/39059702764), SUCCESS at SHA 953dee455337ffdbbe85301b99d1dbce8876d51c, including the pinned 247-module Hodge integration and sorryAx audit. Evidence artifact 12111325492, sha256:6a95df4eed8a7213f334aba15eb45c107e6f494ad5b8ac28583f4a1e25a4c1fb.

## Exact remaining deformation-to-arbitrary-X obstacle

This positive all-p construction works because the split CM variety E^(2p) has **additional mixed graph divisors** connecting the two K-signature groups. On a very general simple Weil-type abelian variety, the rational Neron–Severi space is generated by the polarization and those mixed factor-graph divisors do **not** persist as algebraic divisors. Hence their products cannot simply be spread as divisor intersections throughout the Weil-type moduli family; nevertheless the two rank-one Weil Hodge eigensectors persist as rational (p,p) classes and the CM correspondence projector remains algebraic. This isolates the exact next geometric discovery: **deform or replace the split native cycles by genuinely higher-codimension algebraic cycles on a non-split Weil-type original A**, verifying their canonical Betti classes. Do not assume that cycles on one split fiber automatically deform across moduli. From there develop an arbitrary-X incidence construction capable of targeting general primitive rational Hodge α.

This is a real completed **native source-production subcase in every p** plus a testable algebro-geometric deformation obstruction; it is not a proof of the all-varieties Hodge conjecture.


## Focused follow-through (18 October): exactly one nonsplit original-X source, not another family

The actual target is unchanged. The special split E^(2p) construction is a **successful boundary example** and not a source for a general variety. We now freeze the smallest decisive transfer test at **one genuinely nonsplit Weil-type abelian fourfold with rank-one rational Néron–Severi group**. Every proposed universal GST source-construction mechanism must pass this fixed test before being promoted as all-X progress.

### 1. The source obligation has been compressed from a basis to ONE irreducible subvariety

Let A be a Weil-type abelian 2p-fold with its genuine rational rank-two Weil Hodge subspace W and actual algebraic CM isogeny f=[2+i]. The Weil projector Π_W is an algebraic correspondence. Its restriction T=f* to W has irreducible polynomial
\[
 t^2-2a t+(a^2+b^2),\qquad b\ne0.
\]
In a rational companion basis let a nonzero projected genuine algebraic source z=(x,y). Then
\[
 Tz=(-(a^2+b^2)y,\ x+2ay),\quad
 D=\det(z,Tz)=(x+ay)^2+(by)^2>0.
\]
For EVERY prescribed rational target α=(u,v)∈W, define exact rational coefficients
\[
 c=\frac{u(x+2ay)+(a^2+b^2)yv}{D},\qquad
 e=\frac{xv-yu}{D}.
\]
The genuine native cycle \(c\,\Pi_W Z+e\,\Pi_W f^*Z\) has canonical Betti class α, whenever one original-X algebraic cycle Z with Π_W cl(Z)=z≠0 has been constructed. This is exact coefficient recovery, not a presumed full-rank Gram matrix. The new functions \`cmWeilOneSourceCoeff0\`, \`cmWeilOneSourceCoeff1\` and Lean theorem \`cmWeilOneSourceReconstruction\` verify every coefficient, and \`cmWeilOneSourceDet_pos\` proves positivity without special-case numerical assumptions. [Lean Actions #39061912241](https://github.com/kyo-oo/HC-PROOF/actions/runs/39061912241) **GREEN** at SHA \`534349905156d5b81f9857640abc55f6194b1eb7\`, including 247-module integration and sorryAx audit. Wolfram verified the formula for the genuine p=2,p=3,p=4 CM characteristic values and a prescribed test target (7,-3).

Moreover every rational algebraic cycle on projective A has a finite presentation in genuine irreducible codimension-p components (existing \`GSTCompactNativeCyclePresentation\`). By linearity, if Π_W detects a nonzero rational cycle then it detects ONE irreducible component. The new theorem \`cmWeilProjectedFiniteNativeSourceWitness\` proves this source extraction over arbitrary rational native modules. [Lean Actions #39062250730](https://github.com/kyo-oo/HC-PROOF/actions/runs/39062250730) **GREEN** at source SHA \`d9fb6c42a45ab1869c8b527f59be05f607ae7c08\`.

**ONE concrete geometric target for the nonsplit test:**
\[
\boxed{\text{Construct one irreducible codimension-two subvariety }
V\subset A\text{ with }\Pi_W\operatorname{cl}_A(V)\ne0,}
\]
for a general nonsplit rank-one-Picard Weil-type fourfold A. If it exists, actual CM translates give the full exceptional rational Weil (2,2) space. It is not currently constructed by this proof program.

### 2. Exact structural reason why the original split-cycle source does not deform

The Weil rational local system W itself **remains of Hodge type (p,p)** throughout a K-linear polarized deformation of fixed signature (p,p): the K-eigenspace H¹_σ has complex dimension 2p, and its Hodge decomposition always has p holomorphic and p antiholomorphic dimensions; hence the top wedge ∧^(2p) H¹_σ always has bidegree (p,p), and likewise its conjugate. The algebraic CM projector remains a global relative algebraic correspondence because the K action persists.

But the individual mixed graph divisor D_i from split E^(2p) is not a Hodge divisor under a general K-linear deformation. The simplest explicit first-order check occurs for p=2. Inside a four-dimensional complex σ-eigenspace let the split holomorphic basis contain e₁,e₂ and antiholomorphic basis f₁,f₂. Take the standard off-diagonal local deformation
\[
 u_1=e_1+t f_2,\quad u_2=e_2,\qquad
 v_1=f_1,\quad v_2=f_2+t e_1,
 \quad 1-t^2\ne0 .
\]
Here (u₁,u₂) spans the deformed holomorphic subspace and (v₁,v₂) the complementary antiholomorphic subspace. Then
\[
 e_1\wedge f_1
   =\frac{u_1\wedge v_1 - t\,v_2\wedge v_1}{1-t^2}.
\]
Its **(0,2) coefficient is exactly −t/(1−t²)** and has first derivative −1 at t=0. Therefore the old divisor class has nonzero first-order Hodge obstruction, while the **top exterior determinant**
\[
 e_1\wedge e_2\wedge f_1\wedge f_2
     \in \bigwedge^2 H^{1,0}_\sigma(t)\wedge\bigwedge^2H^{0,1}_\sigma(t)
\]
retains bidegree (2,2). Wolfram evaluated the full 2×2 basis change, its determinant 1−t² and the nonzero first-order (0,2) coefficient −1 exactly. This is an explicit local linearized Hodge model; a full algebraic family must additionally satisfy the chosen polarization compatibility, and no cycle deformation is inferred from this calculation.

**Key distinction:** being a Hodge class on every fiber does not imply being an algebraic cycle on every fiber. The split projected class is a flat rational Hodge section, but its source divisor geometry cannot simply be transported to a nonsplit fiber.

### 3. Precise generic divisor-channel no-go, still inside Gate 3

On a nonsplit Weil-type abelian 2p-fold A (p≥2) with \(\mathrm{NS}(A)_\mathbb Q=\mathbb Q\,\theta\), every rational divisor product of codimension p is a multiple of \(\theta^p\). The CM isogeny [2+i] acts on the polarization by norm 5, so \(T\theta^p=5^p\theta^p\). The explicit all-p Weil projector P_p(T) has polynomial factor T−5^p I; hence
\[
 \boxed{\Pi_W(\theta^p)=0.}
\]
In particular, applying more CM-graph correspondences, combinations of divisor products, or projector polynomials to the **known polarization algebra** never constructs the required one nonzero Weil source. The lemma \`cmWeilCentralEigenspaceFilter_kills_ambient\` formalizes the eigenvector-killing identity for arbitrary rational modules and arbitrary p as an exact GST source-channel obstruction. This is not a statement that the desired Hodge classes are nonalgebraic; it identifies which source-generation methods do not reach them.

### 4. Exact geometric route criterion: one dominating higher-codimension Chow family

Fix an integral positive-dimensional base S of polarized nonsplit Weil-type fourfolds with universal abelian family A/S carrying its K action. The rank-two Weil rational local system and its algebraic projector are globally defined. On a flat relative irreducible family of codimension-two subvarieties V⊂A_s, the projected Betti class Π_W cl(V_s) is locally constant. If a relative Hilbert/Chow component **dominates S** and its generic projected class is nonzero, it produces exactly the one source required above and therefore both exceptional algebraic Weil directions on the general original fiber.

A single cycle on a special split fiber does not give such a dominating family. Relative Hilbert schemes have countably many Hilbert-polynomial components, each proper over S; their images are constructible/closed for the projective Hilbert parametrization. Existence of detected cycles on a *very general* fiber would force one component to dominate S (the standard uncountable-base countability argument). This is a **testable source-birth criterion**, not an assertion that the requisite component has been constructed.

**No further family switching in this route:** the next source-production attempt is specifically to construct or detect a dominating codimension-two relative Chow component with nonzero Weil projection on a genuinely nonsplit A. This hard case is a necessary test of any method claimed to work on arbitrary X. After that, the complete all-X Hodge target retains its original separate source-generation obligation.
