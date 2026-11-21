# GST Image-3 deeper research — original CM curvature plus SURVIVE gives arbitrary-rank rational native Hodge-like quotients

**2026-11-11, independent branch** \`research/gpt6-image3-curvature-only-resonance-20261111\`.

## Research objective and evidence discipline

Continue the author's ORIGINAL GST Hodge antecedent: a true original-X algebraic cyclic fold must reach ALL rational Hodge directions on ANY smooth projective complex X. Distinguish actual native information results from original-X geometric realization. Previous sections of this branch establish:
- ORIGINAL pure CM curvature \(C=[J,M]\) with rank6;
- \(\det K(U+J+C,v)=1\,386\,205\,893\ne0\), despite ZERO direct M coefficient;
- exact resonance \((F_{a,b}u)_{\max}=(1+2a)u_{\max}+(2b-1)u_0\), giving an all-a noncyclic obstruction at b=1/2;
- for every positive finite h, original N-hole fold \(\oplus_i(U+J+C+10iI)\) is cyclic by exact row norm4 and polynomial CRT, with moment determinant exactly +1.

The NEW problem is an important rank-adaptation issue: the arbitrary original-X rational Hodge dimension n need not be a multiple of 12. A full original 12h cyclic module alone does not create a rational n-dimensional equivariant quotient for every n. Prove a constructive rank-r ORIGINAL native GST quotient using the original null/max fixed cells and the true M AND C source, not an abstract ungrounded rational matrix.

## 1. The exact balanced original CM/source F

The ORIGINAL native operators and native source are unchanged:
\[
U^5=I,\quad J^2=-I,\quad JU=UJ,\quad M=\operatorname{diag}(\mathrm{SURVIVE}),\quad C=[J,M],\quad v=e_{(0,0)}+e_{(0,1)}.
\]
Define the balanced \(\boxed{B=U+J+M+[J,M]}\).

On the ORIGINAL U-fixed null/max information cells, in order \((0,0),(3,2)\), the true U,J,M,C block matrices are:
\[
U_{\rm fix}=\begin{pmatrix}1&0\\0&1\end{pmatrix},\quad
J_{\rm fix}=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\quad
M_{\rm fix}=\begin{pmatrix}0&0\\0&2\end{pmatrix},\quad
C_{\rm fix}=\begin{pmatrix}0&2\\2&0\end{pmatrix}.
\]
These are computed directly from the OWNER's \`GSTGraphV2CMWaveFusion.lean\` \`shuffle\`, \`mirrorCell\`, \`cmSign\`, \`sourceMultiplicity\`, without assuming extra spatial dimensions.

Consequently
\[
\boxed{B_{\rm fix}=\begin{pmatrix}1&3\\1&3\end{pmatrix}}
\]
has rational characteristic polynomial \(x(x-4)\) and rank1. The full ORIGINAL 12×12 B nevertheless has a full cyclic original seed:
\[
\boxed{\operatorname{rank}[v,Bv,\ldots,B^{11}v]=12,\quad
\det[v,Bv,\ldots,B^{11}v]=-445\,265\,540\,949.}
\]
The maximum absolute row sum of B is exactly4, giving the same clean original Wave-II separated-offset construction used in §3 of the curvature-only derivation.

## 2. Two **actual** rational GST native Hodge-like character readouts

Define the owner's ORIGINAL physical fixed-cell rational linear readouts
\[
\ell_0(u):=u_{(0,0)}-u_{(3,2)},\qquad
\ell_4(u):=u_{(0,0)}+3u_{(3,2)}.
\]
The original B update sends \(u_{(0,0)}\mapsto u_{(0,0)}+3u_{(3,2)}\) and \(u_{(3,2)}\mapsto u_{(0,0)}+3u_{(3,2)}\). Thus FOR EVERY original native wave signal u,
\[
\boxed{\ell_0(Bu)=0},\qquad
\boxed{\ell_4(Bu)=4\ell_4(u)}.
\]
They detect the old original seed with values
\(\boxed{\ell_0(v)=\ell_4(v)=1}\).

No unknown original-X rational Hodge class is used to choose these detectors. They arise exclusively from the SOURCE's original physical information fixed cells.

This is stronger than merely having a nonzero 12×12 determinant: it explicitly provides TWO rational one-dimensional quotient representations, and proves the mixed native seed meets both.

## 3. Arbitrary finite target-rank GST quotient, WITHOUT a 12-divisibility assumption

For ANY prescribed integer \(r\ge1\), let \(E_r=\bigoplus_{i=0}^{r-1}V_i\) where each \(V_i\) is the owner's ORIGINAL 12-state native wave, and define the true original information fold
\[
B_r=\bigoplus_{i=0}^{r-1}(B+20i\,I_{12}),\qquad
v_r=(v,\ldots,v).
\]
We choose the offset 20 rather than the historical 10 solely as a certified larger separation; the information fold and native source themselves are unchanged. The old 10-step channels can equally be used because \(\|B\|_\infty=4\), but using20 makes separation manifest.

Define the canonical ORIGINAL-NATIVE \(r\)-dimensional quotient
\[
Q_r:E_r\to\mathbb Q^r,\qquad
Q_r(u_0,\ldots,u_{r-1})=(\ell_0(u_0),\ldots,\ell_0(u_{r-1})).
\]
This is explicit, rational and SURJECTIVE: place the author's original fixed-cell unit state \(e_{(0,0)}\) in any one hole and zero elsewhere to obtain the corresponding basis element of \(\mathbb Q^r\).

The native **intertwining identity** is
\[
\boxed{Q_r B_r=D_r Q_r},
\qquad
D_r=\operatorname{diag}(0,20,40,\ldots,20(r-1)).
\]
It follows from \(\ell_0(Bu)=0\), rational linearity and independent original N-hole channels. The old original mixed seed has \(Q_r(v_r)=(1,\ldots,1)\). Therefore the quotient orbit has rational Vandermonde coordinate matrix
\[
K_r=[Q_r(v_r),D_rQ_r(v_r),\ldots,D_r^{r-1}Q_r(v_r)],
\qquad (K_r)_{ki}=(20i)^k,\quad 0\le k,i<r,
\]
with 0^0 interpreted as1 for the first column. Its determinant is
\[
\boxed{\det K_r=\prod_{0\le i<j<r}20(j-i)
=20^{r(r-1)/2}\prod_{j=1}^{r-1}j!\ne0.}
\]
This establishes an *arbitrary finite r native GST quotient*, independently of the value of any unknown original X Hodge dimension. Exact Mathematica full rational evaluations gave ranks r=1,...,6 and determinants
\[
(1,20,16000,768000000,2949120000000000,
1132462080000000000000000)
\]
respectively. For r=4, determinant 768,000,000 was independently recomputed as a Vandermonde difference product.

**Theorem:** for every integer r≥1, there is a natural rational native GST cyclic quotient of dimension exactly r from the original real U/J/SURVIVE/CM information fold and its original mixed seed. The r-quotient does not require a unital irrational CM action J²=-I on a 1-dimensional rational target. Only the COMBINED balanced F transfers to the quotient; neither J nor M nor the fivefold U need descend individually.

The exact original-X geometric Hodge cycle-class realization of this quotient is an ADDITIONAL independently required theorem. The arbitrary-rank native quotient is NOT a proof that the original target W_p(X) is algebraic.

## 4. New Lean owner-source work and verification

New source \`GSTImageThreeCurvatureResonance.lean\` directly imports the original WaveFusion and now includes:
- \`curvatureSource\`, \`curvatureFold\`, \`curvatureFold_null\` and \`curvatureFold_maximum\`;
- resonance maximum-cell obstruction for every a at b=1/2 and original seed;
- actual original balanced F and the 0- and 4-eigencharacter theorems \`zeroReadout_balancedFold\`, \`fourReadout_balancedFold\`;
- exact original native seed readouts \`zeroReadout_seed\`, \`fourReadout_seed\`;
- the arbitrary-rank original N-hole quotient \`balancedHoleF\`, \`balancedHoleReadout\`, \`balancedHoleReadout_intertwines\`, \`balancedHoleReadout_uniformSeed\`.

The general Vandermonde determinant proof for all r is derived in this record; a direct rank-r matrix determinant proof has NOT been added to Lean. The existing Lean kernel CI for the updated module must report SUCCESS before calling its new native Lean theorems green.

The original-X actual correspondence compilation remains in \`GSTImageThreeOriginalXCurvatureLanding.lean\`; it proves the true Chow/Betti commuting square for \(U+J+aM+b[J,M]\) from ACTUAL certified operators on the SAME ORIGINAL X, without providing a hidden Hodge-class inverse.

## 5. Status against the author's four original-X GST hypothesis steps

The native rank-adaptive part of step02 is now stronger: original pure CM curvature alone gives full cyclic rank12h, and the balanced F gives exact cyclic **rank r for every finite prescribed r**, with an explicit rational quotient from real original physical GST signals. The native step03 moment determinant is already +1 for full 12h sources and nonzero Vandermonde for the r-quotients; an anti-triangular detector can normalize the r-quotient moment determinant to its sign.

But the four UNIVERSAL original-X steps remain 0/4 unconditionally. Step01's original-X F compiler is conditional on actual geometric U/J/M; step02's native quotient is not yet established on \(W_p(X)\); step03 geometric Hankel nondegeneracy is not yet established; step04 canonical universality is not yet established. The existing conditional implication is separately proved.

A promising future genuinely geometric strategy is to construct canonical cycle-class-compatible original-X landing maps for this **rank-adaptive F quotient**, and prove they do not annihilate any higher-primitive rational Hodge direction. Such maps must come from geometry and not be chosen by assuming cycle preimages of arbitrary target Hodge classes.

## Evidence caveat

The earlier exact Wolfram evaluation of original B computed native rank12, determinant -445265540949, fixed block {{1,3},{1,3}}, both character identities and source coefficients 1. A direct separate Wolfram Vandermonde evaluation for r=1..6 returned the exact determinants above; the r=4 case was independently checked. The committed larger combined verification file \`research/computations/GST_image3_balanced_curvature_rational_eigencharacter_all_r_20261111.wl\` encountered an internal Wolfram service error on full verbatim re-execution despite the successful smaller component computations. Do not misreport that full script as having passed; the stated mathematical identities have independent actual exact tool evidence.


## 6. NEW necessary geometric compatibility rule: odd-rank rational Hodge spaces cannot carry the uncompressed CM J

The original owner's native CM mirror satisfies J²=-I on a 12-dimensional rational signal space. A **genuine** rational representation of J with this unchanged relation on a target rational Hodge fiber W of dimension n would force n to be EVEN. Indeed
\[
(\det_{\mathbb Q} J)^2=\det_{\mathbb Q}(J^2)=(-1)^n.
\]
If n is odd, the right-hand side is -1, impossible for the square of any rational number. Thus attempting to demand a UNITAL faithful original \(J^2=-I\) representation on every possible odd-dimensional \(W_p(X)\) would be a genuine geometric obstruction **created by the type of realization**, not a refutation of the author's GST Hodge hypothesis.

The NEW balanced GST rank-adaptive quotient solves this **internal algebraic** compatibility obstacle correctly: it only demands descent of the COMBINED true original \(B=U+J+M+[J,M]\). Its rational quotient has any dimension r (including odd r), while the individual native complex operator J generally does NOT descend through the \(\ell_0\)-kernel. No invalid 1-dimensional rational complex structure is required.

For the universal original-X step, any attempt to use the balanced rank-r quotient must provide a geometric original-X Chow F and a canonical Betti action on \(W_p(X)\) with exactly the **combined F** compatibility, not claim that U,J,M automatically become compatible individual endomorphisms of all Hodge fibers of arbitrary rank. If actual geometric original-X J happens to be defined on a larger even-dimensional cohomology carrier, a Hodge subquotient need not retain J itself.

This removes a conceptual compatibility trap in the user's arbitrary-dimensional/cardinality program but does NOT construct algebraic cycles for previously unknown rational Hodge classes.
