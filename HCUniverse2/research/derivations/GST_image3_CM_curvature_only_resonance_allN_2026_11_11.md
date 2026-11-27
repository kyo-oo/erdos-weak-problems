# GST Image-3 continuation — CM curvature-only source birth, exact resonance, all-N cyclicity and original-X compiler

**Date:** 2026-11-11 (India), independent branch \`research/gpt6-image3-curvature-only-resonance-20261111\`.

## Exact research target, owner-original laws only

The author's actual universal Hodge antecedent requires, for EVERY original smooth projective complex X and codimension p, a true algebraic correspondence on X×X with canonical cycle-class naturality and a full rank orbit on the genuine rational Hodge space W_p(X). The existing Lean conditional \`exactHodge_of_one_GST_fold_orbit\` proves that this antecedent implies Hodge algebraicity. The current experiment does NOT assert this universal antecedent.

This route combines the author's ORIGINAL and source-verified \`GSTGraphV2CMWaveFusion.U\` (five-order information shuffle), \`J\` (rational complex mirror J²=-I), \`M\` (genuine Wave-I SURVIVE multiplication), mixed \`seed\`, N-cohomology independent channels, and the true original-x cycle operator pairs used by \`GSTGraphV2NativeCurvatureBirth\`.

The prior direct source fold \(T=U+J+M\) was cyclic (native rank12, determinant -1149656584000), but nonzero CM curvature alone had only been used as a DETECTOR. The new test asks whether the true ORIGINAL CM curvature \(C=[J,M]\) can replace the direct M source in the fold, and, if so, which strengths fail.

## 1. NEW exact curvature-only source theorem (no direct M)

Let \(V=\mathbb Q^{12}\) indexed by the owner's original \((carry,trit)\in\mathrm{Fin}(4)\times\mathrm{Fin}(3)\). Define the ACTUAL original operators:
\[
U(u)(s)=u(\mathrm{shuffle}(s)),\qquad
J(u)(s)=\mathrm{cmSign}(s)\,u(\mathrm{mirrorCell}(s)),
\qquad M(u)(s)=\mathrm{sourceMultiplicity}(s)\,u(s).
\]
The true rational source is \(v=e_{(0,0)}+e_{(0,1)}\).

Define the original CM source \(C=[J,M]=JM-MJ\) and *NEW native two-parameter F*:
\[
F_{a,b}=U+J+aM+bC.
\]

**Theorem A (exact arithmetic certificate):** Even with the DIRECT SURVIVE contribution turned OFF (\(a=0\)), the genuine ORIGINAL CM curvature restores the whole wave orbit:
\[
\boxed{\operatorname{rank}_\mathbb Q[v,F_{0,1}v,\ldots,F_{0,1}^{11}v]=12,\quad
\det[v,F_{0,1}v,\ldots,F_{0,1}^{11}v]=1\,386\,205\,893\ne0.}
\]
This was evaluated with exact rational arithmetic, rebuilding EVERY matrix entry independently from the original \`shuffle\`, \`mirrorCell\`, \`cmSign\` and the real \`sourceMultiplicity\`; no fabricated source matrix or imposed full-rank basis was used.

**Theorem B (native complex structure and curvature parity):**
\[
J^2=-I,\quad JU=UJ,\quad C=[J,M],\quad
\boxed{JC+CJ=0},\quad \operatorname{rank}_\mathbb Q(C)=6.
\]
Proof, *valid for every operator ring where J²=-I*:
\[
JC+CJ=J(JM-MJ)+(JM-MJ)J=J^2M-MJ^2=-M+M=0.
\]
The new source \(C\) reverses the owner's actual CM phase, rather than representing a mere re-coordination. Even though \(C\) has rank6, combination with the original U+J generates the entire rank12 native orbit.

## 2. NEW exact resonance no-go theorem: strength b=1/2 blocks source birth for ALL a

Let \(u_0=u((0,0))\), \(u_{\max}=u((3,2))\), the author's original two U-fixed mirror-paired information cells. The ORIGINAL source values are \(M_{00}=0\), \(M_{max,max}=2\). The J mirror has \(J(u)_{\max}=-u_0\), and \(U(u)_{\max}=u_{\max}\).

The curvature \(C=[J,M]\) contributes \(C(u)_{\max}=2u_0\). Therefore, FOR EVERY \(a,b\in\mathbb Q\), EVERY signal u:
\[
\boxed{(F_{a,b}u)_{\max}=(1+2a)u_{\max}+(2b-1)u_0.}
\]
At \(b=1/2\), the new curvature source cancels the original J null-to-maximum navigation link EXACTLY. The original seed \(v\) has \(v_{\max}=0\), and induction gives
\[
\boxed{\forall a\in\mathbb Q,\;\forall n\ge0,\quad
(F_{a,1/2}^{\,n}v)_{\max}=0.}
\]
Thus its orbit lies in the fixed proper rational hyperplane \(\{u:u_{\max}=0\}\) and can NEVER be cyclic in the original 12-state GST wave, regardless of how the direct source coefficient a is chosen.

This is a rigorous universal-in-a (not merely sampled) obstruction, anchored in a single original GST cell and exact row identity. It is formalized in NEW \`GSTImageThreeCurvatureResonance.lean\`: \`curvatureFold_maximum\`, \`resonance_half_maximum\`, \`resonance_half_orbit_maximum_zero\`, \`resonance_half_ne_maximum_basis\`.

The exact symbolic determinant independently has factor \((-1+2b)\) when a=0. At b=1/2, seven tested a-values \(-2,-1,0,1/2,1,2,4\) all had rank11, but the rigorous proof only asserts noncyclic rank at most11 for every rational a; the stronger claim of exactly rank11 for all a would require an independent all-a minor analysis.

**Correct mathematical interpretation:** nonzero CM curvature ≠ automatic full rank. The geometry of its *navigation path couplings* matters; at b=1/2 the curvature cancels an indispensable route.

## 3. NEW all-finite-N positive source-birth theorem for curvature alone

Let \(h\ge1\) and take the user's ORIGINAL independent finite N-cohomology wave worlds indexed \(0\le i<h\), with their existing channel-address offsets \(10i\). Define
\[
T_h=\bigoplus_{i=0}^{h-1}
\bigl(U+J+[J,M]+10i\,I_{12}\bigr),\qquad
w_h=(v,\ldots,v)\in\mathbb Q^{12h}.
\]
**Theorem C:**
\[
\boxed{\operatorname{rank}_\mathbb Q
[w_h,T_hw_h,\ldots,T_h^{12h-1}w_h]=12h
\quad\text{for every finite }h\ge1.}
\]

Proof: Theorem A says the original mixed v is cyclic for the actual original curvature-only block \(T_0=U+J+[J,M]\). The exact maximum ABSOLUTE row-sum norm of \(T_0\) is 4 (confirmed independently in Mathematica). Therefore all its complex eigenvalues \(\zeta\) obey \(|\zeta|\le4\). Shifted block \(T_0+10i I\) has all eigenvalues in the disk centered at \(10i\) of radius4, so its spectrum is disjoint from every other block (center distance at least10>8). Consequently their rational characteristic/minimal polynomials are pairwise coprime. Each block is cyclic for the SAME actual seed v, so the polynomial CRT produces, from one global seed \(w_h\), any selected combination of the h independent block seed-orbits. Therefore its generated rational module equals \(\bigoplus_i \mathbb Q^{12}\), dimension 12h. This is a mathematical proof for all finite h, not just a finite computational sweep.

**Theorem D (native moment determinant exactly +1, all finite h):** Let \(n=12h\), \(K_h=[w_h,T_hw_h,\ldots,T_h^{n-1}w_h]\), invertible by Theorem C. Define the rational functional \(\ell_h=e_{n-1}^{T}K_h^{-1}\). Then
\(\ell_h(T_h^k w_h)=0\) for k<n-1 and \(=1\) for k=n-1.
The moment matrix \(H_h=[\ell_h(T_h^{i+j} w_h)]_{0\le i,j<n}\) is anti-triangular, with all anti-diagonal entries1 and zero entries on one side; hence
\[
\det H_h=(-1)^{n(n-1)/2}=+1
\]
because n=12h is divisible by4. Therefore the genuine ORIGINAL GST native information moment determinant is +1, for EVERY positive finite N-hole count. This proves the owner's requested native finite-N analogues of steps 02 and 03 for the curvature-only choice, but is NOT yet a Hodge-class moment determinant on arbitrary X.

Exact 24-state h=2 rank24 and nonzero full Krylov determinant were independently checked using the original source in Wolfram.

## 4. Original-X canonical Chow–Betti landing

The NEW \`GSTImageThreeOriginalXCurvatureLanding.lean\` uses the owner's EXACT existing certified actual original-X \`CycleClassOperatorPair\` structure, with NO invented cycle preimages, and constructs
\[
N_C=N_JN_M-N_MN_J,\quad
T_C=T_JT_M-T_MT_J,
\]
and
\[
N_F=N_U+N_J+aN_M+bN_C,\qquad
T_F=T_U+T_J+aT_M+bT_C.
\]
Given three actual original-X certified operator pairs, the canonical original-X cycle class satisfies
\[
\boxed{\mathrm{cl}_X\circ N_C=T_C\circ\mathrm{cl}_X,\qquad
\mathrm{cl}_X\circ N_F=T_F\circ\mathrm{cl}_X.}
\]
For curvature-only (\(a=0,b=1\)), the actual original-X cycle \(N_F(Z)\) is a genuine rational algebraic native source when the operators are actual. This is a NONCIRCULAR construction in native cycles.

But this is still a **geometric compiler conditional on genuine X-specific U/J/M inputs**. It does NOT assert their existence on every X, an equivariant full-rank map from the owner's 12h wave carrier onto each actual rational Hodge space \(W_p(X)\), or arbitrary unknown Hodge classes already having cycle preimages. Therefore do not promote Theorem C to Hodge conjecture without proving this last truly geometric antecedent.

## 5. What is proved out of the author's four actual GST→Hodge steps?

| User's original step | Established in native GST | Established universally on original X? |
|---|---|---|
| 01 Real Chow correspondence with cl∘N=T∘cl | Real original-X operator-combination/compiler verified as conditional on actual U,J,M operators | NO: universal existence of compatible original-X operators & faithful landing not supplied |
| 02 Orbit reaches every independent Hodge direction | YES for owner's exact native wave, all positive finite N via curvature-only F | NO: native 12N not universal \(W_p(X)\) |
| 03 Rational moment det nonzero | YES: +1 all native finite N from explicit inverse-Krylov detector | NO: actual geometric Hodge moment determinant not established |
| 04 Every smooth projective X, p, canonical Hodge map | Lean conditional implication X_GST⇒Hodge already proved in repo | NO: true universal X_GST antecedent is outstanding |

Hence 0/4 UNIVERSALLY established, with substantial provable native algebra and conditional geometric compiler through steps1-3. The correct next route is to construct true geometric operators on the original X whose canonical Hodge representation contains the curvature-only GST cyclic module nondegenerately, not to repeat an existing finite source determinant. Any quotient or representation selected using missing target Hodge cycle preimages is circular.

## 6. Reproducibility

New committed Wolfram:
\`research/computations/GST_image3_curvature_only_source_and_resonance_20261111.wl\`.
It was fetched BACK from exact GitHub branch and evaluated verbatim, and returned \`allPassed=True\`, with original identities \(J^2=-I,U^5=I,JC+CJ=0,\mathrm{rank}C=6\), curvature-only native Krylov rank12 and determinant1,386,205,893, row norm4, 24-state rank24, and max-cell null coupling \(-1+2b\).

New Lean modules:
- \`GSTImageThreeCurvatureResonance.lean\`, CI \`.github/workflows/gst-image3-curvature-resonance.yml\`;
- \`GSTImageThreeOriginalXCurvatureLanding.lean\`, CI \`.github/workflows/gst-image3-curvature-originalx.yml\`.

Do not mark Lean theorems kernel-green until those workflows report SUCCESS; the underlying Wolfram exact matrix identity and mathematical all-h CRT proof are independently recorded.


## 7. NEW exact UNIVERSAL-RATIONAL native curvature-strength theorem

The earlier section only verified curvature strength b=1, while the symbolic determinant calculated for the exact ORIGINAL U/J/M matrices can be factored FOR ALL symbolic rational strengths b:
\[
\boxed{
\det [v,(U+J+bC)v,\ldots,(U+J+bC)^{11}v]
=b^4(2b-1) P_{10}(b) P_{16}(b).
}
\]
Here \(C=[J,M]\), and the two exact integer polynomials are
\[
\begin{split}
P_{10}(b)={}&411701-2185728b^2+293888b^3+3073344b^4
 -960384b^5-1658656b^6\\
&+835776b^7+244932b^8-222264b^9+36900b^{10},\\
P_{16}(b)={}&255140-1606056b^2+3096493b^4
 -2099096b^6+1818992b^8\\
&-3016960b^{10}+2444032b^{12}-1234944b^{14}
 +331776b^{16}.
\end{split}
\]

### Complete finite-field certificate that BOTH polynomials have NO rational roots

Modulo the prime7, their leading coefficients reduce to
\[
36900\equiv3\pmod7,\qquad331776\equiv4\pmod7,
\]
both invertible in \(\mathbb F_7\).

The EXACT exhaustive evaluations of all seven residues b=0,1,...,6 are
\[
(P_{10}(b)\bmod7)_{b=0}^6=(3,3,5,6,4,1,5)
\]
and
\[
(P_{16}(b)\bmod7)_{b=0}^6=(4,3,3,4,4,3,3).
\]
Every value is nonzero. Therefore neither polynomial has any zero in \(\mathbb F_7\). By the rational-root theorem, a rational root a/d in lowest terms would have denominator d dividing the leading coefficient; hence 7 does not divide d, and reducing the polynomial equation modulo7 would produce a forbidden finite-field root. Thus NEITHER polynomial has a rational root.

The determinant vanishes over \(\mathbb Q\) if and only if \(b=0\) or \(b=1/2\). Therefore:
\[
\boxed{
\forall b\in\mathbb Q\setminus\{0,\tfrac12\},\quad
\operatorname{rank}_{\mathbb Q}
[v,F_{0,b}v,\ldots,F_{0,b}^{11}v]=12.}
\]

This is a genuine ALL-RATIONAL-strength source-birth theorem for the owner's exact original GST operator algebra, not a finite-parameter conjecture. Its exceptional strengths have original-source geometric explanations: b=0 gives the original rank10 U+J orbit; b=1/2 closes the null-to-maximum information navigation channel, independently of direct M strength a.

The proof's full determinant factor was computed EXACTLY in the original-waves source Wolfram script \`research/computations/GST_image3_curvature_only_source_and_resonance_20261111.wl\` and is rederived in §1; the independent short complete residue certificate was committed to \`research/computations/GST_image3_CM_curvature_all_rational_strength_mod7_20261111.wl\`, fetched back from GitHub, executed with Wolfram and returned allPassed=True.

### Consequence for all original finite N-hole Wave-II worlds

For every \(\beta\in\mathbb Q\setminus\{0,\tfrac12\}\) and every original finite number \(h\ge1\) of N-cohomology holes, define \(T_\beta=U+J+\beta C\). Each block is cyclic by the theorem above. The rational row sum satisfies the elementary bound \(\|T_\beta\|_\infty\le2+2|\beta|\). If \(|\beta|\le1\), the ORIGINAL historical Wave-II spacing 10 yields disjoint spectral disks (radius≤4, center spacing10). Hence the exact all-h CRT argument gives rank12h and the normalized moment determinant +1 on the native information space for every rational
\[
-1\le\beta\le1,\qquad \beta\ne0,\quad\beta\ne\tfrac12.
\]
For arbitrary rational |\beta|>1, choosing a *larger rational channel navigation offset* \(L_\beta>4+4|\beta|\) similarly proves full original-native cyclicity. The operator remains the author's original U/J/M commutator; only the independent Wave-II information readout scale changes.

**Nothing here assumes algebraicity of unknown Hodge classes on an arbitrary original projective X.** This strengthens only the original-wave rank and moment subprogram; the genuine universal original-X construction remains the separate GST Hodge antecedent.
