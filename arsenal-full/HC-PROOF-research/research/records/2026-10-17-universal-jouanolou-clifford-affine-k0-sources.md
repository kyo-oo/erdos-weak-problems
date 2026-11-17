# Mathbox Gate 3 — explicit algebraic projectors on universal affine replacements

- **Date / checkpoint:** 2026-10-17. Research branch \`research/gpt6-native-point-primitive-span-20261017\`; base checkpoint \`e82048f9a1d3a06500595a232717dd78973df179\`.
- **Fixed final target:** For all smooth projective complex varieties \(X\), codimensions \(p\), and rational \((p,p)\) Hodge classes \(\alpha\), construct a native rational algebraic codimension-\(p\) cycle on **original \(X\)** with its canonical Betti class \(\alpha\).
- **Work-package target:** Construct genuine ALGEBRAIC vector-bundle sources from explicit equations on smooth affine models without presupposing any K-theory lift of \(\alpha\), and test their relation to a canonical affine replacement of arbitrary \(X\).

## 1. Universal, genuinely affine carrier for every original X

Fix a closed embedding \(X\hookrightarrow\mathbb P^N_{\mathbb C}\). Let \((\mathbb P^N)^\vee\) be the dual projective space and define
\[
 J(X)=\{(x,H)\in X\times(\mathbb P^N)^\vee:x\notin H\}.
\]
The excluded incidence locus is the zero divisor of \(\mathcal O_X(1)\boxtimes\mathcal O(1)\), an **ample** line bundle on the projective product. Thus its complement \(J(X)\) is **affine**. Over a chart \(x_i\neq0\), normalized equations \(\sum_j\lambda_jx_j=1\) solve uniquely for \(\lambda_i\) and leave \(N\) free affine parameters. Consequently \(\pi:J(X)\to X\) is a Zariski-locally trivial \(\mathbb A^N\)-bundle (Jouanolou affine replacement) for **every** smooth projective \(X\). It is smooth.

By affine-bundle homotopy invariance,
\[
  \pi^*:H^{2p}(X,\mathbb Q)\simeq H^{2p}(J(X),\mathbb Q),\qquad
  \pi^*:CH^p(X)_{\mathbb Q}\simeq CH^p(J(X))_{\mathbb Q}.
\]
These maps respect canonical Betti classes; rational algebraic \(K_0\) is likewise invariant on smooth regular schemes. Because the Betti map is a geometric isomorphism, the affine target \(\pi^*\alpha\) has pure Hodge type \((p,p)\) for every original \(X,p,\alpha\). **An algebraic affine cycle on \(J(X)\) can be descended unambiguously to an algebraic cycle on original \(X\)** using the Chow inverse. This is a direct all-\(X\) affine model without the auxiliary divisor-boundary induction.

**Precise remaining generator problem:** produce \(Z_{J(X)}\in CH^p(J(X))_{\mathbb Q}\) with \(\mathrm{cl}_{J(X)}(Z_{J(X)})=\pi^*\alpha\) *without assuming the desired Chow witness*. The affine equivalence above is not an existence proof. It is a rigorous geometry-first environment in which to manufacture the required algebraic K-classes.

## 2. Universal rank-one projector manufactured from the incidence equations

The regular functions on \(J(X)\)
\[
 e_{ij}=\frac{x_i\lambda_j}{\sum_k x_k\lambda_k}
\]
are globally well-defined: each is homogeneous degree zero separately in the two projective factors and the denominator never vanishes on \(J(X)\). The matrix \(E=(e_{ij})\) satisfies
\[
   \mathrm{tr}\,E=1,\qquad e_{ik}e_{kj}=e_{ij}e_{kk},
   \qquad E^2=E.
\]
The \(\operatorname{im}(E)\) over the AFFINE coordinate ring is therefore a **genuine algebraic projective module**, precisely the pullback of the tautological algebraic line \(\mathcal O_X(-1)\). It exists on **every** original \(X\), without Oka or a chosen K-theory preimage.

The current rank-one source produces the ambient hyperplane Chern classes. It does not supply arbitrary primitive Hodge directions, so it must be extended with explicit **higher-rank primitive projectors**, not mistaken for complete Hodge spanning.

## 3. Clifford recursion manufactures algebraic K-classes at every p

For each integer \(p\ge1\), over the polynomial ring \(\mathbb Z[x_1,\ldots,x_p,y_1,\ldots,y_p,z]\) put \(q_p=\sum_i x_i y_i\). Define \(A_1=(x_1)\), \(B_1=(y_1)\) and recursively with \(I\) of size \(2^{p-1}\):
\[
 A_{p+1}=\begin{pmatrix}A_p&x_{p+1}I\\y_{p+1}I&-B_p\end{pmatrix},\qquad
 B_{p+1}=\begin{pmatrix}B_p&x_{p+1}I\\y_{p+1}I&-A_p\end{pmatrix}.
\]
Direct block multiplication and commutativity show \(A_pB_p=B_pA_p=q_p I\) **for every p by induction**. Set
\[
 E_p=\begin{pmatrix}zI&A_p\\B_p&(1-z)I\end{pmatrix},
 \quad \text{size }2^p\times2^p .
\]
One direct block multiplication gives the **polynomial identity**
\[
 \boxed{E_p^2-E_p=(q_p-z(1-z))I_{2^p},\quad
  \operatorname{tr}E_p=2^{p-1}.}
\]
On the smooth affine split quadric
\[
 Q_{2p}=\operatorname{Spec}\,
 \mathbb C[x_1,\ldots,x_p,y_1,\ldots,y_p,z]/(q_p-z(1-z)),
\]
\(E_p^2=E_p\). Hence \(P_p=\operatorname{im}E_p\) is a **genuine algebraic projective module of rank \(2^{p-1}\)** on an affine variety of complex dimension \(2p\). Under any genuine algebraic map \(U\to Q_{2p}\), pulling back \(E_p\) constructs an algebraic projective module on that particular affine \(U\). This is an explicit source factory available in EVERY codimension \(p\); its pullback is defined by polynomial equations on \(U\), not by a topological/Hodge preimage assumption.

A second explicitly manufactured **native codimension-p algebraic cycle** on \(Q_{2p}\) is
\[
 L_p=\{z=y_1=\cdots=y_p=0\}\cong\mathbb A^p,
\]
with codimension \(p\). Its Betti class is nonzero: the compact real sphere inside \(Q_{2p}(\mathbb C)\) defined by \(y_i=\overline{x_i}\), \(z\in\mathbb R\), \(\sum|x_i|^2=z(1-z)\) is an \(S^{2p}\). It intersects \(L_p\) transversely at the single south pole \(x=y=z=0\), with local intersection number \(\pm1\); thus \(\mathrm{cl}(L_p)\) evaluates nontrivially against that sphere. Therefore this is a genuine nonzero rational algebraic class in middle degree **for every p**, without assuming its cycle preimage.

For \(p=1\), \(E_1=\begin{pmatrix}z&x\\y&1-z\end{pmatrix}\). Its image line has a polynomial global section whose zero divisor is \(L_1=\{z=y=0\}\). For the universal affine replacement of \(X=\mathbb P^1\), the identification \(J(\mathbb P^1)\simeq Q_2\) sends the universal rank-one incidence projector to this explicit matrix (up to change of coordinates). Hence the Clifford source starts in the ACTUAL universal affine replacement construction rather than an unrelated toy model.

## 4. Exact independent verification and Lean connection

- Wolfram evaluated the polynomial matrix equations for \(p=1,2,3,4\), obtaining matrices of sizes \(2,4,8,16\), \(A_pB_p=B_pA_p=q_pI\), \(E_p^2-E_p=(q_p-z(1-z))I\) and traces \(1,2,4,8\). This is **exact symbolic arithmetic**, not floating point, and the all-\(p\) proof is the separate block induction above.
- The independent pure-stdlib polynomial audit \`research/computations/affine_clifford_k0_source.py\` checks every polynomial coefficient without external CAS dependencies. In GitHub Actions [#39049136728](https://github.com/kyo-oo/HC-PROOF/actions/runs/39049136728), the polynomial audit PASSED for \(p=1,\ldots,4\); that first combined run FAILED later in a Lean tactic, not in the polynomial construction. The ring-generic Lean rank-one theorem \`quadricBottProjector_idempotent\` is being repaired/verified in \`GSTUniversalResolvedSupportHodge.lean\` with the existing 247-module workflow. Do not equate a failed Lean tactic with a false polynomial identity.
- Full geometric K-theory/Chern-class and affine-bundle/analytic realization for the current GST Stage2G interfaces is still a **separate formalization task**, although the classical algebraic constructions above are explicit and independent of the conjecture.

## 5. Direct next operation on all X,p,alpha

For each original embedded \(X\) and prescribed \(\alpha\), work **on the actual affine ring** \(A=\Gamma(J(X),\mathcal O)\). The concrete candidate space consists of polynomial idempotent matrices \(E\in M_N(A)\), certified by \(E^2=E\), whose algebraic Chern character \(ch_p(\operatorname{im}E)\) equals \(\pi^*\alpha\) under the canonical rational Betti comparison. The incidence projector is a certified ambient generator; the Clifford family supplies explicit additional source matrices when \(A\) contains polynomial quadric data.

**First unresolved mathematical implication:** construct enough genuinely **new algebraic idempotents over \(A\)** (or independently geometric Chow cycles) to hit each prescribed primitive Hodge \(\pi^*\alpha\), not merely ambient Chern classes or a subspace generated by existing cycles. This is the single Gate-3 source-production target, and its truth would imply the original rational Hodge conjecture. No conjectural full-rank hypothesis was added to any proof.

**Route status:** constructive all-\(X\) affine carrier and universal explicit K₀ source factories obtained, with exact algebraic identities; spanning of arbitrary primitive rational Hodge targets open. Natural next attack: build Jacobian-derived higher-rank projectors over arbitrary \(A\), then test whether their primitive Chern directions supply classes outside the universal rank-one span.

## 6. A decisive original-X obstruction and the higher-rank direction

**Clifford quadric pullbacks alone cannot realize an arbitrary prescribed Hodge class.** The affine quadric \(Q_{2p}\) deformation-retracts to a compact real \(S^{2p}\). Thus \(H^{4p}(Q_{2p},\mathbb Q)=0\), so its middle algebraic generator \(u_p=\operatorname{cl}(L_p)\) has \(u_p^2=0\). For any algebraic \(f:J(X)\to Q_{2p}\) the pulled-back Hodge class \(f^*u_p\) likewise satisfies \((f^*u_p)^2=0\).

On a smooth **cubic fourfold containing an algebraic plane** \(P\), write \(H=h^2\). The exact genuine intersection matrix is
\[
 \langle H,H\rangle=3,\quad\langle H,P\rangle=1,\quad
 \langle P,P\rangle=3,\qquad
 Z=3P-H,\quad Z\cdot H=0,\quad Z^2=24.
\]
The pullback of this *already genuine* primitive class to the affine Jouanolou model is nonzero and retains square \(24\). Therefore it **cannot equal a rational multiple of any single affine-quadric generator pullback**. Stronger: on a cubic fourfold the rational \((2,2)\) intersection form is definite (weak Lefschetz gives \(b_2=1\), Hodge–Riemann gives positivity on the primitive \((2,2)\) sector and \(H^2=3\)). Hence every rational \((2,2)\) class of square zero is zero. Every algebraic map \(J(X)\to Q_4\) pulls the generator to a rational \((2,2)\) class of square zero and **therefore to zero**. A finite sum of such classes remains zero and cannot produce \(Z\). This rules out *Clifford-quadric maps alone* as the universal primitive source mechanism, even though the Clifford idempotents themselves are honest algebraic bundles.

**Second independent audit — smooth affine complete-intersection Jacobian projectors:** For \(U\subset\mathbb A^m\) smooth complete intersection of codimension \(c\), its coordinate Jacobian \(J:A^m\to A^c\) admits an algebraic right inverse \(B\) by the Jacobian criterion and Bézout identity among maximal minors. The polynomial projector \(P=I_m-BJ\) is idempotent with image \(\ker J=T_U\). Yet the split sequence \(0\to T_U\to A^m\to A^c\to0\) gives \(T_U\oplus A^c\simeq A^m\). Thus \([T_U]- (m-c)[A]=0\in\widetilde K_0(U)\); **the Jacobian tangent projector produces no nontrivial positive-degree rational Chern-character class on any such smooth affine complete intersection**. Explicitly on split quadrics, the Jacobian row \(J=(y_1,\ldots,y_p,x_1,\ldots,x_p,2z-1)\) has polynomial right inverse \(B=(2x_1,\ldots,2x_p,2y_1,\ldots,2y_p,2z-1)^T\), since \(JB=4\sum x_i y_i+(2z-1)^2=1\) modulo \(q_p-z(1-z)\). Wolfram confirmed the exact polynomial difference equals \(4(q_p-z(1-z))\). The new generic Lean Jacobian idempotent lemmas formalize the algebraic construction, but this K-theory check prevents it from being misused as a primitive class generator on CI affines.

**Resulting Gate-3 move:** Work directly with nontrivial **higher-rank algebraic projectors over \(A=\Gamma(J(X),\mathcal O)\)** whose Chern classes have nonzero self-intersections and independently measurable primitive components. A universal rank-one projector only supplies the hyperplane line; a projector with globally split factorization through a free rank-\(r\) module is likewise K₀-trivial. A candidate must be genuinely nontrivial in \(\widetilde K_0(A)\), not just idempotent. Use explicit algebraic equations, then calculate the canonical rational \(ch_p\) and compare with the *prescribed* \(\pi^*\alpha\). No conjectural source-spanning statement is treated as proved by these tests.

## 7. Constructive non-spherical source through the equations of X

To escape the square-zero restriction of the affine-quadric generator, use the SAME Clifford block identities as **matrix factorizations of the actual defining equations of projective hypersurfaces**, rather than maps into affine quadrics.

If a hypersurface \(X=\{F=0\}\subset\mathbb P^N\) contains a codimension-\(m\) complete-intersection subvariety cut out by \(l_1,\ldots,l_m\), then the defining polynomial lies in that ideal and can be expressed
\[
    F=\sum_{i=1}^m l_i q_i .
\]
The Clifford matrices from section 3, evaluated at \(x_i=l_i\), \(y_i=q_i\), satisfy
\[
    \boxed{A_mB_m=B_mA_m=F I_{2^{m-1}}.}
\]
This is a genuine polynomial **matrix factorization** of \(F\). Over the hypersurface coordinate ring \(R/(F)\), the 2-periodic complex has square-zero differentials. Its resulting algebraic matrix-factorization/MCM module is manufactured from the actual defining equations rather than a conjectural target cycle. On smooth hypersurfaces, the associated sheaf is locally free wherever the matrix-factorization cokernel is maximal Cohen–Macaulay; its graded projective realization and precise Chern character must be computed separately.

A decisive test is the smooth Fermat cubic fourfold
\[
 X=\{F=\sum_{i=1}^3(y_i^3-x_i^3)=0\}\subset\mathbb P^5.
\]
It contains the genuine plane \(P\) given by \(l_i=y_i-x_i=0\). Put \(q_i=y_i^2+x_iy_i+x_i^2\). Then \(F=\sum l_iq_i\), and the Clifford recursion constructs **explicit 4×4 algebraic matrices \(A_3,B_3\)** with \(A_3B_3=B_3A_3=F I_4\). Wolfram independently checked both matrix identities symbolically, with all polynomial coefficients exact. The existing original-\(X\) plane \(P\) has independent primitive cycle \(3[P]-h^2\), whose square is \(24\): this is the benchmark that the higher-rank matrix-factorization channel must detect, unlike pure affine-quadric pullbacks.

**Next real construction test:** prove the exact algebraic K₀/Chern character of the matrix-factorization sheaf in this benchmark and show that its primitive part hits \(3[P]-h^2\). Then generalize the geometric syzygy source beyond an already supplied plane, ultimately to arbitrary original \(X,p,\alpha\). The matrix identity is **already proved algebraically**; the nonambient K₀/Chern comparison is a new substantive implication and is not silently claimed.
