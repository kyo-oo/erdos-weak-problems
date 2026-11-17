# Mathbox — Actual diagonal-graph perfect-complex births beyond GST Catalan Koszul sources

**Date:** 2026-10-19. **Program:** original all-varieties rational Hodge theorem, fixed acceptance unchanged. **Branch base:** 6cad83c857237713000b05df8a44a1c1bbdbefbb, research/gpt6-native-point-primitive-span-20261017. **Route:** replace coordinate-only elliptic Koszul words by a larger REAL native source type: the elliptic diagonal graph, then take arbitrary external GST world births. **Result:** uniform all-rank algebraic primitive source frame of size 2^m on genuine original self-products E^(2m); a verified new geometric regime not spanned by coordinate divisor products. This is **not** the theorem for every arbitrary smooth projective X or every rational Hodge target.

## 1. Two native Hodge-primitive divisors on the SAME original E×E

Let E/C be any elliptic curve with basepoint o. On S=E×E put
\[
x_1=[\{o\}\times E],\qquad x_2=[E\times\{o\}],\qquad
\delta=[\Delta_E]\in CH^1(S)_{\mathbb Q}.
\]
These are actual algebraic Cartier divisors. Their Chow intersection products satisfy
\[
x_1^2=x_2^2=\delta^2=0,\qquad
x_1x_2=x_1\delta=x_2\delta=[(o,o)].
\]
The identity delta²=0 is the triviality of the diagonal normal bundle \(N_{\Delta/S}\cong T_E\), not merely an equality of cohomological degrees. For the true ample \(h=x_1+x_2\), define
\[
P=x_1-x_2,\qquad D=\delta-x_1-x_2.
\]
Then **in Chow** \(hP=hD=0\), and their intersection products are
\[
P^2=D^2=-2[(o,o)],\qquad PD=0.
\]
The signed Hodge–Riemann pairing on the primitive \((1,1)\)-subspace is \(Q_S(u,v)=-\int_S uv\), hence the actual \(2\times2\) native geometric Gram is \(\mathrm{diag}(2,2)\). In particular, \(D\) is a genuine independently constructed nonzero primitive divisor direction orthogonal to the coordinate Koszul source P.

## 2. PERFECT COMPLEX, not a selected Hodge witness

Let \(L_1=\mathrm{pr}_1^*\mathcal O_E(o), L_2=\mathrm{pr}_2^*\mathcal O_E(o)\), and \(M=\mathcal O_{E\times E}(\Delta_E-x_1-x_2)\). These are **actual algebraic line bundles**, requiring NO prescribed Hodge class alpha as input.

The actual algebraic rational K₀ classes are
\[
A=[L_1]-[L_2],\qquad
B=\frac12([M]-[M^{-1}]).
\]
Since \(x_1^2=x_2^2=0\) and S has dimension two,
\[
\operatorname{ch}(A)=e^{x_1}-e^{x_2}=P,\qquad
\operatorname{ch}(B)=\tfrac12(e^D-e^{-D})=D.
\]
**Both have PURE rational Chern character in codimension one.** The antisymmetric inverse line-bundle operation in B is crucial; simply using \([M]-[\mathcal O]\) would have a nonzero codimension-two Chern term \(D^2/2=-[(o,o)]\) and spoil the exact pure-degree GST source birth.

## 3. The all-rank diagonal-graph GST tensor world birth

For each m≥1, the **ORIGINAL** smooth projective abelian \(2m\)-fold \(X=E^{2m}=\prod_{j=1}^m S_j\) has genuine ample \(H=\sum_j(x_{2j-1}+x_{2j})\). For each word \(\epsilon\in\{P,D\}^m\) form
\[
\mathcal E_\epsilon=\boxtimes_{j=1}^m
\begin{cases}
A_j,&\epsilon_j=P,\\
B_j,&\epsilon_j=D,
\end{cases}
\qquad
Z_\epsilon=\operatorname{ch}_m(\mathcal E_\epsilon)
=\prod_{j=1}^m\epsilon_j\in CH^m(X)_{\mathbb Q}.
\]
Every tensor component has ch ONLY in degree one. Thus the entire product ch is PURELY degree m, with no Chern/Todd leakage; \(T_X\) is trivial. Actual Chow product identities give
\[
H Z_\epsilon=0\in CH^{m+1}(X)_{\mathbb Q}.
\]
For the signed Hodge-Riemann polarization \(Q_X(u,v)=(-1)^m\int_X uv\), Künneth/projective intersection factorization yields the EXACT Gram
\[
\boxed{
Q_X(Z_\epsilon,Z_\eta)=
\prod_{j=1}^m 2\,\mathbf1_{\epsilon_j=\eta_j}
=2^m\mathbf1_{\epsilon=\eta}.
}
\]
Therefore **2^m independently algebraic rational primitive classes** are born for each m, with no assumed native primitive Hodge witness, nonzero determinant, or target preimage. Their indexed Gram matrix is \(2^m I_{2^m}\), determinant \((2^m)^{2^m}>0\). GSTPrimitiveProductTowerStabilization.lean was edited *in place* with the honest E×E intersection dictionary and Boolean-labeled product Gram laws. That formalization is the exact rational cup/intersection algebra core; the actual Chow/GRR/Künneth instantiation is a separate scheme-level semantics requirement.

The true finite-flat normalized GST algebraic K₀ projector FIXES each source: after replacing H by sufficiently ample kH to define a genuine finite projective map \(f:X\to\mathbb P^{2m}\), its pure ch_m has \(f_*\operatorname{ch}_m(\mathcal E_\epsilon)=0\), because \(H^m Z_\epsilon=0\). On an abelian variety \(\mathrm{Td}(T_X)=1\); GRR and injectivity of projective rational ch therefore give \(f_*\mathcal E_\epsilon=0\in K_0(\mathbb P^{2m})_{\mathbb Q}\), so \(\mathcal P_f^K(\mathcal E_\epsilon)=\mathcal E_\epsilon\). These are ACTUAL original-X algebraic K₀/Chow sources, not projections of already-specified Hodge target cycles.

## 4. Independent of the previously COMPLETE squarefree divisor-word GST frame

The existing arbitrary-rank GST Catalan theorem in [Koszul record](2026-10-19-gst-koszul-primitive-all-even-elliptic-product.md) constructs \(C_m\) independent native primitive source classes from **coordinate-only** divisor words \(x_i\).

The new \(D_j=\delta_j-x_{2j-1}-x_{2j}\) lies purely in
\(H^1(E_{2j-1})\otimes H^1(E_{2j})\) under Künneth: subtracting x₁+x₂ removes the outer \(H^0\otimes H^2\) and \(H^2\otimes H^0\) components of the diagonal. Hence ANY product word containing at least one D_j is orthogonal (under top-degree intersection) to EVERY coordinate-only squarefree divisor-word source; at that pair, a cohomological pure coordinate monomial has bidegree (0 or 2,0 or 2) and cannot pair with (1,1) to top (2,2). (At the Chow level, vanishing of some individual mixed cycles would require an additional rational-equivalence analysis; Betti orthogonality is sufficient for native class independence.)

There are 2^m−1 graph-containing words, all mutually orthogonal and of nonzero norm. Their span intersects the Catalan squarefree primitive span trivially by positivity. Therefore the **real source birth raises the independent primitive algebraic rank** from \(C_m\) to at least
\[
\boxed{C_m+2^m-1}
\]
on every original E^(2m), without double-counting the one pure pair-Koszul word already in Catalan.

**Explicit m=2 audit (X=E^4).** The Catalan sources \(P=(x_1-x_2)(x_3-x_4)\) and \(Q=(x_1-x_3)(x_2-x_4)\) have Gram \(\begin{psmallmatrix}4&2\\2&4\end{psmallmatrix}\). The new source classes are
\[
D_{12}P_{34},\qquad P_{12}D_{34},\qquad D_{12}D_{34}.
\]
Their signed Gram is \(4I_3\), all cross pairings against P,Q vanish, and thus
\[
G_{5}=\operatorname{diag}\bigl(
\begin{psmallmatrix}4&2\\2&4\end{psmallmatrix},4,4,4\bigr),
\qquad \det G_5=12\cdot 4^3=\boxed{768}.
\]
Wolfram EXACT arithmetic verified both the elliptic-pair intersection table and this determinant. The added sources detect Künneth \(H^1\)-graph primitive directions unavailable to any pure squarefree coordinate-divisor polynomial.

## 5. GST target-directed actual native perfect complex in this genuinely enlarged frame

For an arbitrary rational primitive Hodge class \(\alpha\) on the ORIGINAL X, define exact periods \(a_\epsilon=Q_X(\alpha,Z_\epsilon)\). The ACTUAL rational algebraic perfect-complex source
\[
\boxed{\mathcal E_\alpha^{\rm graph}
=\frac1{2^m}\sum_{\epsilon\in\{P,D\}^m} a_\epsilon\,\mathcal E_\epsilon}
\]
has honest algebraic rational CHOW class
\[
Z_\alpha^{\rm graph}=\frac1{2^m}\sum_\epsilon a_\epsilon Z_\epsilon,
\]
whose pairings satisfy
\[
Q_X(Z_\alpha^{\rm graph},Z_\eta)=a_\eta,\qquad
Q_X(\alpha,Z_\alpha^{\rm graph})
=\frac1{2^m}\sum_\epsilon a_\epsilon^2\ge0.
\]
It has a strictly positive target coupling when alpha is detected by at least one new graph source. Combined with the existing Catalan native period compiler, the graph-containing words can be added **orthogonally** to the old frame, giving a target-selected native source for the entire direct sum sector of dimension \(C_m+2^m-1\). This is a concrete multi-sector GST source birth and not a false claim that this span equals the full rational Hodge fiber for arbitrary X.

## 6. Evidence, audit, and exact next mathematical move

- **Math proof:** all algebraic surface intersection identities, pure-ch rational K₀ computation, arbitrary-m external product Chow primitivity and signed product Gram factorization, and enlarged algebraic rank lower bound as above.
- **Wolfram:** exact elliptic pair \(\{hP,hD,P^2,PD,D^2,Q(D,x_1),Q(D,x_2)\}=\{0,0,-2,0,-2,0,0\}\), and exact m=2 enlarged Gram determinant 768.
- **Lean:** in-place changes in GSTPrimitiveProductTowerStabilization.lean at commit 2a3b31487622288ee0d66fa48c161f1b6ae05a07. Kernel receipt MUST be read after focused CI #39168025378 finishes. The Lean ring model is NOT itself a scheme-level algebraic K₀ object or a canonical Hodge-cycle class; keep those instantiation gates separate.
- **Geometric scope:** self-products E^(2m) of smooth complex elliptic curves (all E, including CM and non-CM); no all-varieties primitive representative is claimed here.
- **Next geometric attack:** exploit diagonal-graph perfect complexes and GST projective normalization on *arbitrary abelian varieties* via Poincaré sheaves and genuine homological Fourier–Mukai transforms, or construct a nontrivial target-sensitive original-X correspondence slice using actual derived algebraic kernels on general X. For any final all-X claim, the missing requirement is to make the resulting algebraic K₀ Chern-image sources span the actual rational (p,p) fiber, and to authenticate canonical Betti semantics. A real source rank upgrade for an infinite new family is an intermediate result, not a replacement of this fixed objective.
