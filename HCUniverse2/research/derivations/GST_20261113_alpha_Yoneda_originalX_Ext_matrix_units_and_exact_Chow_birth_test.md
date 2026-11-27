# GST prescribed-alpha algebraic Yoneda source, original-X full matrix units, and direct Chow-birth test

**Date:** 13 November 2026. **Base:** d89bb3b4a8f583a94e98232af1dfd9024ebb3cbe.  
**Target (unchanged):** for arbitrary smooth projective complex original \(X\) of dimension \(d\), any \(p\), and prescribed \(\alpha\in H^{2p}(X,\mathbb Q)\cap H^{p,p}(X)\), construct \(Z_\alpha\in CH^p(X)_{\mathbb Q}\) and prove \(\operatorname{cl}_X^{\mathrm{can}}(Z_\alpha)=\alpha\). No algebraic cycle representing the target is a permitted input.

This is an attack on the source-birth arrow. Its positive advance over the earlier topological Thom–Porteous source is an ACTUAL original-\(X\) algebraic coherent-derived morphism chosen by \(\alpha\). The derived matrix-unit engine is constructed, then its most direct attempt to yield a Chow cycle is tested and refuted as a method. The universal target is **not** proved here.

## 1. Universal construction of algebraic extension data FROM alpha

Let \(X\) be smooth projective connected over \(\mathbb C\), \(0\le p\le d\). Projective coherent GAGA and the Hodge–Dolbeault decomposition give

\[
W_p(X)_{\mathbb Q}:=H^{2p}(X,\mathbb Q)\cap H^{p,p}(X,\mathbb C)
\longhookrightarrow H^p(X,\Omega_X^p)
\cong \operatorname{Ext}^p_{\mathcal O_X}(\mathcal O_X,\Omega_X^p)
\cong \operatorname{Hom}_{D^b_{\mathrm{coh}}(X)}
(\mathcal O_X,\Omega_X^p[p]).
\tag{1}
\]

**Theorem A (alpha-first algebraic derived birth).** Every prescribed rational Hodge \(\alpha\) determines an actual algebraic derived arrow
\(e_\alpha:\mathcal O_X\to\Omega_X^p[p]\). It is nonzero iff \(\alpha\ne0\). It admits a Yoneda \(p\)-fold extension presentation through algebraic coherent sheaves. Neither an algebraic target cycle nor an algebraic \(K_0\) preimage is input.

**Proof.** The rational Hodge class belongs to the complex \((p,p)\) summand. Dolbeault gives \(H^p(X^{an},\Omega_{X^{an}}^p)\), and coherent GAGA identifies it with \(H^p(X,\Omega_X^p)\). Since \(\mathcal O_X\) is locally free rank one, \(\operatorname{Ext}^p(\mathcal O_X,\Omega_X^p)\cong H^p(X,\Omega_X^p)\), which is derived Hom. These maps are injective on the displayed rational subspace. Yoneda Ext classes can be represented by coherent extensions. QED.

**Type distinction:** an algebraic Ext class is an algebraic morphism/extension, **not** a Chow cycle. The construction is genuinely on the original \(X\) but cannot be called the universal Hodge proof.

## 2. Exact algebraic Yoneda/Serre detector for nonzero primitive alpha

The algebraic Serre trace for connected \(X\) is
\[
\operatorname{Tr}_X:
\operatorname{Ext}^d_{\mathcal O_X}(\mathcal O_X,\Omega_X^d)
=H^d(X,\Omega_X^d)\overset{\sim}{\longrightarrow}\mathbb C.
\tag{2}
\]

For \(\beta\in H^{d-p}(X,\Omega_X^{d-p})\), wedge and Yoneda yield an ACTUAL algebraic derived morphism
\(b_\beta:\Omega_X^p\to\Omega_X^d[d-p]\).
The composite has trace
\[
\operatorname{Tr}_X(b_\beta\circ e_\alpha)
=\int_X\alpha\smile\beta .
\tag{3}
\]
The equality uses Serre trace/de Rham comparison with the usual Hodge normalization; scalar comparison powers of \(2\pi i\) are fixed once Tate twists are fixed.

**Theorem B (nonzero prescribed-alpha trace).** Suppose \(2p\le d\), \(0\ne\alpha\in W_p(X)_\mathbb Q\) is primitive relative to rational ample \(h\), i.e. \(h^{d-2p+1}\alpha=0\). Set
\[
\beta_\alpha=h^{d-2p}\alpha\in
 H^{d-p}(X,\Omega_X^{d-p}),
\qquad
s_\alpha=\operatorname{Tr}_X(b_{\beta_\alpha}\circ e_\alpha).
\]
Then
\[
\boxed{s_\alpha=\int_X\alpha^2h^{d-2p},\qquad
(-1)^p s_\alpha>0.}
\tag{4}
\]
**Proof.** Pair by Yoneda cup/wedge and Serre trace to obtain the integral. Because the prescribed class is rational Betti, it is real. The primitive \((p,p)\) Hodge–Riemann bilinear relation gives the strict signed inequality. QED.

For every \(x\in\operatorname{Ext}^p(\mathcal O_X,\Omega_X^p)\), the formula
\[
\boxed{\Pi_\alpha(x)=
\frac{\operatorname{Tr}_X(b_{\beta_\alpha}\circ x)}
{s_\alpha}\,e_\alpha}
\tag{5}
\]
therefore defines an ACTUAL algebraic-Ext-data rank-one endomorphism, with \(\Pi_\alpha(e_\alpha)=e_\alpha\) and \(\Pi_\alpha^2=\Pi_\alpha\). It is not an algebraic correspondence on \(X\times X\).

## 3. All-codimension, all-rank actual algebraic Yoneda matrix units

Poincaré duality, rational Hard Lefschetz and Hodge–Riemann imply the pairing
\[
W_p(X)_\mathbb Q\times W_{d-p}(X)_\mathbb Q
\longrightarrow \mathbb Q,\quad
(a,b)\longmapsto\int_X a b
\tag{6}
\]
is nondegenerate. Choose any rational basis \(a_1,\ldots,a_n\) of the first Hodge space and its rational dual \(b_1,\ldots,b_n\) in the complementary Hodge space; \(n\) is the actual dimension and may be zero. Let \(e_i\) and \(v_j\) be their actual Yoneda and wedge/Serre-derived arrows, respectively.

**Theorem C (actual derived Ext matrix algebra).** Define on \(\operatorname{Ext}^p_X(\mathcal O_X,\Omega_X^p)\)
\[
\boxed{
\mathcal E_{ij}(x)=e_i\,\operatorname{Tr}_X(v_j\circ x).
}
\tag{7}
\]
These are actual \(\mathbb C\)-linear operators constructed from algebraic coherent derived morphisms on original \(X\). They restrict to rational-linear endomorphisms on \(W_p(X)_\mathbb Q\), where
\[
\boxed{
\mathcal E_{ij}\mathcal E_{k\ell}=\delta_{jk}\mathcal E_{i\ell},
\qquad
\sum_i\mathcal E_{ii}=\operatorname{id}_{W_p(X)_\mathbb Q}.
}
\tag{8}
\]
**Proof.** Duality is \(\operatorname{Tr}_X(v_j\circ e_k)=\delta_{jk}\), hence \(\mathcal E_{ij}\mathcal E_{k\ell}(x)=
\delta_{jk}e_i\operatorname{Tr}_X(v_\ell\circ x)\). The identity is basis reconstruction. QED.

If \(n\ge2\), the owner's rational CM and survival/source operators can be represented on any two Yoneda coordinates by
\(J=\mathcal E_{21}-\mathcal E_{12}\) and \(M=\mathcal E_{11}\). On their 2-plane:
\[
J^2=-I_2,\quad M^2=M,\quad
[J,M]=\mathcal E_{12}+\mathcal E_{21}\ne0 .
\tag{9}
\]
This realizes the **matrix algebra** of the original wave/CM idea through genuine original-X algebraic coherent extension operations. It does not construct the owner's original 12-cell wave operators or satisfy their physical realization/scheme correspondence naturality automatically.

## 4. EXECUTED first Chow-extraction attempt: exact mapping-cone cancellation

Build the ACTUAL algebraic perfect complex \(C_e=\operatorname{Cone}(e:\mathcal O_X\to\Omega_X^p[p])\).

**Theorem D (all-X K0 invisibility).** For every \(e\) at the required degree,
\[
\boxed{
[C_e]=(-1)^p[\Omega_X^p]-[\mathcal O_X]
\quad\text{in }K_0^{alg}(X),
}
\tag{10}
\]
independent of \(e\). Thus all algebraic Chow Chern characters of \(C_e\), their canonical rational Betti classes, and any constructor factoring only through \(K_0\) cannot distinguish \(e_\alpha\) from \(e_0=0\).

**Proof.** The defining triangle
\(\mathcal O_X\to\Omega_X^p[p]\to C_e\to\mathcal O_X[1]\)
implies \([\Omega_X^p[p]]=[\mathcal O_X]+[C_e]\) in algebraic \(K_0\). Shift by \(p\) multiplies a class by \((-1)^p\). Therefore (10). QED.

**Stronger test for \(p\ge2\).** The canonical \(t\)-structure long exact sequence gives
\[
\mathcal H^{-p}(C_e)=\Omega_X^p,\qquad
\mathcal H^{-1}(C_e)=\mathcal O_X,
\qquad
\mathcal H^j(C_e)=0 \ \ (j\notin\{-p,-1\}).
\tag{11}
\]
These sheaves and their direct Fitting supports do not depend on \(e\), even though the full derived object does. For \(p=1\) the only nonzero cohomology is in degree \(-1\), a coherent extension \(0\to\Omega_X^1\to E_e\to\mathcal O_X\to0\), which may vary but has fixed \(K_0\).

**Scaling falsification.** For nonzero \(\alpha\), the algebraic Yoneda class \(te_\alpha\) varies for \(t\in\mathbb C\), yet
\[
[C_{t e_\alpha}]=[C_0]\quad\text{for every }t.
\tag{12}
\]
An assertion \(\operatorname{ch}_p(C_{te_\alpha})=t\alpha\) is false already at \(t=0,1\). This is a counterexample to this source-birth method, not to the Hodge conjecture.

## 5. What the actual mathematical attempt changes

The owner now has a three-level **typed** construction for any prescribed \(\alpha\):

1. **Smooth/topological original-X source:** prior exact \(p+1\)-world Thom–Porteous and positive-current/Green transport.
2. **Algebraic coherent original-X source (THIS theorem):** the ACTUAL morphism \(e_\alpha\), nonzero Yoneda/Serre detector and exact matrix-unit algebra, without any algebraic target cycle.
3. **Chow original-X source:** still the target, not implied by (1) or (2).

The calculation (10)–(12) rules out ordinary cone Chern characters and Fitting supports of its cohomology sheaves as the missing step. An actual extension-dependent **geometric support jump** or an independently constructed original-X algebraic perfect complex with a newly born \(K_0\) class is required to cross the next arrow. An arbitrary abstract matrix word, a flat family of cones, or a Fourier–Mukai operator built solely from the unchanged \(K_0\) class of these cones cannot do so.

## Independent exact check and source scope

Wolfram tests, using a positive definite rational Gram form and a nonorthogonal rational basis, verified the matrix-unit products, traces and identity reconstruction for rational dimensions \(n=1,\dots,5\); the general proof is (8). The original 2-plane \(J,M,[J,M]\) identities follow by a direct \(2\times2\) multiplication. The companion exact Wolfram script is saved under research/computations. None of these finite matrix checks asserts an algebraic Chow construction.

Original repo interfaces examined: GSTClassicalHodgeGeometryFirstTwoGenerator.lean, GSTHodgeSingleHypothesisConditional.lean, GSTFilteredK0SourceConservation.lean, GSTNCurrentCalibrationCompatibility.lean, GSTUniversalChowRetractToTarget.lean, the 2026-11-03 extension-sensitive causal fold paper, and the 2026-10-21 derived-ideal/Atiyah bridge record. These earlier source files did not establish universal K0 extraction from arbitrary coherent Yoneda classes; this derivation supplies the actual source/detector and a precise tested boundary. Novelty is not claimed.

**Verdict:** exact mathematical theorems for the stated Ext and \(K_0\) scope, based on standard Hodge/Serre/derived-category results; algebraic-Chow Hodge conjecture remains unproved. This is mathematics-first, self-audited; no Lean CI claimed.
