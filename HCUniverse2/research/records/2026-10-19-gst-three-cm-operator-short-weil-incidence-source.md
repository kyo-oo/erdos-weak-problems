# Mathbox GST — three genuine CM operators and minimal nonsplit Weil-sixfold incidence sources

**Date:** 2026-10-19. **Target:** original full rational Hodge conjecture \`GSTClassicalHodgeExactClayStatement.EveryHodgeClassIsRationalAlgebraic\`, especially the genuine primitive-source birth gate and a valid falsification route.

**Scope:** nonsplit polarized Weil-type abelian sixfold with \(K=\mathbf Q(i)\) and rational Hermitian form \(\mathrm{diag}(1,1,1,-1,-1,-3)\). Its signature is \((3,3)\) and discriminant square-class \(3\) does not lie in the norm group \(N(K^\times)\), so the hyperbolic sixfold source theorem in the pinned companion manuscript does not directly apply.

**Base:** \`66d2045d9e2f204f4933765da821de1187a79c35\` on the active branch \`research/gpt6-native-point-primitive-span-20261017\`. **Mathematical Lean module edited in place:** \`GSTUniversalCMArithmeticObstruction.lean\`.

## 1. A qualitatively shorter, exact algebraic Weil source projector

The original source filter was degree six in the actual algebraic isogeny \(T=[2+i]^*\):
\[
P_{\mathrm{old}}(T)=-
\frac{(T-125)(10391779+68381T)(T^2-150T+15625)(T^2+70T+15625)}
{930187500000000000}.
\]
It required seven graph words \(1,T,\ldots,T^6\), very large integer virtual weights, and difficult incidence geometry.

Add the *genuine algebraic* \(K\)-endomorphisms
\[
S=[1+i]^*,\quad U=[i]^*.
\]
On \(H^6(A,\mathbf Q)\), U acts as \((-1)^{j+1}\) on the \(j\)-th complex \(K\)-weight sector. Hence \((1-U)/2\) kills every odd weight. On even weights:
\[
\begin{aligned}
j=0,6 &: \quad 2T+234+11S=0,\ S^2+64=0,\\
j=2,4 &: \quad 2T-150-25S=0,\ S^2+64=0.
\end{aligned}
\]
Wolfram exact rational interpolation gives the complete projector:
\[
\boxed{\mathcal P_{\mathrm{Weil}}(T,S,U)
  =\frac{(1-U)(4800-32T+175S+3TS)}{19200}.}
\]
It takes value 1 at the pure Weil weights \(j=0,6\), zero at \(j=1,2,3,4,5\), and squares to itself on every sector. It uses **only eight** genuine algebraic graph correspondences from \(1,T,S,TS\) and their U-translates, with integral K0 coefficients
\[
(4800,-32,175,3,-4800,32,-175,-3)
\]
and denominator 19,200, rather than \(930187500000000000\). No prescribed Hodge-to-Chow inverse occurs in the polynomial.

**Earlier intermediate breakthrough:** combining U and T alone gave a cubic
\[
\frac{1-U}{2}\cdot
\frac{(T+234)(T^2-150T+15625)}{6000000}
\]
with denominator 12 million, and the same pure Weil spectral action. Adding S cuts the maximum isogeny word degree to 1 in each of T,S and reduces denominator further to 19,200.

**Exact kernel proofs:** \`cmWeilSixfoldThreeOperatorProjector_fixes_pure\`, \`_kills_odd\`, \`_kills_even_mixed\`, \`_idempotent\`, \`_integer_formula\`. The module preserves the former verified degree-six and cubic projectors instead of rewriting old correct work. The three-operator addition is **GREEN** at SHA \`2da35068d6f39399f15511fdb36b17dc455194ff\`, [pinned GH Lean CI #39274317430](https://github.com/kyo-oo/HC-PROOF/actions/runs/39274317430).

## 2. A connected *geometric* eight-graph incidence network with minimum-size bridges

At the genuine central CM point \(A=E^3_+\times E^3_-\), the four K-isogeny graph words have Gaussian slopes represented by \(a=(1,2+i,1+i,1+3i)\), and U changes the graph slope sign. The actual support labels are
\[
Z_0,Z_1,Z_2,Z_3,\;UZ_0,UZ_1,UZ_2,UZ_3.
\]

For supports indexed by \(v=(j,e)\) and \(w=(k,f)\) with \(e,f\in\{0,1\}\), the linear equations of the graph subvarieties yield determinant amplitude
\[
n(v,w)=
\begin{cases}
|\mathrm{Im}(a_j\bar a_k)|,&e=f,\\
|\mathrm{Re}(a_j\bar a_k)|,&e\ne f.
\end{cases}
\]
The actual pair-of-elliptic-factors finite intersection degree is \(4n(v,w)^2\), and for the two-kernel-divisor incidence \(W_{v,w}\), the standard Koszul/elliptic-RR source \(\mathrm{Ext}^2_A(\mathcal O_{W_{v,w}},\mathcal O_{Z_v})\) has an \(H^0\) summand of dimension
\[
\boxed{16\,n(v,w)^4}.
\]

With integer source signs \(+,-,+,+,-,+,-,-\), the seven edges
\[
(0,1),\ (0,4),\ (0,6),\ (0,7),\
(1,2),\ (3,4),\ (4,5)
\]
are opposite-sign and connect all eight supports. **Each has n=1**, so all seven needed candidate Ext² summands have dimension exactly 16. No opposite-sign support pair has n=0, so this is a minimum possible maximum for any such graph-incidence network. The parent function \( [0,0,1,4,0,4,0,0]\) certifies connectedness in at most two steps.

The proof uses the actual Gaussian labels of algebraic graph morphisms, not a freely assumed Hodge Gram rank. Kernel-checked Lean:
- \`cmWeilSixfoldThreeOpGraphTree_all_windings_one\`;
- \`cmWeilSixfoldThreeOpGraphTree_connected\`;
- \`cmWeilSixfoldThreeOpGraphTree_all_ExtTwo_sixteen\`;
- \`cmWeilSixfoldThreeOpGraphTree_lower_bound\`.

**GREEN** GH CI [#39274317430](https://github.com/kyo-oo/HC-PROOF/actions/runs/39274317430).

For comparison: the previous common seven-graph incidence constructed a **single** big W with \(h^0\mathrm{Ext}^2\ge 17324^2=300120976\), much larger than the dimension 495 of the entire raw semiregularity target for an abelian sixfold:
\[
\sum_{k=1}^6 h^{k-1,k+1}(A)
=\sum_{k=1}^6 \binom6{k-1}\binom6{k+1}=495.
\]
The intermediate two-operator source's best 8-support tree had maximal candidate Ext² dimension 1,296. Those statements have separate **GREEN** formal receipts [#39270822010](https://github.com/kyo-oo/HC-PROOF/actions/runs/39270822010), [#39273152643](https://github.com/kyo-oo/HC-PROOF/actions/runs/39273152643).

**CRITICAL distinction:** these are dimensions of the explicitly computed *global Ext² source summands on algebraic incidence geometries*, not a proved bound on the final unknown coupled sheaf's obstruction space. Injectivity of its full raw semiregularity map must be established in geometry; no dimension count proves it.

## 3. Exact central CM geometric source, corrected K signs

Take the true \(K\)-eigen sixth exterior form
\[
\Omega=\prod_{j=1}^{3}(e_j+i f_j)\wedge
       \prod_{j=4}^{6}(e_j-i f_j),\quad
W_R=\Re\Omega,\ W_I=\Im\Omega.
\]
For each \(j=1,2,3\), use the signed genuine algebraic diagonal-difference divisor
\[
D_j=[F_{j,1}]+[F_{j,2}]-[\Delta_{j,j+3}]
\]
on the two elliptic factors; its rational cohomology cross term is
\(e_j\wedge f_{j+3}-f_j\wedge e_{j+3}\). Let \(Z=D_1D_2D_3\in CH^3(E^6)_{\mathbf Q}\).

A full exact Wolfram exterior-algebra computation (all 64 pure-K monomials and 8 graph terms, orientation \(e_1\cdots e_6 f_1\cdots f_6\)) gives
\[
\int W_R\,Z=0,\quad
\int W_I\,Z=-8,\quad
\begin{pmatrix}\int W_R^2&\int W_RW_I\\\int W_IW_R&\int W_I^2\end{pmatrix}
=\begin{pmatrix}32&0\\0&32\end{pmatrix}.
\]
The CM weight decomposition is orthogonal for the top-degree cup product because \(T_jT_k\) has the top eigenvalue \(5^6\) only for complementary \(K\)-weights \(j+k=6\). Both the old and improved algebraic Weil projectors act as identity on this exceptional plane and annihilate its orthogonal complement. Therefore at this central product-CM period,
\[
\boxed{\mathrm{cl}(\mathcal P_{\mathrm{Weil}} Z)=-\tfrac14 W_I.}
\]
This is an **explicit genuine algebraic-cycle source** at the CM central fibre, not a guessed nonzero source or a false counterexample. The cup and projection computation is independently exact in Wolfram; its complete sixfold exterior algebra and geometric Betti comparison are not yet one fully instantiated Lean theorem.

## 4. PURE CENTRAL K0 GRAPH CHARACTER — an actual perfect-complex source

The central graph components \(Z_v\subset E^6\) are abelian *threefold subgroups* of the smooth sixfold. Their tangent inclusion is a constant inclusion of Lie algebras; hence their normal bundles are trivial rank-three bundles. For each closed immersion \(i_v:Z_v\hookrightarrow E^6\), Grothendieck--Riemann--Roch gives
\[
\operatorname{ch}(i_{v*}\mathcal O_{Z_v})
=\frac{i_{v*}\operatorname{Td}(T_{Z_v})}
       {\operatorname{Td}(T_{E^6})}
=i_{v*}(1)=[Z_v]
\quad\text{in }H^{6}(E^6,\mathbf Q),
\]
with **all other rational Chern-character degrees zero**. This uses the real geometric trivial tangent bundles of the abelian subgroup and ambient abelian variety; it is not a formal assumption that all abstract cycles have such a Chern character.

Therefore the **explicit integral virtual perfect class**
\[
\Xi=
4800[\mathcal O_{Z_0}]
-32[\mathcal O_{Z_T}]
+175[\mathcal O_{Z_S}]
+3[\mathcal O_{Z_{TS}}]
-4800[\mathcal O_{U Z_0}]
+32[\mathcal O_{U Z_T}]
-175[\mathcal O_{U Z_S}]
-3[\mathcal O_{U Z_{TS}}]\in K_0(E^6)
\]
is a genuine finite signed combination of actual coherent sheaves (hence representable by a finite perfect complex using odd shifts), with
\[
\boxed{\operatorname{ch}_3(\Xi)=-4800\,W_I,\qquad
\operatorname{ch}_{k\ne3}(\Xi)=0.}
\]
The equality follows from the verified exact projector \(\Xi=19200\,P_{\mathrm{Weil}}([\mathcal O_Z])\), the 64-term rational exterior computation \(\operatorname{cl}(P_{\mathrm{Weil}}Z)=-\tfrac14W_I\), and GRR for each genuine abelian graph subgroup. It is a **true algebraic source with pure Weil rational Chern character on the specific CM product sixfold**.

This source is VIRTUAL: an ordinary coherent sheaf whose smallest-dimensional support codimension is three has effective leading support cycle and strictly positive \(\theta^3\)-degree, while the nonzero pure Weil class satisfies \(W_I\cup\theta^3=0\) for a compatible polarization. Thus a semiregular **ordinary** sheaf transporting \(\Xi\)'s exceptional middle character must use an auxiliary higher-dimensional incidence support / nonzero lower Chern terms, or a different derived semiregularity theorem; one cannot insist it remain a purely codimension-three effective sheaf. This explains the necessity of the preceding incidence/sheaf coupling route mathematically rather than through a free existence hypothesis.

The GRR and exterior-geometric identifications in this subsection are written as mathematical derivations; the entire scheme-level Chern-character comparison for this specific \(E^6\) has not yet been separately instantiated in Lean's own abelian-scheme topology layer.

## 5. Immediate full-geometry research obligation

**Construct an ordinary semiregular coherent/perfect sheaf on the nonsplit sixfold period family** whose cohomological Chern character transports the above signed Weil source, using the EIGHT actual short CM graph supports and SEVEN minimal two-divisor incidence bridges. The critical design problem is *nontrivial coupling* between opposite \(K_0\) parities without simply replicating 4,800 uncoupled graph-sheaf summands. Large direct sums generally have off-diagonal raw Ext² trace kernels; these new low-degree incidences supply genuine connecting Ext² classes, but do not automatically solve the global derived lifting, nilpotent deformation obstruction or raw semiregularity injectivity.

Any ordinary coherent sheaf with pure primitive middle Chern character as its leading support cycle and no lower support terms would face the ample-degree positivity obstruction: effective codimension-three support has positive \(\theta^3\)-degree, whereas a pure Weil class is orthogonal to \(\theta^3\). Consequently the desired ordinary sheaf likely needs **nonzero lower Chern terms / an incidence carrier** so that the Weil class appears in its corrected higher Chern character; it cannot just be a sheaf supported on the pure signed primitive cycle.

A family \(\Gamma_t\in CH^3(A_t)_{\mathbb Q}\) with the genuine canonical Betti class of \(-W_I/4\) for all nonsplit periods would settle this **Weil sector**. To DISPROVE Hodge on one actual nonsplit A, conversely prove \(\mathcal P_{\mathrm{Weil}}\mathrm{cl}_A(Z)=0\) for *all* codimension-three algebraic cycles Z; finite source tests are not a universal negative theorem. The full all-varieties theorem remains a separate higher-quantifier goal.

**Evidence classification:** projector and rational incidence combinatorics kernel-proved; central product-CM exterior source exact computation plus standard geometric interpretation; semiregular all-period source birth not instantiated; full Hodge conjecture neither proved nor refuted.
