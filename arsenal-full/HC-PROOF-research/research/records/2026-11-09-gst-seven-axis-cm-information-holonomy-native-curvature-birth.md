# GST seven-axis information, cosmological CM folds, and all-order curvature: exact research burst

**Date:** 2026-11-09. **Repo/branch:** `kyo-oo/HC-PROOF` / `research/gpt6-native-point-primitive-span-20261017`.  
**Starting checkpoint:** `7e1b8607172c3108f04a8f8f2512f3da9751ec0c`.  
**Tools:** Mathbox research-program + research-attempt + computation-audit + proof-audit contracts, connected GitHub and Wolfram Language exact rational arithmetic.  
**Target:** advance the OWNER'S dimensionless seven-axis GST information transformation and its coupling to existing omniversal CM/NM geometry and the infinite formal curvature tower, not redesign the seven axes as spatial dimensions.

## 1. Information is not destroyed by the x4/base3 physical local transformation

The original `GSTCanonicalSevenAxisBridge`, `GST2DMixedEmergence`, `GSTGraphV2NonEuclidean` and `GSTGraphV2ProductionLaws` define an exact x4/base3 update. It is NOT a scalar update on the output trit alone: the full physical information cell is

\[
s=(C,d)\in\{0,1,2,3\}\times\{0,1,2\}.
\]

The exact edge law has the two outputs

\[
F(C,d)=(C',d'),\qquad
C'=\lfloor(C+4d)/3\rfloor,\quad d'=(C+4d)\bmod3.
\]

**Exact inverse (proved in new Lean):**

\[
\boxed{F^{-1}(C',d')=\big((d'+3C')\bmod4,\ \lfloor(d'+3C')/4\rfloor\big).}
\]

This is a permutation of all 12 physical states; it does not identify two different physical cells. The original seven-axis graph therefore possesses a provable *local information-preservation law* when the carry and trit are retained together.

**Stronger exact theorem (proved in new Lean):**

\[
\boxed{F^5=\mathrm{id}\quad\text{on all 12 physical cells}.}
\]

Its permutation structure is two cycles of length five and two fixed points. Writing the information code as `t=C+4d` gives cycles

\[
(1,4,5,9,3),\qquad (2,8,10,7,6),\qquad (0),\qquad(11).
\]

The two fixed cells are `(C,d)=(0,0)` and `(3,2)`. The period-five theorem is a state transformation law, NOT a claim of five spatial dimensions or of five-periodicity of the original horizontal energy `4^tE` for fixed E.

**Exact infinite-depth theorem (proved in new Lean):** on `u:Nat -> Cell` define `\mathcal F(u)(k)=F(u(k))`. Then

\[
\mathcal F^{-1}(\mathcal F(u))=u,\quad
\mathcal F^5(u)=u
\]

as whole infinite functions, without selecting a terminal information depth.

### Generalization: all positive radix pairs

For positive `m,n`, define the reordered information code

\[
F_{m,n}(t)=\lfloor t/n\rfloor +m(t\bmod n).
\]

**Universal conservation identity:**

\[
\boxed{F_{m,n}(t)+(mn-1)\lfloor t/n\rfloor=mt,}
\quad\Longrightarrow\quad
F_{m,n}(t)\equiv mt\pmod{mn-1}.
\]

The code interval `0<=t<=mn-1` is permuted. `0` and `mn-1` are fixed; interior codes are permuted by multiplication by m modulo mn-1, which is invertible because `gcd(m,mn-1)=1`. Therefore the finite-order period on the interior is controlled by the multiplicative order of m modulo mn-1 (when the modulus exceeds 1). For m=4,n=3, the modulus is 11 and \(4^5\equiv1\pmod{11}\), explaining the special period-five theorem.

**Wolfram exact check:** all 36 positive radix pairs m,n∈{2,...,7} passed both the modular identity and the permutation check for every code in 0,...,mn-1. The preceding algebra, not the bounded check, establishes the universal identity.

## 2. CM geometric odd curvature is mathematically distinct from a change of coordinates

Take a noncommutative associative rational operator algebra and J²=-1, as in the branch's `GSTCMQuadraticNativeRankForcing` imaginary-quadratic CM route.

Define doubled parity projections (no division needed):

\[
E_J(A)=A-JAJ,\qquad O_J(A)=A+JAJ,\quad E_J(A)+O_J(A)=2A.
\]

Then \(JE_J(A)=E_J(A)J\), \(JO_J(A)=-O_J(A)J\), and the CM fold curvature is

\[
\boxed{\mathcal R_J(A)=[J,A]=JA-AJ=J O_J(A).}
\]

As J is invertible (inverse \(-J\)), \(\mathcal R_J(A)=0\iff O_J(A)=0\). This gives an exact test for a *genuinely J-breaking* fold component rather than a chosen readout.

The noncommutative composition and Bianchi laws are:

\[
[J,AB]=[J,A]B+A[J,B],\qquad
[A,[B,C]]+[B,[C,A]]+[C,[A,B]]=0.
\]

A stronger **CM parity product law** useful for all-order memory is

\[
2 E_J(AB)=E_J(A)E_J(B)+O_J(A)O_J(B),
\]
\[
2 O_J(AB)=E_J(A)O_J(B)+O_J(A)E_J(B).
\]

Consequently, two J-odd fold modes can produce a J-even second-order interaction; the J-odd interaction terms are exactly the mixed even-odd products. These identities work in arbitrary associative rings with J²=-1; when normalized by 2 over rational coefficients they give a strict Z/2 operator splitting.

### All-order curvature tower dictionary

The existing `GSTFoldTowerSquare.JetTowerInf` and `GSTInfiniteTowerCurvatureCascade` already define actual unbounded formal memory levels:

\[
D=d+\sum_{k\ge0}\varepsilon^{k+1}\phi_k,\qquad
K_k=d\phi_k+\phi_kd+\sum_{i+j=k-1}\phi_i\phi_j.
\]

This is a *formal* power series and each coefficient contains only a finite sum; it is not an analytic assertion that the series converges.

Under a J-equivariant base differential (`[J,d]=0`), the parity product laws yield, for every natural index k, the graded recursions

\[
E_J(K_k)=dE_J(\phi_k)+E_J(\phi_k)d
+\frac12\sum_{i+j=k-1}\left(E_J(\phi_i)E_J(\phi_j)
+O_J(\phi_i)O_J(\phi_j)\right),
\]
\[
O_J(K_k)=dO_J(\phi_k)+O_J(\phi_k)d
+\frac12\sum_{i+j=k-1}\left(E_J(\phi_i)O_J(\phi_j)
+O_J(\phi_i)E_J(\phi_j)\right).
\]

These follow algebraically from the ring identities; **this full tower recursion is derived here at proof-on-paper level**, while the new Lean integration formalizes its universal operator ingredients and all-index graph-modulated CM readout, not yet these two displayed full convolution recursions as named kernels.

## 3. Strong observation: lossless fivefold information does not imply zero ordered holonomy

Attach two rational CM operators J,K to an information cell via the original carry and trit:

\[
P(C,d)=C J+d K,\qquad
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\quad
K=\begin{pmatrix}1&0\\0&-1\end{pmatrix},\quad
J^2=-I,\quad JK=-KJ.
\]

For the actual five-cycle

\[
(0,1)\to(1,1)\to(1,2)\to(3,0)\to(1,0)\to(0,1)
\]

put \(\Delta_i=P(s_{i+1})-P(s_i)\). Then

\[
\Delta_0=J,\quad \Delta_1=K,\quad
\Delta_2=2J-2K,\quad \Delta_3=-2J,\quad \Delta_4=K-J.
\]

So \(\sum_i\Delta_i=0\) and also \(\sum_i[J,\Delta_i]=0\), yet

\[
\boxed{[\Delta_0,\Delta_1]=[J,K]
=\begin{pmatrix}0&2\\2&0\end{pmatrix}\ne0.}
\]

Thus the **second-order noncommutative curvature is nonzero on an exactly information-conserving cycle**.

A harder exact test: define an ordered fold transport

\[
U(\varepsilon)=\prod_{i=0}^{4}(I+\varepsilon\Delta_i)
\]

in the orbit order. Its linear term is zero, but its quadratic term is

\[
\boxed{[\varepsilon^2]U(\varepsilon)
=\sum_{i<j}\Delta_i\Delta_j
=\begin{pmatrix}2&-5\\-5&2\end{pmatrix}\ne0.}
\]

At rational \(\varepsilon=1/10\), exact Wolfram arithmetic gives

\[
U(1/10)=
\begin{pmatrix}
12949/12500&-591/12500\\
-307/6250&3144/3125
\end{pmatrix},\quad
\det U(1/10)=129987/125000\ne0.
\]

All five transport matrices are individually invertible: their exact determinants are `101/100, 99/100, 1, 26/25, 1`. The complete ordered product is itself invertible but **not the identity**.

This is a precise GST mechanism: **local information returns, while order-sensitive fold memory can survive the completed orbit**. The total additive curvature vanishes because it is an exact discrete coboundary; the noncommutative ordered product is a different observable. It would be erroneous to identify the two.

## 4. From curvature to an actual original-X algebraic-cycle source

The most important geometric next connection uses the branch's existing `CycleClassOperatorPair V H p`, which has actual rational native-cycle operator N, ambient cohomology operator T, and the verified cycle-class commuting square.

For two such genuinely geometric pairs A and B and a native cycle Z on the ORIGINAL X, define the explicit **native curvature birth cycle**

\[
\boxed{Z_{AB}:=N_A N_B Z-N_B N_A Z\in CH^p(X)_{\mathbb Q}.}
\]

Cycle-class naturality alone derives the exact equation

\[
\boxed{\mathrm{cl}_X(Z_{AB})
=[T_A,T_B]\,\mathrm{cl}_X(Z).}
\]

This is an actual algebraic-cycle constructor whenever A and B are genuine native operations (the existing `RealizedFiniteClosedCorrespondence` adapter is one admissible carrier). It is NOT a free Hodge-to-Chow inverse.

**Source-rank discovery test:** let W_old be a rational subspace of the actual Hodge fiber. If an independently geometric readout \(\ell\) vanishes on W_old but

\[
\ell([T_A,T_B]\mathrm{cl}(Z))\ne0,
\]

then the new genuine native cycle class lies **outside** W_old. That provides a concrete and falsifiable geometric rank-gain certificate.

**Sharp opposite test:** if both T_A and T_B preserve W_old and \(\mathrm{cl}(Z)\in W_{old}\), then \([T_A,T_B]\mathrm{cl}(Z)\in W_{old}\) automatically. Thus any new-source mechanism must exhibit actual operator mixing; the abstract existence of a nonzero commutator alone does not establish escape. This explains exactly what the GST graph+CM geometry must **construct**, not merely rename.

## 5. Exact repository architecture and semantic boundaries

This is an additive upgrade, not replacement:

- Original dimensionless seven-axis arithmetic and its x4/base3 laws: `GSTCanonicalSevenAxisBridge.lean`, `GSTGraphV2NonEuclidean.lean`, `GSTGraphV2ProductionLaws.lean`.
- Carrier-free causal ontology: `GSTGraphV2OmniversalCore.lean` and causal-component quotient `GSTGraphV2CausalComponents.lean`.
- Information-preserving local and infinite-depth transformations: **new** `GSTGraphV2InformationRecovery.lean`; arbitrary-radix exact law: **new** `GSTGraphV2GeneralRadixConservation.lean`.
- Recursive causal worlds and actual mathematical birth interfaces: `GSTGraphV2SelfExpandingCosmology.lean`, `GSTGraphV2UnboundedHigherCausality.lean`, `GSTGraphV2OmniversalHyperEvents.lean`.
- Already existing true native Hodge/CM/NM event graph: `GSTGraphV2CMNMPrimitiveUpgrade.lean`, `GSTGraphV2CMNMCoupledUniverse.lean`, plus `GSTCMQuadraticNativeRankForcing.lean`.
- Full unbounded formal curvature memory: `GSTFoldTowerSquare.lean` and `GSTInfiniteTowerCurvatureCascade.lean`; combined readout and CM parity split: **new** `GSTGraphV2CMInfiniteCurvatureBridge.lean`.
- Genuine original-X curvature algebraic cycle constructor and rank-gain criterion: **new** `GSTGraphV2NativeCurvatureBirth.lean`.

**Crucial observational distinction:** Applying the local 12-state shuffle repeatedly is an abstract information-state transformation. Its period 5 is not the assertion that the global arithmetic energy 4^tE, the geometric variety X, or the original event graph itself has five-period dynamics. Similarly, attaching curvature operators to each cell is an additional testable realization; the graph-to-actual-geometric-operator comparison requires the existing native and cohomological correspondence semantics.

## 6. Exact computation record and validation scope

All Wolfram calculations above use exact integers/rationals (no floating tolerance). The finite matrix example is a **witness that the second-order curvature phenomenon is possible**, not a theorem that all CM algebraic correspondences exhibit it.

- Exact 12-state permutation F and cycle lengths 5,5,1,1.
- Universal-radix finite check m,n=2,..,7: 36 pairs, every code in 0,..,mn-1, zero failures. The universal formula has an independent all-m,n proof.
- CM J²=-I, even and odd projections and the nonzero local commutator.
- Full ordered product polynomial and exact rational ε=1/10 invertible holonomy.
- Exact operator identities have corresponding new Lean declarations; read the actual GitHub Actions status and logs for the final verification verdict (do not infer from committed text).

## 7. Critical mathematical continuation

Use the established GST graph information-orbit and **genuine original-X curvature cycles** as input to the existing Hodge cyclicity mechanism, not an arbitrary abstract linear endomorphism:

1. Select actual native correspondences \(A,B\) by a specified GST/CM/Number Manipulation rule applied to geometric data of \(X\) and its Hodge-marked class, without secretly inserting a pre-known representative.
2. Construct \(Z_{AB}\) on the original X using actual native push-pull and compute its **canonical** whole-Betti class through the same geometric correspondence.
3. Find a geometrically fixed (not after-the-fact chosen) detector \(\ell\) showing curvature-source escape from the old native orbit. The new Lean detector/rank lemma is an exact check of this implication.
4. Iterate across the CM parity-graded infinite curvature carrier and cosmological multiworld birth rules, preserving actual algebraic-cycle semantics, to seek a covering orbit for the prescribed Hodge directions.

This is a concrete source-generation route. The thing to calculate next is the geometric *off-diagonal curvature block* \(\operatorname{pr}_{W_{old}^{\perp}}[T_A,T_B]|_{W_{old}}\), on a specified smooth projective source with actual Chow correspondences, rather than another arbitrary moment determinant on an already-algebraic model.


## 8. GENUINE HIGHER-CODIMENSION CURVATURE SOURCE: A CM ABELIAN FOURFOLD

This section is a **new composition** of the existing exact elliptic-product Chow matrix-unit construction in `research/derivations/GST_single_hypothesis_fold_moment_conditional_2026_11_08.tex` (lines 188–219), the new original-X curvature cycle theorem, and a fixed geometric detector.

Let `X=E₁×E₂×E₃×E₄` for pairwise nonisogenous **CM elliptic curves**. It is a smooth projective complex **fourfold**. Let `d_i` be the pullback of the point-divisor class from factor `E_i`; for any 2-subset I of {1,2,3,4}, define the actual codimension-two algebraic cycle `D_I = ∏_{i∈I} d_i`.

The six `D_I` have independent rational Betti classes. The exact geometric intersection law is

\[
\int_X D_I\,D_{J^c}=\delta_{IJ}
\]

for |I|=|J|=2, because \(d_i^2=0\) and \(\prod_i d_i\) has degree one. Hence the actual algebraic correspondences on `X×X`

\[
\Gamma_{JI}:=\pi_1^*D_{I^c}\cdot\pi_2^*D_J\in\CH^4(X\times X)_\mathbb Q
\]

satisfy \((\Gamma_{JI})_*D_K=\delta_{IK}D_J\).

Choose distinct labels `I₀={1,2}`, `I₁={1,3}`, and put

\[
A=\Gamma_{I_0 I_0},\quad B=\Gamma_{I_1 I_0},\quad Z=D_{I_0}.
\]

Then A is the native projector to the first divisor-product direction and B maps that direction into the second:

\[
A Z=Z,\quad B Z=D_{I_1},\quad A(BZ)=0,\quad B(AZ)=D_{I_1}.
\]

The **actual original-X codimension-two curvature cycle** is

\[
\boxed{Z_{AB}=A(BZ)-B(AZ)=-D_{I_1}.}
\]

The geometric detector `ℓ(α)=∫_X α·cl(D_{I₁^c})` is fixed by the actual intersection pairing. It annihilates the old span `W_old=Q·cl(D_{I₀})`, but

\[
\boxed{\ell(\mathrm{cl}(Z_{AB}))=-1\ne0.}
\]

Thus the commutator produces a new actual middle-degree algebraic Hodge direction outside the initial one-dimensional sector, in complex dimension four and codimension two. In the six-dimensional divisor-product sector, the exact Wolfram 6×6 test outputs

```
curvatureAppliedToD_12 = {0,-1,0,0,0,0}
geometricDetectorOld = 0
geometricDetectorNew = -1
rank(old, curvature) = 2
```

**Scope:** These are explicitly known algebraic divisor-product classes, not every rational primitive (2,2) Hodge direction on an arbitrary fourfold. The new contribution of this example is a nontrivial **genuine algebraic correspondence curvature birth mechanism** beyond a purely linear-matrix analogy. It is an exact geometric benchmark for stronger GST/CM source constructions.

## 9. Verified implementation and computation receipts

- `GSTGraphV2InformationRecovery.lean`: exact physical inversion, order-five and all-depth stream recovery — GitHub Actions [42534272752](https://github.com/kyo-oo/HC-PROOF/actions/runs/42534272752) **SUCCESS**.
- `GSTGraphV2GeneralRadixConservation.lean`: arbitrary positive-radix mass balance and modulus — GitHub Actions [42535812117](https://github.com/kyo-oo/HC-PROOF/actions/runs/42535812117) **SUCCESS**.
- `GSTGraphV2CMInfiniteCurvatureBridge.lean`: CM parity splitting and product grading, Jacobi/Bianchi, zero fivefold additive curvature, nonzero consecutive fold commutator, and JetTowerInf readout — the **same** GitHub Actions [42535812117](https://github.com/kyo-oo/HC-PROOF/actions/runs/42535812117) **SUCCESS**.
- `GSTGraphV2NativeCurvatureBirth.lean`: actual original-X commutator cycle with exact cycle-class identity and geometric rank escape/invariance tests — GitHub Actions [42535736525](https://github.com/kyo-oo/HC-PROOF/actions/runs/42535736525) **SUCCESS**.
- Exact Wolfram script `research/computations/gst_seven_axis_cm_curvature_holonomy_20261109.wl` was fetched back from the committed GitHub file and executed unchanged in Wolfram Language; results: all logical checks True, rational ordered holonomy as in Section 3, and six-dimensional fourfold middle-sector rank gain as in Section 8.

The two original source files `GSTCanonicalSevenAxisBridge.lean` and `GSTGraphV2NonEuclidean.lean` were **not** rewritten; their fundamental laws and dimensionless seven axes remain intact. The older `docs/GST_V2_OPERATING_MANUAL.md` has instead been upgraded to explicitly record the new conservation and curvature theorems.
