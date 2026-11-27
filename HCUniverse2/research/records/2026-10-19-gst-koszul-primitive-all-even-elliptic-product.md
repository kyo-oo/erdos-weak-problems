# Mathbox: GST independent algebraic perfect-complex primitive births in ALL even dimensions

**Date:** 2026-10-19 · **Main target unchanged:** for every original smooth projective complex X, every p and every rational (p,p) class alpha, construct a rational Chow cycle with genuine canonical Betti class alpha. **Active route:** actual algebraic K₀ sources, finite-flat Chow projection, polarized GST native frame. **First checkpoint:** c7e5ca0ef1b47cfd205b304707b1bfcf3b9c5484. **Lean changes:** GSTUniversalResolvedSupportHodge.lean, including a concrete rank-two elliptic-fourfold source family and a dimension-uniform Koszul lemma.

## 1. Geometric source, original X, exact types

Let the ORIGINAL complex projective abelian variety be \(X=E_1\times\cdots\times E_{2m}\), where \(m\ge1\) and each \(E_j\) is a smooth projective elliptic curve. Choose a degree-one line bundle \(L_j\) on \(E_j\); denote its first Chern class on X by \(x_j=c_1(\operatorname{pr}_j^*L_j)\in CH^1(X)_\mathbb Q\).

The true algebraic Chow relations are \(x_j^2=0\); \(H=\sum_j x_j\) is a genuine ample polarization, and \(\int_X x_1\cdots x_{2m}=1\). The integral perfect-complex K-class
\[
\mathcal E_m=\bigotimes_{k=1}^m ([L_{2k-1}]-[L_{2k}])
\in K_0(X)
\]
is constructed independently of an arbitrary Hodge target alpha. Every factor has Chern-character degree-zero part zero, degree-one part \(x_{2k-1}-x_{2k}\). Therefore the FIRST nonzero rational GRR/Chow degree of \(\mathcal E_m\) is exactly
\[
\boxed{Z_m=\prod_{k=1}^m(x_{2k-1}-x_{2k})\in CH^m(X)_\mathbb Q.}
\]
No Chern/homology target witness is among the input data.

## 2. Dimension-uniform exact polarized primitive source

For ANY commutative coefficient ring and any paired square-zero classes \(u_k,v_k\) one has
\[
(u_k+v_k)(u_k-v_k)=u_k^2-v_k^2=0,\qquad
(u_k-v_k)^2=-2u_kv_k.
\]
Since \(H=\sum_k(u_k+v_k)\) and \(Z=\prod_k(u_k-v_k)\),
\[
\boxed{HZ=0,\quad Z^2=(-2)^m\prod_k u_kv_k.}
\]
On the actual original X, the product of all factor divisors integrates to one. Thus
\[
\boxed{(-1)^m\int_X Z_m^2=2^m>0.}
\]
This supplies a genuinely nonzero middle Lefschetz-primitive (m,m) algebraic class on EVERY such original X, despite \(T_X\) being trivial and tangent Chern sources therefore vanishing.

The exact general-rank Lean proof uses the list-valued \`hyperplaneOfPairs\` and \`koszulPrimitiveSource\` inside namespace \`GSTNativeAbelianKoszulAllEvenDimensions\`. It proves both equalities inductively for arbitrary list length, with square-zero divisors as the only algebraic relations. Its GH Actions status must be determined from the revision-matched run, rather than presumed.

### GST finite-flat K₀ projection fixes EVERY Koszul birth without correction

These sources have a stronger property than simply having a nonzero leading primitive Chern class: their Chern character is **PURE of degree m**. Indeed \(x_i^2=0\) implies
\(\mathrm{ch}([L_i]-[L_j])=e^{x_i}-e^{x_j}=x_i-x_j\) EXACTLY (higher degree terms vanish individually), so
\[
\mathrm{ch}(\mathcal E_M)=Z_M\quad\text{with no other Chow degrees.}
\]
The ample \(H=\sum_i x_i\) need NOT be globally generated because a degree-one line bundle on an elliptic curve has only one section. Choose instead a sufficiently positive integer \(k\) (for instance \(k\ge3\) on every factor) so that \(kH\) is very ample, and take a genuine finite linear projection \(f:X\to\mathbb P^{2m}\) with \(f^*O(1)=kH\). Since \(H Z_M=0\), one has \((kH)^m Z_M=0\) and hence
\(f_*Z_M=0\in CH^m(\mathbb P^{2m})_\mathbb Q\): the sole projective Chow coefficient is \(\int_X Z_M (kH)^m=0\). For an abelian variety \(T_X\) is algebraically trivial, hence \(\mathrm{Td}(T_X)=1\). Genuine GRR says
\[
\mathrm{ch}(f_*\mathcal E_M)\,\mathrm{Td}(T_{\mathbb P^{2m}})
=f_*(\mathrm{ch}(\mathcal E_M)\,\mathrm{Td}(T_X))
=f_*Z_M=0.
\]
The projective Todd class is invertible and the rational Chern character is injective on \(K_0(\mathbb P^{2m})_\mathbb Q\). Therefore the **actual algebraic K₀ pushforward vanishes**
\[
\boxed{f_*\mathcal E_M=0\in K_0(\mathbb P^{2m})_\mathbb Q,\qquad
\mathcal P_f^K(\mathcal E_M)=\mathcal E_M.}
\]
Consequently the FULL matching basis and all target-selected rational combinations already lie in the exact fixed-point subspace of GST's normalized finite-flat K₀ projector. They require neither an abstract source birth nor an extra Todd/degree correction; the source is a real independently constructed bounded perfect complex built from line bundles.

This proof uses the **genuine projective GRR and rational Chern isomorphism as mathematical geometry**. The current generic Lean source module already proves \`normalizedVirtualPrimitive_fixes_kernel\`; fully instantiating scheme K₀/GRR and canonical Betti comparison remains a separate implementation obligation.

## 3. Two independently born primitive cycles on one abelian fourfold

For \(m=2\), the already present P source is joined by a second algebraic virtual perfect complex:
\[
\begin{split}
P&=(x_1-x_2)(x_3-x_4),\\
Q&=(x_1-x_3)(x_2-x_4).
\end{split}
\]
Both are Chow codimension two and Lefschetz-primitive for \(H=\sum_{i=1}^4 x_i\). In the **genuine squarefree divisor product basis** \((x_{12},x_{13},x_{14},x_{23},x_{24},x_{34})\),
\[
P=(0,1,-1,-1,1,0),\quad
Q=(1,0,-1,-1,0,1).
\]
The cup/cap intersection pairing only pairs complementary 2-sets, so
\[
\boxed{G(P,Q)=\begin{pmatrix}4&2\\2&4\end{pmatrix},\qquad
\det G=12,\quad G^{-1}=\tfrac1{12}\begin{pmatrix}4&-2\\-2&4\end{pmatrix}.}
\]
For any actual prescribed primitive Hodge alpha, put \(a=Q(\alpha,P)\), \(b=Q(\alpha,Q)\). The target-directed original-X rational algebraic combination is
\[
\boxed{Z_\alpha=\frac{2a-b}{6}P+\frac{2b-a}{6}Q.}
\]
The **exact** two period equalities are
\(Q(Z_\alpha,P)=a,\ Q(Z_\alpha,Q)=b\), and
\[
\boxed{Q(\alpha,Z_\alpha)=\frac{a^2-ab+b^2}{3}>0}
\]
when \((a,b)\ne(0,0)\). The positivity is elementary via \(4(a^2-ab+b^2)=(2a-b)^2+3b^2>0\). This is a native target-sensitive algebraic perfect-complex source, with no alpha Chow preimage among the assumptions.

Wolfram exact-rational test on 2026-10-19: cup(P)=cup(Q)=(0,0,0,0), G=[[4,2],[2,4]], det(G)=12, inverse=[[1/3,-1/6],[-1/6,1/3]], exact period recovery, exact target coupling \(a^2/3-ab/3+b^2/3\), positivity for real a,b not both zero.

The Lean definitions/theorems \`GSTNativeAbelianKoszulRankTwo.nativeKoszulP\`, \`nativeKoszulQ\`, \`nativeKoszul_two_source_gram_determinant\`, \`nativeKoszulTargetCycle_P_period\`, \`nativeKoszulTargetCycle_Q_period\`, \`nativeKoszulTargetCycle_primitive\`, and \`nativeKoszulTargetCycle_target_pairing\` were committed into the EXISTING GSTUniversalResolvedSupportHodge.lean. A small tactic-level conjunction correction was applied after first CI reported a \`True ∧ True ∧ True\` residual; do not label this suite kernel-green until the new CI run succeeds.

## 4. Larger rank: explicit Catalan-family experiment

For every noncrossing perfect matching \(M\) of \(\{1,\dots,2m\}\), the actual integral \(K_0\) perfect complex made from factors \([L_i]-[L_j]\) defines another primitive Chow source
\[
Z_M=\prod_{(i,j)\in M}(x_i-x_j).
\]
The number of noncrossing matchings is the Catalan number \(C_m=\frac1{m+1}\binom{2m}{m}\). A *potential* stronger GST law is that the \(Z_M\) provide a native \(\mathbb Q\)-basis of the primitive squarefree divisor-product sector \(\ker(H: \mathcal A_m\to\mathcal A_{m+1})\), where \(\mathcal A=\mathbb Q[x_1,\dots,x_{2m}]/(x_1^2,\dots,x_{2m}^2)\). The dimension predicted by the projective-product Lefschetz module is
\[
\dim\ker H=\binom{2m}{m}-\binom{2m}{m-1}=C_m.
\]

**Finite exact computational audit** (2026-10-19): independently enumerate ALL noncrossing matchings recursively, expand each cycle into the squarefree degree-m monomial basis with coefficients in \(\{-1,0,1\}\), compute matrix ranks modulo the fixed exact prime 1,000,003 (no randomization, floats or sampling), and compare to the entire theoretical Catalan dimension. Results:

| m | noncrossing complexes | matrix shape | exact rank mod 1,000,003 | Catalan |
|---|---:|---:|---:|---:|
| 1 | 1 | 2×1 | 1 | 1 |
| 2 | 2 | 6×2 | 2 | 2 |
| 3 | 5 | 20×5 | 5 | 5 |
| 4 | 14 | 70×14 | 14 | 14 |
| 5 | 42 | 252×42 | 42 | 42 |

The signed rational intersection Gram \(G_{MN}=(-1)^m\int_X Z_M Z_N\) was also constructed EXACTLY as the complement-incidence product matrix. Its exact Gram determinant is 2 at m=1, 12 at m=2, 5184 at m=3 and 8,358,844,170,240 at m=4; exact finite-field Gram rank is 42 at m=5. The m=3 Gram matrix in the recursive matching order is
\[
\begin{pmatrix}
8&-4&-4&2&-4\\
-4&8&2&-4&2\\
-4&2&8&-4&2\\
2&-4&-4&8&-4\\
-4&2&2&-4&8
\end{pmatrix}
\]
with det=5184. These are exact FINITE tests, not proof that all m has full Catalan rank.

### Dimension-uniform Catalan GST native basis: explicit mathematical proof

**Theorem.** Over Q, for EVERY integer m≥1 and original X=E1×...×E(2m), the integral perfect-complex classes \(\mathcal E_M=\bigotimes_{(i,j)\in M}([L_i]-[L_j])\) indexed by noncrossing perfect matchings M have algebraic leading Chern classes \(Z_M=\prod_{(i,j)\in M}(x_i-x_j)\) that form a **Q-basis of the full primitive squarefree divisor-product subspace** \(\ker[H:\mathcal A_m\to\mathcal A_{m+1}]\), where \(\mathcal A=\mathbb Q[x_1,\ldots,x_{2m}]/(x_i^2)\). Here "full" refers only to the geometric **divisor-product** subspace, NOT the complete rational primitive Hodge space of X.

*Proof, step 1 (each source primitive).* Every x_i has square zero and \(H=\sum_{(i,j)\in M}(x_i+x_j)\). Since \((x_i+x_j)(x_i-x_j)=0\), each term of \(HZ_M\) is zero. This is exactly the arbitrary-length identity in the existing Lean module.

*Proof, step 2 (independent through an integral triangular matrix).* Write every matching pair as i<j. Let \(L(M)\) be the m-element subset of all left endpoints. In the polynomial expansion of \(Z_M\), the coefficient of the distinguished squarefree monomial \(x_{L(M)}=\prod_{i\in L(M)}x_i\) equals **+1**, since it picks the left term from EVERY pair. All other nonzero monomials are obtained by replacing some left endpoints i by larger right endpoints j. Consequently their ordered m-element index sets are lexicographically **no smaller** than \(L(M)\). A noncrossing matching is uniquely determined by its left-endpoint set: reading the positions left-to-right, connect each right endpoint to the last as-yet unmatched left endpoint (stack algorithm); the matching is necessarily nested or disjoint, and this procedure recovers it uniquely. Order the noncrossing matchings by lexicographic left-endpoint sets and take the square submatrix of the coefficient matrix whose rows are precisely these distinguished monomials and whose columns are the matching cycles. Entries above the permitted triangular side vanish by the lex property and **every diagonal entry is +1**. This matrix has determinant +1. Thus these genuinely algebraic K₀ sources are linearly independent **integrally**, for arbitrary m, without randomization or an analytic assumption.

*Proof, step 3 (compute the complete primitive dimension directly).* Let \(\mathcal A_k\) have its squarefree-monomial orthonormal basis and let \(U_k:\mathcal A_k\to\mathcal A_{k+1}\) multiply by H. Its adjoint \(D_{k+1}\) deletes one variable from a monomial. Directly count additions/removals of indices to obtain
\[
D_{k+1}U_k-U_{k-1}D_k=(2m-2k)\,\mathrm{id}_{\mathcal A_k}.
\]
For k<m this implies
\[
\|U_kv\|^2=\|D_kv\|^2+(2m-2k)\|v\|^2,
\]
so \(U_{m-1}\) is injective. Complementation of subsets identifies \(D_{m+1}\) with \(U_{m-1}\), so \(D_{m+1}\) is injective, and its adjoint \(U_m\) is surjective. Hence
\[
\dim_{\mathbb Q}\ker U_m
=\binom{2m}{m}-\binom{2m}{m+1}
=\frac1{m+1}\binom{2m}{m}=C_m.
\]
Meanwhile the noncrossing matchings have exactly \(C_m\) elements: the partner of index 1 divides the remainder into two smaller independent noncrossing matchings, giving the Catalan recurrence \(C_m=\sum_{k=0}^{m-1}C_k C_{m-1-k}\), \(C_0=1\). Since the \(C_m\) constructed cycles are independent and in the primitive kernel of dimension \(C_m\), they form a basis. QED.

*Consequences for GST.* The signed middle primitive Hodge–Riemann intersection pairing is positive definite on the full rational primitive divisor-product sector (or equivalently the squarefree algebra carries the positive real/Kähler inner product). Therefore the Gram matrix \(G_{MN}=(-1)^m\int_X Z_M Z_N\) is positive definite and invertible over Q in every m. For EVERY prescribed rational primitive Hodge class alpha, measured periods \(a_M=(-1)^m\int_X\alpha\,Z_M\) yield an actual rational algebraic K₀ perfect-complex and Chow-cycle compiler
\[
\boxed{
Z_\alpha^{\mathrm{div}}=
\sum_{M,N} Z_M (G^{-1})_{MN} a_N.
}
\]
This class matches **every** period against the full squarefree primitive divisor-product sector, and represents alpha exactly WHEN alpha belongs to that sector. This replaces any assumed nonzero determinant and any target-by-target algebraic source selection with a finite, explicit, geometrically constructed complete frame for the named sector, uniformly in dimension.

**Proof scope:** The algebraic proof above is complete for the squarefree divisor-word primitive sector of products of elliptic curves, conditional only on the standard explicit Chow relations \(x_i^2=0\), degree-one intersection and algebraic line bundle Chern construction. Lean currently kernel-checks the arbitrary-m primitivity and square identity (not the full combinatorial noncrossing basis argument). The finite m=1..5 computations are independent reproducibility checks, not the justification for the general theorem. This statement does not identify the squarefree sector with all rational Hodge classes or with exotic nonsplit Weil classes.

### GST full-rank integer Gram law and ACTUAL perfect-complex realization for any target in the sector

The Catalan basis proof upgrades the GST native source frame from a prescribed rank into a **finite algorithmically enumerable, invertible, integral Gram matrix in EVERY m**. There is also an exact geometric closed description of its entries, not merely an assumed detector matrix.

Overlay two noncrossing perfect matchings M,N as graphs on the same 2m labeled elliptic factors. Their union consists of disjoint alternating even cycles (an edge of M then an edge of N; common edges are length-two multicycles). Call the number of connected components c(M,N). When expanding \(Z_M Z_N\), a term contributes to the top class \(\prod_i x_i\) iff every vertex is selected precisely once by one of its incident factors. On each alternating component there are exactly TWO valid alternating choices, and the two choices have the SAME sign because they exchange selections in an even number of factors. Thus there are exactly \(2^{c(M,N)}\) contributing terms, all of the same sign determined by the orientations \(i<j\) of the line-bundle differences. Therefore
\[
\boxed{\left|(-1)^m\int_X Z_M Z_N\right|=2^{c(M,N)}.}
\]
The sign is computed combinatorially by choosing either alternating coloring and counting factors selecting their larger-labeled endpoint. This formula constructs EVERY integer Gram entry from the actual perfect-complex pairing graph and defines a deterministic arbitrary-rank GST geometric readout.

The dimension-uniform Catalan basis and positive-definite signed primitive intersection form imply \(G_m\) is an **invertible integer matrix** with positive integer determinant \(D_m=\det G_m\). Given an arbitrary rational primitive Hodge alpha on this original X, put \(a_M=(-1)^m\int_X\alpha Z_M\in\mathbb Q\). Define the actual rational source
\[
\mathcal E_\alpha^{\rm rat}
=\sum_{M,N}(G_m^{-1})_{MN}\,a_N\,\mathcal E_M
\in K_0(X)_\mathbb Q .
\]
Then \(Z_\alpha^{\rm div}=\operatorname{ch}_m(\mathcal E_\alpha^{\rm rat})\) is the true algebraic Chow cycle matching all primitive divisor-source periods.

**Finite denominator → one genuine bounded perfect complex.** Choose a positive integer N so that \(N a_M\in\mathbb Z\) for every M. Since \(G_m^{-1}=\operatorname{adj}(G_m)/D_m\) and the adjugate is integral, the class
\[
\boxed{\widetilde{\mathcal E}_\alpha
=N D_m\,\mathcal E_\alpha^{\rm rat}
=\sum_{M,N}\operatorname{adj}(G_m)_{MN}
   (N a_N)\,\mathcal E_M
\in K_0(X)}
\]
has INTEGER coefficients of genuine integral tensor-of-line-bundle-difference sources. Each \(\mathcal E_M\) expands as a signed finite sum of actual line-bundle tensor products. Assemble the positive terms in even cohomological degree and negative terms in odd cohomological degree; this produces an **actual bounded perfect complex of algebraic vector bundles on the ORIGINAL X** representing \(\widetilde{\mathcal E}_\alpha\). Its true degree-m Chern character is exactly \(N D_m\,Z_\alpha^{\rm div}\). The rational Chow target is recovered by dividing by \(ND_m\), as required for rational Hodge classes.

This is a uniform target-sensitive **constructive perfect-complex realization** for the ENTIRE squarefree primitive algebraic divisor-word sector in arbitrary middle dimension. The prescription uses the prescribed target's rational periods against independently produced actual line-bundle Koszul sources, an INTEGER Gram inverse, and finite direct sums/shifts; it does NOT assume a Hodge-to-K₀ preimage for alpha.

**Exact finite graph audit:** enumerate all noncrossing matchings, construct the integer source-to-monomial matrix, form the signed Gram using complementary middle monomials, then count alternating cycle components for every ordered matching pair. For m=1,2,3,4,5 (respectively 1,2,5,14,42 matchings), the independently computed identity \(|G_{MN}|=2^{c(M,N)}\) had **ZERO mismatches over all** 1+4+25+196+1764=1990 matrix entries. This computation checks the general graph proof, rather than establishing it through sampling.

**Geometric scope:** on a nonsplit Weil-type abelian fourfold with NS_Q=Qθ, these elliptic factor line bundles are not present. Thus even a complete squarefree divisor-product span cannot be asserted to provide every exceptional Weil Hodge class. The all-X program must still obtain an independently algebraic perfect complex beyond existing divisor products, e.g. a genuinely exotic sheaf/Hilbert/CM construction on the original nonsplit X. This is the specific geometric source-growth obligation; the alpha-selected K₀ and Gram compiler then produces explicit original-X cycles.

## 5. Current work products

- Lean: GSTUniversalResolvedSupportHodge.lean, existing module edited to add both source families and all-m square-zero algebraic laws; both source-module GitHub Actions [#39165331470](https://github.com/kyo-oo/HC-PROOF/actions/runs/39165331470) and pinned full integration [#39165331316](https://github.com/kyo-oo/HC-PROOF/actions/runs/39165331316) **completed successfully** at Lean commit 497e751bcfb4694fb1d8cc9bf4e0aa68eb5308d7.
- Calculation: Wolfram exact fourfold pairing and inverse Gram; deterministic finite-field rank check for m=1..5; rational exact determinants for m<=4.
- Hodge/Chow type gate: The genuine perfect complexes and their actual Chow Chern classes are mathematical original-X constructions, while the **Lean** all-m code operates at the exact rational squarefree intersection-algebra interface. The canonical Betti realization on arbitrary schemes is still a separate geometric input, and the conjecture for all X,p,alpha is not inferred from this source subfamily.
