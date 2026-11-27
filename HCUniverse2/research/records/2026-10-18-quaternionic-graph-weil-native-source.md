# Mathbox — quaternionic graph constructs exceptional Weil algebraic classes beyond CM elliptic powers

**Date:** 2026-10-18. **Single active program:** the exact all-varieties rational Hodge conjecture, all p and prescribed rational (p,p) alpha with canonical original-X Betti equality. **Single current geometric test:** move from split CM elliptic-power Weil sources to a **genuinely quaternionic Weil abelian fourfold** without assuming a cycle preimage.

## The original geometric source, not an algebraic Hodge preimage hypothesis

Use the rational *indefinite division quaternion algebra*
\[
 D=(-1,3)_{\mathbb Q}=
 \mathbb Q\langle i,j:i^2=-1,\ j^2=3,\ ji=-ij\rangle.
\]
It is division because \(3\notin N_{\mathbb Q(i)/\mathbb Q}(\mathbb Q(i)^\times)\), equivalently 3 is not a sum of two rational squares. It splits at the real place, as the quaternion signs are one negative and one positive. Standard quaternionic Shimura-curve geometry gives polarized complex abelian surfaces \(B\) with an order in \(D\) acting by genuine algebraic endomorphisms. Choose an order containing i,j, or clear denominators of the rational endomorphism j. For a general such QM surface B, B is simple, so it is not isogenous to the elliptic square \(E^2\). Because the algebraic automorphism j anti-commutes with i, its action on H¹ exchanges the sigma and bar-sigma Q(i) eigenspaces. It is an isogeny since \(j^2=3\,\mathrm{id}\).

Let \(A=B\times B\), with diagonal K=Q(i) action. The K action has Hodge signature **(2,2)**, hence A is a genuine Weil-type abelian fourfold, now **not isogenous to CM elliptic \(E^4\)**. The actual graph
\[
 \boxed{\Gamma_j=\{(b,jb):b\in B\}\subset A}
\]
is an irreducible **algebraic codimension-two subvariety** of the original A. Its cohomology class is generated without choosing a Weil/Hodge target preimage. If j was replaced by an integer multiple, the graph-top-wedge pairing below is scaled by a nonzero integer square and stays nonzero.

## Exact rational H¹ and graph-top-wedge computation

On the rational 4-dimensional H¹ of a QM surface, choose a basis for the regular D-module. The two actual rational endomorphism matrices are
\[
 I=\begin{pmatrix}
 0&-1&0&0\\1&0&0&0\\0&0&0&-1\\0&0&1&0
 \end{pmatrix},
\quad
 J=\begin{pmatrix}
 0&0&3&0\\0&0&0&-3\\1&0&0&0\\0&-1&0&0
 \end{pmatrix}.
\]
Exact matrix arithmetic gives \(I^2=-1\), \(J^2=3\), \(IJ+JI=0\). Thus in \(H^1(B,\mathbb C)\) the eigen-subspace of I with eigenvalue \(+i\) has complex dimension two. Choose its explicit basis
\[
 u_1=(0,0,i,1)^\top,\qquad u_2=(i,1,0,0)^\top.
\]
The \(+i\)-eigenspace of \(H^1(A,\mathbb C)\) has dimension four. Pullback along the genuine graph \(\Gamma_j\hookrightarrow A\) sends a basis of this K-eigenspace to the four forms \((u_1,u_2,Ju_1,Ju_2)\) on \(B\). Their top exterior determinant is
\[
 \boxed{\det[u_1,u_2,Ju_1,Ju_2]=-12\ne0.}
\]
The conjugate Weil eigenline is also nonzero by conjugation. Since the pairing of the graph's Betti fundamental class with the top K-eigenspace is nonzero, the **actual algebraic graph class has a nonzero projection into the two-dimensional rational Weil (2,2) subspace**. This is the missing positive geometric source for this quaternionic original fourfold.

GSTCMQuadraticNativeRankForcing and the kernel-verified all-rational-target CM one-source reconstruction now apply directly. In fact the actual \(f=[2+i]\) has two distinct nonreal-conjugate eigenvalues on the Weil space; \(\Pi_W[\Gamma_j]\) and \(f^*\Pi_W[\Gamma_j]\) are rationally independent algebraic classes. The explicit inverse 2×2 CM orbit matrix from GSTUniversalCMArithmeticObstruction constructs a rational combination for **every prescribed rational class in the Weil subspace of this very A**. No rank-two source premise was supplied: the graph made the first source.

## All positive codimensions without reverting to elliptic-only sources

For \(p=2m+\varepsilon\ge2\), \(m=\lfloor p/2\rfloor\ge1\), \(\varepsilon\in\{0,1\}\), take \(B\) above and a CM elliptic curve \(E\) with K action. Define
\[
 A_p=(B^m\times E^{\varepsilon})\times(B^m\times E^{\varepsilon})
\]
with diagonal K on the B blocks, opposite K actions on the two E blocks, and product polarization. It has complex dimension 2p, K signature (p,p), and retains a **genuine quaternionic factor**. Let the graph map between the two p-dimensional factors be the product of the anti-K isogeny \(j^m\) on B blocks and identity on the oppositely K-labelled E block. This is an actual codimension-p algebraic graph cycle. Its pullback of the top sigma exterior form has determinant (up to basis permutation sign)
\[
 \boxed{\Delta_p=(-12)^m(2i)^{\varepsilon}\ne0,\quad
          |\Delta_p|^2=144^m 4^\varepsilon>0.}
\]
Hence this explicit graph is a nonzero algebraic Weil source for every p≥2; the same *verified* CM orbit arithmetic spans the entire rational Weil space on these A_p. This extends the source beyond elliptic powers in **every codimension**, without switching the Gate-3 problem.

The constructed A_p are generally **decomposable and not very general/simple** Weil-type abelian varieties. This is a deliberate boundary: it is a new nonsplit-elliptic original-X family, **not** a claim that the universal Hodge theorem or even all very-general Weil cases are solved.

## Independent exact certificates and formal scope

- **Wolfram** verified the two explicit rational 4×4 quaternion matrices, their squares, anti-commutator, the \(+i\) eigenvectors, the graph-top-wedge determinant −12, and the odd-p elliptic determinant \(2i\), with exact product values p=2,...,8.
- **GitHub exact polynomial/linear-algebra audit:** \`research/computations/quaternionic_graph_weil_source.py\` verifies all these relations with Gaussian-integer exact arithmetic and the uniform product norm for p=2,...,12; no floating point or nondeterministic sampling.
- **Lean:** \`GSTUniversalCMArithmeticObstruction.lean\` now contains \`quaternionicAntiKGraphSwitchesEigensector\`, \`quaternionicAntiKGraphNonzero\`, and \`quaternionicGraphWeilTensorNormNonzero\` with no new axiom or source selector. These formally handle anti-K eigenspace exchange, isogeny nonvanishing, and exact all-p tensor nonzero. Geometry of a polarized QM surface, the graph fundamental class, and the Hodge exterior wedge comparison are **standard mathematical inputs described above, not yet kernel-instantiated in a full abelian-variety Betti implementation**.
- [Exact pinned GST Hodge integration CI](https://github.com/kyo-oo/HC-PROOF/actions/runs/39063843544) is the associated source-commit run. Read the final CI status and logs before promoting this theorem to GREEN.

## The one continuing original-X construction problem

The original all-\(X,p,\alpha\) problem is unchanged. The new graph source covers a meaningful **non-elliptic quaternionic Weil** family in all p; it does NOT establish the existence of a detected codimension-p cycle on an arbitrary *simple* Weil-type A or arbitrary X. The immediate unsolved test within the same Weil branch remains constructing such a source on a very general simple Weil-type fourfold, where neither QM product graphs nor extra split elliptic graph divisors are available. A complete all-X proof must then also move beyond Weil varieties. Do not substitute a green arithmetic rank theorem or a cohomological projector for that geometric existence step.
