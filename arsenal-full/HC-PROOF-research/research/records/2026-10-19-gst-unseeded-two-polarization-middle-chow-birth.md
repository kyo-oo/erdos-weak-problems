# GST unseeded two-polarization middle Chow/K₀ source on non-product original varieties

- **Date:** 2026-10-19 (IST)
- **Kind:** constructive source theorem, computation and exact proof audit
- **Base checkpoint:** \`e419df5ff721518a3c47af062d6589d8771ba91b\`; source code extended at \`b608486401a87b1b364e1e2cfb7e221d5b2d762e\` and \`6e6d74ac0d23f6f2a450908435b6010e93ac46f5\`.
- **Goal:** produce actual algebraic middle primitive Chow sources with no pre-existing primitive seeds or supplied Hodge target preimage, in a geometric class broader than CM varieties, curve products or split roots.
- **Existing module strengthened:** \`GSTPrimitiveProductTowerStabilization.lean\`.
- **Mathematical evidence:** uniform proof in commutative Chow ring below; exact Wolfram checks for m=1,...,6; Lean kernel checks for all-m primitive factorization and fourfold norm. Scheme-level cycle-class/GRR comparisons and source surjectivity are **not** claimed by abstract ring-level Lean proof.

## Source on ORIGINAL X, including nonsplit finite covers

Let A and B be arbitrary smooth projective complex m-folds with ample divisor classes h_A and h_B. Let X be any smooth projective complex 2m-fold with a **finite surjective morphism** q:X→A×B of positive degree e. X need not be a product (e.g. a smooth finite branched cover).

Let
\[
u=q^*\operatorname{pr}_A^*h_A,\qquad v=q^*\operatorname{pr}_B^*h_B,\qquad H=u+v.
\]
These are actual algebraic divisor classes on X. Since u and v come from m-folds, \(u^{m+1}=v^{m+1}=0\) in the genuine rational Chow ring, and \(H=q^*(h_A+h_B)\) is ample because q is **finite**.

Define the explicit **unseeded** native codimension-m Chow class
\[
\boxed{P_m(u,v)=\sum_{k=0}^m (-1)^k u^{m-k}v^k\in CH^m(X)_\mathbb Q.}
\]
It does not assume either A or B has a primitive algebraic source; its only inputs are algebraic ample line bundles. Direct telescoping in the Chow ring gives
\[
H P_m=(u+v)\sum_{k=0}^m(-1)^k u^{m-k}v^k
=u^{m+1}-(-v)^{m+1}=0.
\]
Consequently P_m is **genuinely Lefschetz-primitive**, not merely in the kernel of the finite-flat Chow pushforward.

Squaring and using the same nilpotence, each monomial in P_m² vanishes unless its two indices sum to m. There are exactly m+1 surviving terms, all with sign (-1)^m:
\[
\boxed{P_m^2=(-1)^m(m+1)u^m v^m.}
\]
The projection formula for finite q gives the genuine positive integral
\[
\boxed{(-1)^m\int_X P_m^2=(m+1)e
\left(\int_A h_A^m\right)\!
\left(\int_B h_B^m\right)>0.}
\]
Therefore \(P_m\ne0\) on the original nonsplit X, in every m≥1 for this class of geometries.

## Actual perfect-complex realization without Hodge preimages

Choose algebraic line bundles L_u,L_v on X with first Chern classes u,v. Define their augmentation classes \(a=[L_u]-[\mathcal O_X]\), \(b=[L_v]-[\mathcal O_X]\) in K₀(X). Then the **explicit integral virtual algebraic perfect-complex source**
\[
\mathcal E_m=\sum_{k=0}^m (-1)^k a^{m-k}b^k
\]
is an algebraic K₀ class, not a numerical replacement or a selected Chow preimage. Because \(\operatorname{ch}(a)=e^u-1\) starts in degree one, \(\operatorname{ch}(b)=e^v-1\) also starts in degree one. Thus
\[
\operatorname{ch}_j(\mathcal E_m)=0\ (j<m),\qquad
\operatorname{ch}_m(\mathcal E_m)=P_m(u,v).
\]
The leading Chern/Todd purity mechanism is formalized separately in \`GSTUniversalResolvedSupportHodge.lean\` at \`e419df5\`; that existing Lean machinery works with graded rational source coefficients and must still be instantiated with the actual Chow/K₀ ring and canonical Betti comparison for the complete geometric bridge.

## Decisive fourfold test, and a false shortcut identified

For X=(P¹)^4, let a,b,c,d denote the four actual fiber hyperplane classes, each square-zero, and set u=a+b, v=c+d, H=u+v.

A naive finite-flat trace-zero correction of the independent algebraic codim-two class ab is
\[
T=ab-\tfrac1{12}H^2.
\]
It has zero projective trace \(\int_X T H^2=0\), but
\[
HT=\tfrac12(abc+abd-acd-bcd)\ne0.
\]
Thus **trace zero is NOT the same as middle Lefschetz primitiveness**; any universality argument conflating the two requires correction.

The constructed true primitive normalization is
\[
Z=\tfrac16P_2(u,v)
=\frac{ab+cd}{2}-\frac{H^2}{12}.
\]
It satisfies \(HZ=0\) and \(\int_X Z^2=1/3\). Exact Wolfram polynomial reduction modulo \((a^2,b^2,c^2,d^2)\) independently checked these expressions.

For m=2 in arbitrary commutative ring with \(u^3=v^3=0\), Lean formalizes
\[
P_2=u^2-uv+v^2,\qquad (u+v)P_2=0,\qquad P_2^2=3u^2v^2.
\]
The subsequent theorem proves P₂≠0 whenever \(3u^2v^2\ne0\). For m=1,...,6, Wolfram exact reduction modulo \((u^{m+1},v^{m+1})\) yielded \(P_m^2=(-1)^m(m+1)u^mv^m\), agreeing with the general term-counting proof above. These finite checks validate signs but are NOT the proof of the general identity.

## Gate-3 placement and next step

- **Proved mathematically for the stated geometry:** genuine original-X primitive algebraic classes from two independently constructed ample divisors on any smooth finite cover of A×B; exact signed nonzero intersection and explicit algebraic K₀ source.
- **Lean scope:** ring-level arbitrary-m primitive factorization, nilpotence, and m=2 norm/nonzero law, with revision-matched GitHub Actions evidence; does not encode arbitrary scheme q, Chow ring or canonical Betti map as fully instantiated objects.
- **First missing implication for full Hodge:** for a prescribed residual \(r_\alpha\) on an *arbitrary* smooth projective original X, independently construct a genuine algebraic Y, L_i, or corresponding incidence operator whose canonical primitive class pairs nontrivially with \(r_\alpha\). Generic X need not have any finite map to A×B; this construction does not assume it exists universally.
- **Continuations:** combine the unseeded primitive factorization with the all-codimension incidence/Koszul source construction on X; inspect coherent sheaf incidence families or birational modified geometries with *verified original-X Gysin descent*. The finite cover source is a proof-of-mechanism, not a new final target.
