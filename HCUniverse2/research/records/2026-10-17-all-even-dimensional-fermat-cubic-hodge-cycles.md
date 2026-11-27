# Mathbox: complete primitive rational Hodge cycles on all even-dimensional Fermat cubics

## Statement — uniform geometric construction

For every integer n≥2, consider the smooth Fermat cubic hypersurface

\[
X_n=\bigl\{z_0^3+\cdots+z_{2n-1}^3=0\bigr\}
\subset\mathbb P_{\mathbb C}^{2n-1},
\qquad \dim_\mathbb C X_n=2n-2.
\]

**The rational middle Hodge classes are represented by rational algebraic cycles.** More precisely, every rational primitive \((n-1,n-1)\)-Hodge class is a rational linear combination of explicit maximal linear planes \(\mathbb P^{n-1}\subset X_n\), through the canonical Betti cycle-class map.

This is a full primitive-cycle construction across an **unbounded-dimensional original-variety family**. The research program's further target is the same construction on *every* smooth projective complex variety, with no Fermat hypothesis.

## 1. Concrete geometric source planes

Choose one of the \((2n-1)!!=(2n)!/(2^n n!)\) perfect matchings M of the 2n projective-coordinate indices. For each of its n pairs (a,b), choose \(\lambda_{(a,b)}=-\omega^{k_{(a,b)}}\), \(k\in\{0,1,2\}\), \(\omega^3=1\). The n linear equations

\[
z_b=-\omega^{k_{(a,b)}}z_a
\]

define a projective \((n-1)\)-plane \(P_{M,k}\subset X_n\), since every pair's cubic contributions cancel. The total number of displayed sources is \((2n-1)!!\,3^n\).

## 2. Exact intersection from projective geometry

Fix one matching and compare planes labeled \(a,b\in(\mathbb Z/3)^n\). Let c=#coordinates where a and b agree. Their scheme-theoretic intersection is \(\mathbb P^{c-1}\) for c≥1, and empty for c=0.

The excess normal-bundle formula and the cubic equation give

\[
[P_a]\cdot[P_b]
=[t^{c-1}]\frac{(1+t)^c}{1+3t}
=\sum_{j=0}^{c-1}(-2)^j
=\frac{1-(-2)^c}{3},
\]

including 0 when c=0. At c=n this is the self-intersection \(c_{n-1}(N_{P/X})\). This equality is the *canonical geometric intersection product* of the source planes, with excess intersections included.

Thus the matching's actual intersection matrix is convolution by

\[
K(g)=\frac{1-\prod_{j=1}^n f(g_j)}{3},\qquad
f(0)=-2,\quad f(1)=f(2)=1.
\]

## 3. Fourier spectrum — a uniform exact proof

Fourier-transform K on the finite abelian group \(A=(\mathbb Z/3)^n\). For a frequency \(\chi=(\chi_1,\dots,\chi_n)\in A\),

\[
\widehat f(0)=0,\qquad
\widehat f(1)=\widehat f(2)=-3.
\]

Therefore

\[
\boxed{
\widehat K(\chi)=
\begin{cases}
3^{n-1},&\chi=(0,\ldots,0),\\
(-1)^{n+1}3^{n-1},&\chi_j\in\{1,2\}\ \text{for all }j,\\
0,&\text{otherwise}.
\end{cases}}
\]

Every all-nonzero frequency has a nonzero eigenvalue, and there are \(2^n\) such frequencies. Hence one matching contributes \(2^n\) independent primitive algebraic Hodge directions plus one hyperplane direction, for **every n**.

For each nontrivial all-nonzero character, form the explicit Fourier orbit-cycle
\[
V_\chi=\sum_{a\in A}\chi(a)[P_{M,a}]\in
CH^{n-1}(X_n)\otimes_{\mathbb Q}\mathbb Q(\omega).
\]
The Fourier Gram identity yields
\[
V_\chi\cdot V_{-\chi}=(-1)^{n+1}3^{2n-1}\ne0.
\]
It follows that the canonical Betti class \(\mathrm{cl}(V_\chi)\) is nonzero and belongs to its stated diagonal-automorphism eigenspace.

## 4. Geometric matching covers EVERY primitive middle-Hodge character

The smooth Fermat cubic's Jacobian ring is

\[
R=\mathbb C[z_0,\dots,z_{2n-1}]/(z_0^2,\dots,z_{2n-1}^2).
\]

The classical equivariant residue description identifies \(H^{n-1,n-1}_{\mathrm{prim}}(X_n)\) with the degree-n piece \(R_n\), dimension \(\binom{2n}{n}\). Its one-dimensional diagonal \(\mu_3^{2n}/\mu_3\) characters have exponent vectors with **exactly n entries 1 and n entries 2**.

Take any such character. Pair each coordinate carrying exponent 1 with one carrying exponent 2. The resulting matching M realizes this character as one of the all-nonzero Fourier characters in step 3. The corresponding algebraic Fourier-cycle Vχ has a nonzero projection onto that one-dimensional middle-Hodge eigenspace.

Since **every** primitive middle-Hodge character admits such an opposite-color matching, the complete collection of actual maximal planes spans

\[
H_{\mathrm{prim}}^{n-1,n-1}(X_n).
\]

Its complex dimension is exactly \(\binom{2n}{n}\). Rationality follows because the originating plane classes lie in \(H^{2n-2}(X_n,\mathbb Q)\): the full complex span of rational algebraic vectors equals the entire complex Hodge sector, hence their rational span equals \(H^{2n-2}(X_n,\mathbb Q)\cap H^{n-1,n-1}(X_n)\) on the primitive component.

## 5. Explicit reconstruction for a rational primitive Hodge class

Choose for each middle character χ one matching Mχ from step 4 and its Fourier plane cycle Vχ. Characters χ and -χ form Galois pairs over \(\mathbb Q(\omega)\). For any rational primitive Hodge class α, its χ-coordinate is obtained from the canonical cup/intersection pairing:

\[
c_\chi(\alpha)=
\frac{\langle\alpha,\mathrm{cl}(V_{-\chi})\rangle}
{\langle\mathrm{cl}(V_\chi),\mathrm{cl}(V_{-\chi})\rangle}
=
\frac{\langle\alpha,\mathrm{cl}(V_{-\chi})\rangle}
{(-1)^{n+1}3^{2n-1}}\in\mathbb Q(\omega).
\]

Summing the algebraic orbit cycles with those coefficients and combining Galois-conjugate pairs gives **an actual rational algebraic codimension-(n-1) cycle** representing α. The hyperplane power \(h^{n-1}\) gives the remaining nonprimitive \((n-1,n-1)\) direction.

This source-to-target map is expressed entirely through explicit geometric planes, diagonal automorphism actions and canonical intersection measurements.

## Computation and formalization evidence

- [Exact 405-plane Fermat cubic fourfold](2026-10-17-fermat-cubic-405-full-hodge-span.md): dimension 4, actual 21-plane full Hodge basis, 20 primitive plane differences, determinants 27 and 81.
- \`research/computations/fermat_cubic_fourier_all_dimensions.py\` independently computes K's Fourier transform with exact integer pairs in \(\mathbb Z[\omega]\) and checks the one-matching rank in dimensions 2,4,6,8: 5,9,17,33. It verifies that all \(\binom{2n}{n}\) middle-color characters have opposite-color matchings in these ranges, with no floating-point arithmetic.
- The rank and matching conclusions for arbitrary n use the **symbolic factorization and explicit pairing proof above**, rather than inference from finite test cases.
- Uniform normal-Chern/discriminant identities already have Lean kernel checks in \`GSTMaximalLinearHypersurfacePrimitive.lean\`; the uniform **equivariant residue correspondence and Fourier eigenspace assembly** are verified here as classical mathematical arguments and remain targets for full Lean formalization.
- Python CI in \`.github/workflows/gst-fermat-cubic-405-rank.yml\` runs both bounded exact audits; record its finished action run.

## Original all-X research objective

The uniform Fermat construction demonstrates that the GST source-generation approach can attain complete rational primitive Hodge rank across arbitrary even dimensions on explicit original hypersurfaces. The remaining all-X geometric program must produce, for arbitrary smooth projective X, algebraic generators with equally complete canonical primitive measurements, or prove a dimension-preserving algebraic transfer that actually carries all rational primitive Hodge characters to X.

## 6. Every codimension, and Fermat cubics of every dimension

The primitive-middle result above upgrades to the **full rational Hodge conjecture for every smooth Fermat cubic hypersurface in every complex dimension**, by ordinary weak/Hard Lefschetz and canonical hyperplane geometry.

Let \(\widetilde X=\{\sum_{i=0}^N z_i^3=0\}\subset\mathbb P^N\), of complex dimension \(D=N-1\). For any codimension p such that \(2p<D\), weak Lefschetz identifies \(H^{2p}(\widetilde X,\mathbb Q)\cong H^{2p}(\mathbb P^N,\mathbb Q)=\mathbb Q h^p\). For \(2p>D\), Hard Lefschetz and Poincaré duality yield the same rank-one algebraic line \(\mathbb Q h^p\). If D is odd, **every** even cohomological degree lies in one of those cases, so every rational Hodge class is already an algebraic hyperplane power.

If \(D=2n-2\) is even, the only further codimension is \(p=n-1\): the diagonal-character Fourier plane construction of steps 1–5 supplies the **complete primitive middle Hodge sector**, and \(h^{n-1}\) supplies the remaining Lefschetz line.

Therefore, for every dimension D and every admissible p, all rational (p,p) Hodge classes on the original smooth Fermat cubic \(\widetilde X\) are represented by concrete rational algebraic cycles. An explicit reconstruction uses hyperplane intersections outside middle degree and Fourier combinations of maximal planes in even middle degree.

This all-dim/all-codim extension uses standard Lefschetz theorems and the uniform Fourier/Griffiths construction; the all-varieties research target extends this source-producing mechanism beyond the Fermat family.
