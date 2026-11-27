# GST triadic geometric source birth via the original CM operator algebra

**Date:** 2026-11-13  
**Research base:** `kyo-oo/HC-PROOF`, `research/gpt6-native-point-primitive-span-20261017` at `d79d96bdf85dd32dd1f2024feca9dfa3ec943fac`.  
**Evidence status:** a valid, all-codimension algebraic source construction on affine quadrics and primitive projective returns; universal `NativeGSTSingleFoldOrbitLaw` NOT proven. Classical Bott/Clifford geometry instantiated by the owner's original CM generators; no historical originality asserted.

## 1. Original owner graph and exact geometric extension

The existing `GSTGraphV2OmniversalCore.lean` specifies three sectors (`null`, `altMinus`, `gstPlus`) and typed events on an unconstrained carrier. `GSTGraphV2OmniversalHyperEvents.lean` allows rules with arbitrary premise types. `GSTGraphV2SelfExpandingCosmology.lean` permits actual birth of geometrically different worlds. This theorem specifies **a new geometrically certified instance** of a hyper-event; it does not redefine the graph, identify ALT with any particular matrix, or assume `allHodgeFromSources`.

The owner's actual CM pair is

\[
J=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\quad M=\begin{pmatrix}0&0\\0&2\end{pmatrix},\quad C=[J,M]=\begin{pmatrix}0&2\\2&0\end{pmatrix}.
\]

Over the complex algebraic ground field set
\[
\sigma_1=C/2,\qquad \sigma_2=-iJ,\qquad \sigma_3=I-M.
\]
These are precisely the three Pauli matrices and satisfy \(\sigma_i\sigma_j+\sigma_j\sigma_i=2\delta_{ij}I\). The scalar \(i\) is in \(\mathbb C\); this is a geometric representation, not a declaration that an arbitrary rational Betti endomorphism is algebraic.

## 2. Theorem: actual algebraic idempotent and source in *every* codimension

For \(p\ge1\) put
\[
R_p=\mathbb C[x_1,\ldots,x_{2p+1}]/(x_1^2+\cdots+x_{2p+1}^2-1),\quad Q_{2p}=\operatorname{Spec}R_p.
\]

Define \(2^p\times2^p\) matrices
\[
\Gamma_{2j-1}=\sigma_3^{\otimes(j-1)}\otimes\sigma_1\otimes I^{\otimes(p-j)},\quad
\Gamma_{2j}=\sigma_3^{\otimes(j-1)}\otimes\sigma_2\otimes I^{\otimes(p-j)},\quad
\Gamma_{2p+1}=\sigma_3^{\otimes p}.
\]
Then the Clifford anticommutator relations imply
\[
S_p=\sum_{j=1}^{2p+1}x_j\Gamma_j,\qquad
S_p^2=I,\qquad
\boxed{e_p=(I+S_p)/2,\quad e_p^2=e_p.}
\]

Thus the image of \(e_p\in M_{2^p}(R_p)\) is a **genuine algebraic vector bundle** \(E_p\) of rank \(2^{p-1}\), not an assumed cycle preimage. The algebraic Grassmann connection \(\nabla=e_pd\) has curvature \(F=e_p(de_p)^2\).

On the real sphere \(S^{2p}\subset Q_{2p}(\mathbb C)\), the Clifford trace identity gives
\[
\operatorname{Tr}(e_p(de_p)^{2p})=\frac{(2p)!i^p}{2^{p+1}}\Omega_{2p},
\]
where \(\Omega_{2p}=\sum_{j=1}^{2p+1}(-1)^{j-1}x_j dx_1\wedge\cdots\widehat{dx_j}\cdots\wedge dx_{2p+1}\) is the unit-sphere volume form. Since
\[
\operatorname{vol}S^{2p}=\frac{2^{2p+1}\pi^p p!}{(2p)!},
\]
we obtain the exact normalized Chern–Weil charge
\[
\boxed{\int_{S^{2p}}\operatorname{ch}_p(E_p)=
\int_{S^{2p}}\frac{1}{p!(2\pi i)^p}\operatorname{Tr}(e_p(de_p)^{2p})=1.}
\]

Hence \(\operatorname{ch}_p(E_p)\ne0\) in \(H^{2p}(Q_{2p},\mathbb Q)\). It is represented by a true rational algebraic codimension-\(p\) cycle through the algebraic Chern character. Its nonzero detector \(\ell_p(v)=\int_{S^{2p}}v\) **constructively fulfills the nonzero-detector condition** of the owner's existing abstract `arbitrary_world_birth_constructs_fresh_native_direction` for this family, relative to the previously available free-module sources (whose positive Chern components vanish).

The identities hold for **all** \(p\) by the displayed Clifford and sphere-volume formulas. Wolfram and an independent SymPy implementation checked the exact matrices, ranks, idempotent identities and normalized charges at \(p=1,2,3\):

| \(p\) | matrix size | rank of \(E_p\) | trace coefficient at north | charge |
|---:|---:|---:|---:|---:|
|1|2|1|\(i/2\)|1|
|2|4|2|\(-3\)|1|
|3|8|4|\(-45i\)|1|

This is a classical Bott-type construction realized through the specific GST CM algebra, **not** a claim of a new historical proof of Bott periodicity.

## 3. Genuine projective original-world return and higher primitive birth

The affine quadric has a smooth projective compactification \(\overline Q_{2p}\subset\mathbb P^{2p+1}\) given by \(\sum X_j^2=X_0^2\). The chart \(X_0\ne0\) is \(Q_{2p}\). Any rational Chow representative \(Z_p\in CH^p(Q_{2p})_\mathbb Q\) of \(\operatorname{ch}_p(E_p)\) has a cycle closure \(\overline Z_p\in CH^p(\overline Q_{2p})_\mathbb Q\). Its canonical Betti class restricts to the nonzero source on the affine open.

But the projective hyperplane class \(h=c_1(\mathcal O(1))\) restricts to zero on that chart, since \(X_0\) trivializes \(\mathcal O(1)\) there. Thus \([\overline Z_p]\notin\mathbb Q h^p\) in the projective middle cohomology. The latter is rank two and algebraic by classical even-quadric intersection theory. Therefore the closure and \(h^p\) span all middle rational Hodge classes of that projective quadric. Subtracting a rational hyperplane multiple yields a nonzero primitive algebraic cycle (primitive in canonical Betti cohomology). **No Schubert cycle was supplied as input.** This completes birth + exact nonzero detection + original projective-world return in every codimension \(p\) for this explicitly constructed quadric family.

## 4. A strict arbitrary-smooth-affine K-theory source vocabulary

For any smooth affine \(U=\operatorname{Spec}R\), finitely generated projective modules correspond to global regular matrix idempotents \(e\in M_n(R)\). Grothendieck–Riemann–Roch/Chern character over the rationals identifies \(K_0(U)\otimes\mathbb Q\cong\bigoplus_p CH^p(U)\otimes\mathbb Q\). Thus every **already algebraic** codimension-\(p\) class can be constructed using finitely many idempotents and rational coefficients. This proves that the proposed NULL-idempotent source vocabulary is **expressively complete for algebraic classes** on any affine world, but NOT that every rational Hodge class is algebraic.

An exact finite polynomial source certificate for a prescribed class \(\beta\in H^{2p}(U,\mathbb Q)\) is a collection \((e_a,q_a,\eta)\), with regular polynomial-matrix idempotents, rational coefficients, and a global algebraic \((2p-1)\)-form, satisfying
\[
\boxed{e_a^2=e_a,\qquad
\omega_\beta-\sum_a \frac{q_a}{p!}\operatorname{Tr}[e_a(de_a)^{2p}]=d\eta.}
\]
Here \(\omega_\beta\) is chosen with the correct algebraic de Rham/Betti normalization. On a smooth affine variety global algebraic differential forms compute de Rham cohomology. Existence of a solution is equivalent to algebraicity of \(\beta\); it is **not** implied by graph closure or a supplied `allHodgeFromSources` field. The successful quadric construction is a nontrivial exact witness for one of these systems.

## 5. Exact counterexample to a universal *single* Bott birth

Let \(X=(\mathbb P^1)^4\), choose a smooth divisor \(D\) of type \((1,1,1,1)\), and let \(U=X\setminus D\), which is smooth affine. Write \(h_i\) for the four hyperplane classes and choose the **already algebraic** class \(\beta=(h_1-h_2)|_U\). Its square is \(-2h_1h_2|_U\), which is NONZERO: weak Lefschetz identifies \(H^2(D)\cong H^2(X)\), so the kernel of \(H^4(X)\to H^4(U)\) is the span of \(D\cdot h_j\). The exact six-by-four Gysin matrix has rank 4, while adjoining the coefficient column for \(-2h_1h_2\) has rank 5. This was recomputed in Wolfram and SymPy.

For any algebraic \(f:U\to Q_2\), the square of the Bott pullback \(f^*\operatorname{ch}_1(E_1)\) is zero because \(H^4(Q_2,\mathbb Q)=0\). Thus \(\beta\) is **not** such a single pullback. This is a real counterexample to the overstrong universal-one-quadric claim, not to GST, and supports use of the owner's genuine arbitrary-arity hyper-events and many-source synthesis.

Moreover any map from a connected projective complex variety to the affine \(Q_{2p}\) is constant, so a direct affine Bott pullback cannot work on arbitrary original projective \(X\). One must use an affine complement, a genuine nontrivial cross-world construction and an algebraic return.

## 6. Failure of transfinite polynomial corrections without algebraic exactness

A tempting limit-stage algorithm is \(f(t)=3t^2-2t^3\), which squares the idempotence defect:
\[
\boxed{f(t)^2-f(t)=-(t^2-t)^2(3-2t)(2t+1).}
\]
Over \(\mathbb Q[t]\), starting from \(t\), the \(n\)th finite iterate has degree \(3^n\), and none is an idempotent: polynomial domains only have scalar idempotents 0,1. An inverse-limit idempotent in a suitable completion is **not necessarily an algebraic idempotent in \(R\)**. The new Clifford construction succeeds precisely because it satisfies an *exact polynomial relation already in R*, avoiding an ungrounded transfinite step.

## 7. The universal GST target and correct evidence classification

For arbitrary original smooth projective \(X\), codimension \(p\), prescribed rational \((p,p)\) class \(\alpha\), the active open theorem remains the existence of an **alpha-sensitive genuine nonsplit algebraic birth**, canonical original-X return, and a realized one-seed cyclic correspondence. A general smooth ample affine complement \(U=X\setminus D\) can return classes to \(X\) once an actual affine representative of \(j^*\alpha\) and a boundary correction are constructed; the universal affine polynomial-idempotent solver has not been found. No change to `NativeGSTSingleFoldOrbitLaw` or existing Lean theorems is asserted. This mathematical work is a proved *realization* of one class of original GST world-birth events and supplies a detector in all codimensions; it is not the universal GST hypothesis proof.

**References:** Weibel, *The K-book*, Corollary II.8.9.1; Stacks Project, Lemma 50.21.3 (algebraic de Rham Chern character); Stacks Project, Chow rational equivalence/localization; standard identification of complex affine quadrics with cotangent bundles of spheres. Exact local checker: `GST_20261113_CM_Bott_NULL_affine_exact.py`. No new Lean CI is claimed.