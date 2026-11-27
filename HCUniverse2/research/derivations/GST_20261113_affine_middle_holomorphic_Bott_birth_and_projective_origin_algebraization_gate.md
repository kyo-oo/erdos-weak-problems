# GST Clifford source birth on all affine middle cohomology: complete topological/holomorphic construction and exact algebraization boundary

**Date:** 2026-11-13. **Evidence:** universal mathematical theorem for topological/holomorphic sources on smooth affine complex middle-dimensional worlds; explicit algebraic counterexample to upgrading all such sources automatically. The GST universal original-projective source-birth hypothesis is not proved.

## Theorem A: all affine middle-degree targets admit an alpha-sensitive holomorphic Clifford source

Let \(U\) be a smooth affine complex algebraic variety of **complex dimension \(2p\)**, \(p\ge1\), and let \(\beta\in H^{2p}(U,\mathbb Z)\). The Andreotti–Frankel–Milnor theorem states that \(U(\mathbb C)\), being Stein of complex dimension \(2p\), has the homotopy type of a CW complex of **real dimension at most \(2p\)**. The sphere \(S^{2p}\) is \((2p-1)\)-connected, so obstruction theory gives a surjective (indeed bijective in the CW-dimension range) degree/class map
\[
[U,S^{2p}]\longrightarrow H^{2p}(U,\mathbb Z),\qquad [f]\mapsto f^*\iota,
\]
where \(\iota\) is the integral generator of \(H^{2p}(S^{2p},\mathbb Z)\). Choose a continuous map \(f_0:U\to S^{2p}\) representing \(\beta\), compose with the inclusion of the real sphere into the complex affine quadric
\[
Q_{2p}=\left\{\sum_{j=1}^{2p+1}x_j^2=1\right\}\subset\mathbb A^{2p+1}_\mathbb C,
\]
and obtain a continuous map \(f:U\to Q_{2p}(\mathbb C)\).

The complex manifold \(Q_{2p}(\mathbb C)\) is a complex homogeneous space of an orthogonal group, hence is Oka. By the Oka principle, \(f\) is homotopic to a **holomorphic** map \(F:U\to Q_{2p}(\mathbb C)\).

Use the algebraic Clifford–CM bundle \(E_p\to Q_{2p}\) constructed from the owner's original \(J,M,[J,M]\), whose normalized degree-\(2p\) Chern-character generator \(\eta_p\) satisfies \(\int_{S^{2p}}\eta_p=1\). Its pullback \(\mathcal V_\beta=F^*E_p\) is now a **genuine holomorphic** vector bundle on the original affine world U, and by naturality and homotopy invariance
\[
\boxed{\operatorname{ch}_p^{Betti}(\mathcal V_\beta)=\beta\quad\text{in }H^{2p}(U,\mathbb Q).}
\]
Thus the construction reaches every integral \(\beta\) (and every rational class after clearing denominators and taking rational K-theory linear combinations). It does **not** need the Hodge condition: it is a topological/analytic theorem for all middle cohomology, and does NOT assume a pre-existing algebraic cycle.

**GST interpretation:** the owner graph allows a new affine world with the original CM operator algebra and an alpha-sensitive topological/homotopy event, followed by a holomorphic realization. This legitimately fulfills the *topological source birth*, *complex/holomorphic gluing*, and *canonical Betti equality* portions of the long-sought triadic law for every affine U of middle dimension. It does not claim that the resultant holomorphic map or bundle is algebraic.

## Theorem B: the analytic-to-algebraic step fails for arbitrary affine input

Take \(U=(\mathbb C^*)^2\), a smooth affine complex surface. Topologically \(U\simeq T^2\), so \(H^2(U,\mathbb Z)\cong\mathbb Z\) has a nonzero generator \(\beta\). By Theorem A there exists a holomorphic map \(F:U\to Q_2(\mathbb C)\) whose Clifford/Bott line bundle pullback has \(c_1(F^*E_1)=\beta\ne0\).

However \(U=\operatorname{Spec}\mathbb C[x^{\pm1},y^{\pm1}]\). This Laurent-polynomial coordinate ring is a regular UFD, so \(\operatorname{Pic}_{alg}(U)=0\); every algebraic line bundle is trivial and has vanishing first Betti Chern class. Therefore **no algebraic morphism** \(g:U\to Q_2\) is homotopic to \(F\) (otherwise \(g^*E_1\) would be an algebraic line bundle with nonzero first Chern class). This is a concrete rigorous counterexample to replacing the analytic source by an algebraic one through a general algebraic-Oka or approximation assertion.

The counterexample is **not** a counterexample to the original projective Hodge conjecture: the class \(\beta\) on \((\mathbb C^*)^2\) is a non-projective-origin mixed-Hodge class of weight 4, not a pullback of a rational pure \((1,1)\) class from a smooth projective compactification. The exact GST target permits only the projective-origin Hodge inputs; that extra structure is essential to a viable restricted algebraization theorem.

## The right upgraded GST law (still open)

For each original smooth projective complex \(X\), codim \(p\), and prescribed rational Hodge \(\alpha\), use an affine complement or a genuine typed GST world-birth to reach an affine world \(U\) of complex dimension \(2p\), with a cohomology return detecting the appropriate class \(\beta\). Theorem A constructs an explicit alpha-sensitive holomorphic map \(F_\beta:U\to Q_{2p}\) whose Clifford projector has the required **topological** Chern class.

The exact missing theorem is a *projective-origin restricted algebraization* rule: in the relevant geometry, replace this holomorphic map by a regular algebraic map or construct an algebraic projector with the same canonical class, without assuming a Chow representative of \(\beta\). This rule must use actual owner +GST/ALT−/NULL certified geometry, and it cannot be justified by the ordinary Oka principle, arbitrary-arity graph closure, or polynomial approximation alone. A further boundary return and true realized one-fold certificate are still required in the exact owner Lean target.

**Impact:** the source existence burden has been reduced from 'invent a cycle from a Hodge class' to an explicit and geometrically typed **holomorphic-to-algebraic lift of a known Clifford projector** for projective-origin classes. Topological and holomorphic birth are now unconditional in the affine middle degree; the algebraic step is a demonstrably nontrivial independent theorem.

**Literature inputs:** Andreotti–Frankel–Milnor CW dimension theorem for smooth affines; Oka principle for complex homogeneous spaces; algebraic K0/Chern theory of the prior derivation; counterexample from Laurent-polynomial factoriality and \(H^2(T^2,\mathbb Z)=\mathbb Z\). Cross-check: Asok–Fasel, *Algebraic vs. topological vector bundles on spheres* (2014) notes non-surjectivity of algebraic-to-topological vector-bundle realization on certain affine varieties; Lárusson–Truong (2019) distinguishes analytic and algebraic Oka properties. No new Lean kernel theorem or CI verification is claimed.