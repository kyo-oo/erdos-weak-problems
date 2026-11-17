# Mathbox — every-original-X affine localization and primitive source frontier

**Date:** 2026-10-18.  
**Pinned base:** `e69156eb04d3278f857183acdc93c413632f08dd`, branch `research/gpt6-native-point-primitive-span-20261017`.  
**Formal development:** `GSTUniversalResolvedSupportHodge.lean`, commit `ab3bbb4135051d42f5eb435d5172af5e05191af4`.  
**Kernel receipt:** [GitHub Actions #39100222168](https://github.com/kyo-oo/HC-PROOF/actions/runs/39100222168), success, full pinned GST Hodge integration including the new theorem declarations and no-sorryAx check.  
**Original goal (UNCHANGED):** for every smooth projective complex variety X, every p and every rational (p,p) class alpha, construct a genuine rational codimension-p algebraic cycle on the ORIGINAL X with canonical Betti class alpha.

## The actual all-X calculation and its scope

Fix a smooth projective complex n-fold X, a smooth ample divisor Y and $U=X\setminus Y$, with $j:U\to X$ and $i:Y\to X$. Take rational cohomology, genuine canonical geometric maps and a rational Hodge class alpha of degree 2p. The ordinary Gysin localization exact sequence includes

\[
H^{2p-2}(Y,\mathbb Q)(-1)\xrightarrow{i_*}
H^{2p}(X,\mathbb Q)\xrightarrow{j^*}
H^{2p}(U,\mathbb Q).
\]

This is geometrical topology and is **not** a surjectivity hypothesis for algebraic cycles.

**Upper-half vanishing.** When 2p>n, the smooth affine n-fold U has the homotopy type of a real CW complex of dimension at most n (Andreotti–Frankel), so H^(2p)(U,Q)=0. Thus every rational Hodge alpha has a rational Hodge preimage beta on the divisor Y under i_*, by strictness of pure Hodge-structure morphisms. If the strictly lower-codimension beta has a *genuine* Chow representative D, then i_*D is the required original-X cycle. The newly proved Lean theorem `affine_boundary_vanishing_constructs_original_hodge_cycle` uses **zero affine native source** in the existing exact Chow/Betti successor formula; no unknown algebraization on U is assumed.

Iterate through a Bertini-smooth ample flag X=X_0 ⊃ X_1 ⊃ ... ⊃ X_k, with

\[
k=2p-n>0,\qquad n_i=n-i,\qquad p_i=p-i.
\]

At all prior levels i<k, 2p_i>n_i, so every step has vanishing open cohomology. At the terminal level, 2p_k=n_k. Consequently any upper-half rational Hodge class on X is the Gysin of some **middle rational Hodge class** on the smooth projective variety X_k of dimension 2(n-p). Representing that single middle class algebraically gives an explicit composite algebraic Gysin cycle on the ORIGINAL X. It is not claimed that the terminal middle class is automatically algebraic.

For p=n-1 and n≥2, X_k is a smooth projective surface and p_k=1; Lefschetz (1,1) does construct its divisor, giving the familiar genuine all-X near-top cycle case. For p=n the terminal degree is zero and the fundamental zero-codimension source gives the top 0-cycle case. These are established classical geometry, and the new Lean theorem kernel-checks the precise source-free one-step native cycle assembly rather than claiming to formalize the complete analytic topology/flag.

**Lower-half and middle affine survival.** When $1\le p$ and $2p\le n$, weak Lefschetz makes i^*:H^(2p-2)(X)→H^(2p-2)(Y) an isomorphism (in the relevant nonnegative degree). The projection formula gives ker(j^*)=L H^(2p-2)(X), where L is cup with the ample class. The rational Lefschetz decomposition gives

\[
H^{2p}(X,\mathbb Q)
 = P^{2p}(X,\mathbb Q)\oplus L H^{2p-2}(X,\mathbb Q),
\]

so the restriction of j^* to the rational primitive part P^(2p)(X) is **injective**. This includes the exact difficult *middle* case 2p=n. The Lean theorems `middle_primitive_affine_restriction_injective` and `nonzero_middle_primitive_has_nonzero_affine_restriction` prove this rational-linear implication for arbitrary X and p from named genuine Betti-localization and primitive-direct-sum comparison data. They do **not** yet instantiate all geometric comparison laws from native Mathlib structures.

**Sharp genuine middle example, not a missing Hodge class.** For a smooth cubic fourfold X containing an algebraic plane P, the true canonical intersection matrix for h² and [P] is [[3,1],[1,3]]. The algebraic primitive class alpha=3[P]-h² has alpha·h²=0 and alpha²=24>0. On a smooth hyperplane Y, im(i_*H²(Y))=Q h², hence j^*alpha≠0. Wolfram computed the exact Gram contraction as `{24,0,8,2,True}`, the final True checking preservation of the degree defect 2p-n along a flag; the Gram rank and determinant are 2 and 8. This is an algebraic example exposing the nonvanishing at the critical middle, **not** evidence against Hodge.

## Why the actual universal primitive generator is still missing

The previous affine-successor GST theorem already gives an explicit original-X cycle

\[
Z_X=\overline{Z_U}+i_*D_Y
\]

provided Z_U in CH^p(U)_Q has canonical class j^*alpha and D_Y corrects the supported boundary Hodge discrepancy. For middle primitive alpha, the new injection proves j^*alpha is generally NONZERO, and the source-free choice Z_U=0 provably cannot work.

Thus the exact research target for all X, all 2p≤dim(X), and arbitrary primitive rational Hodge alpha is an actual **algebraic** affine source with

\[
\mathrm{cl}^{\mathrm{canonical}}_U(Z_U)=j^*\alpha.
\]

Equivalently, one may construct an algebraic K_0(U)_Q class whose degree-2p topological Chern character is the specified restriction (with lower-degree components controlled by Adams purification). Topological K^0 or a holomorphic Oka bundle is insufficient without a *new algebraization theorem*. The relevant class lies in the lowest mixed-Hodge weight W_(2p)H^(2p)(U), not in the arbitrary higher-weight topological K-theory of U. The existing torus counterexample to holomorphic-to-algebraic Picard does not decide this lowest-weight subproblem.

**Two routes executed this checkpoint; one source route remains open:**

1. **Upper-half geometric localization:** proved as a source-free Lean construction; sharply reduces high codimensions to middle on genuine projective hyperplane flags. Not a source-birth solution to middle primitive classes.
2. **Lower/middle hyperplane restriction:** proves nonzero primitive Hodge classes survive on U, ruling out universal boundary-only reconstruction; the cubic-fourfold Gram calculation is a concrete valid discriminator.
3. **Affine algebraic K_0 source birth (open; prior project evidence retained, no new construction proved in this checkpoint):** topological and Hodge-weight input is understood, but constructing a genuine algebraic vector bundle/projective module with the prescribed *projective-origin* degree-2p Chern character remains unproved. Neither existing GST polynomial projectors nor the new relative statements produce such a bundle for arbitrary X,alpha.

**Adversarial verdict:** the all-varieties Hodge conjecture is **not proved**. Gate 3 is not closed. The successful kernel build is evidence for the stated conditional geometric maps and the rational-linear deduction, not for the unprovided universal affine algebraic source. The next decisive mathematical task is to build a prescribed-projective-origin algebraic K_0/Chow source on U from independently constructed affine geometry, *without assuming its Chern character equals the requested Hodge class*. A complete proof must then instantiate canonical Betti comparisons and verify the exact final all-X statement without extra surjectivity assumptions.

**No local Lean installation. No internet search.** GitHub Actions is the Lean compiler; Wolfram arithmetic checks are exact finite/symbolic validation, not a universal existence argument.
