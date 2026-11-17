# GST uniform 2d+2 dimensional rational middle-source world

- **Date:** 2026-10-20
- **Result:** dimension-controlled strengthening of [the indexed single-world all-codimension defect theorem](2026-10-20-gst-single-rational-world-middle-defect-compression.md).
- **Source:** [LaTeX complete derivation](../derivations/GST_rational_middle_blowup_uniform_Segre_2026-10-20.tex).
- **Lean arithmetic:** `GSTGraphV2SelfExpandingCosmology.lean`, `dimension_bounded_middle_rational_blowup_channel` at `26152981a971e04db39f96b8a445ca4eebf3f6b3`.
- **CI:** Graph #39464493690 and pinned Hodge integration #39464493771 triggered at `26152981` (check completed outcome separately). Prior middle-channel and 4-channel inverse at `92b8324` are GREEN in Graph #39463484355 and pinned #39463484304.

## Geometric construction with a dimension bound

Let X be any smooth projective complex d-fold (no prescribed X family or Hodge-class preimage).

By embedding X initially into large projective space and projecting generally away from the secant/tangent locus of dimension ≤2d+1, X admits a closed embedding in P^(2d+2). If already embedded into smaller projective space, include linearly. This requires only ordinary projective geometry, not a Hodge surjectivity condition.

Blow up this `P^(2d+2)` along X and set Y=Bl_X(P^(2d+2)). Then **Y is smooth projective rational, has complex dimension exactly 2d+2, and has normal center codimension c=d+2**. For ALL original codimensions p=0,...,d, the exceptional channel i=d+1−p is valid in {1,...,d+1}; the Hodge class

\[
\beta_p=j_*(\xi^{d-p}q^*\alpha_p)\in\mathrm{Hdg}^{d+1}(Y)_\mathbb Q
\]

is a genuine rational middle Hodge class for arbitrary original rational Hodge alpha_p.

The normal Chern and Segre convolution yields the **exact** original-X Chow retraction

\[
\boxed{
\mathcal R_p(W)=
-\sum_{k=0}^{p}c_k(N_{X/P^{2d+2}})
q_*(\xi^{p-k}j^*W)
\in CH^p(X)_\mathbb Q.}
\]

The class is algebraic on X if and only if beta_p is algebraic on Y. Hence one selected **single** smooth rational variety Y captures all original Hodge defects in its middle grade:

\[
\boxed{
D_{d+1}(Y)\cong\bigoplus_{p=0}^{d}D_p(X),\quad
D_p(X)=\mathrm{Hdg}^p(X)_\mathbb Q/
\mathrm{im}(cl_X^p).}
\]

The usual genuine algebraic zero/point, rational (1,1) divisor and Hard Lefschetz arguments vanish D0,D1,D_(d−1),Dd, so for d≥4 only original p from2 through d−2 remain. For d≤3 the middle defect of this Y is zero.

## Mathematical importance and limits

This removes the embedding dimension and arbitrary target codimension from the family of geometry targets: for every original d-fold all rational Hodge targets can be compressed into one rational (2d+2)-fold and its unique middle grade d+1. The same actual Chow/Betti projector returns any independently constructed middle algebraic representative. It is a proved geometric reduction, not a proof that such middle cycles exist. Rationality of Y does NOT force middle Hodge algebraicity.

The special GST source-birth target is therefore exact: on this explicit Y, construct the canonical middle exceptional source beta_p without assuming an algebraic preimage of alpha_p. If that is accomplished for all beta_p then the explicit corrected return closes every original grade. Full scheme-level Lean realization of the blowup Chow/Hodge isomorphisms remains a distinct acceptance gate; the current Lean declaration verifies the dimension/index arithmetic only.
