# GST source-response criterion, algebraic single-fold synthesis, and exact Hankel certificate

**Date:** 2026-11-13  
**Original branch:** `research/gpt6-native-point-primitive-span-20261017` after `bd821e56baf40934d24abe9b8d7e4c1937e122c9`.  
**Status:** two general algebraic theorems fully proved, with explicit hypotheses; no universal GST source-birth theorem or Lean CI claimed. This record is an upgrade to the mathematical *compiler* and the owner's source-sensing theorem, not a proof of the universal Hodge conjecture.

## Theorem A — a scalar, target-sensitive GST birth response is enough

Let \(X/\mathbb C\) be a smooth connected projective variety, \(p\) a codimension and \(W_p(X)=H^{2p}(X,\mathbb Q)\cap H^{p,p}(X)\). Fix an ample class \(h\). The rational Lefschetz decomposition and Hodge–Riemann bilinear relations give a rational **positive-definite** polarization \(B_p\) on \(W_p(X)\) (change signs on primitive Lefschetz pieces and sum the resulting definite forms). Let \(A_0\subset W_p(X)\) be the span of finitely many genuine algebraic cycle classes already constructed, with \(r=\dim A_0\) and \(n=\dim W_p(X)\).

Suppose the actual owner GST triadic world-birth system possesses the following **constructive response property** for every intermediate known-source subspace \(A\) obtained by adjoining actual born cycles and every nonzero \(\alpha\in A^{\perp_{B_p}}\):

> From the typed +GST/ALT−/NULL hyper-event inputs, construct an ACTUAL original-\(X\) rational algebraic cycle \(Z\) with independently verified \(B_p(\alpha,\operatorname{cl}_X(Z))\ne0\). Neither the cycle nor a target-cycle selector may be supplied as input.

Then there is a deterministic finite mathematical extraction of a complete original-X source basis after at most \(n-r\) successful births. Indeed, for any \(\alpha\ne0\in A^\perp\), a nonzero response to its detector implies \(\operatorname{cl}(Z)\notin A\). Replace \(A\) by \(A+\mathbb Q\operatorname{cl}(Z)\); its dimension increases by at least one. Iterate until the orthogonal complement is zero, which by positive-definiteness is equivalent to \(A=W_p(X)\). At every iteration the **birth obligation is only a nonzero scalar period**, not exact equality \(\operatorname{cl}(Z)=\alpha\).

The condition is still a substantive universal geometric-existence theorem, logically equivalent in total strength to rational Hodge algebraicity if demanded for every \(X,p\). It is not automatically implied by existing graph closure. It is, however, a strictly weaker **per-birth output specification** and is directly compatible with the owner's already-proved `arbitrary_world_birth_constructs_fresh_native_direction`: the new nonzero detector is precisely its `hNew` input. The preceding Clifford/Bott construction supplies this nonzero geometric detector **unconditionally** on affine quadrics in every codimension, demonstrating the mechanism can actually fire in real geometry.

## Theorem B — exact full-Chow one-fold synthesis and determinant, once the actual sources exist

Fix \(X\) of complex dimension \(d\) and codimension \(p\), and suppose the rational Hodge conjecture holds in codimensions \(p\) AND \(d-p\) on this original \(X\). Let \(n=\dim_\mathbb Q W_p(X)\). The rational Poincaré pairing between \(W_p(X)\) and \(W_{d-p}(X)\) is perfect. Choose actual algebraic cycles \(Z_0,\ldots,Z_{n-1}\in CH^p(X)_\mathbb Q\) spanning \(W_p\) and actual complementary dual cycles \(W_0,\ldots,W_{n-1}\in CH^{d-p}(X)_\mathbb Q\) satisfying
\[
\int_X\operatorname{cl}(Z_i)\smile\operatorname{cl}(W_j)=\delta_{ij}.
\]
These duals are rational algebraic combinations of complementary cycle sources (invert the rational intersection matrix). No higher-than-Hodge geometric cycles are silently inserted.

For \(n\ge1\) define the **actual codimension-\(d\) Chow correspondence** on \(X\times X\)
\[
\boxed{\Gamma=\sum_{j=0}^{n-2}\operatorname{pr}_1^*W_j\cdot\operatorname{pr}_2^*Z_{j+1}.}
\]
The standard proper push–pull correspondence action satisfies
\[
\Gamma_*\operatorname{cl}(Z_i)=\begin{cases}\operatorname{cl}(Z_{i+1}),&i<n-1,\\0,&i=n-1.\end{cases}
\]
Thus the single **genuine algebraic seed** \(Z_0\) and single **genuine algebraic correspondence** \(\Gamma\) have a cyclic orbit equal to the entire Hodge space. This is already a full mathematical construction, not a free linear-map selection.

Set the rational geometric detector \(\ell(\beta)=\int_X\beta\smile\operatorname{cl}(W_{n-1})\). Then its Hankel matrix is an exact anti-identity:
\[
H_{ij}=\ell(\Gamma_*^{i+j}\operatorname{cl}(Z_0))=\delta_{i+j,n-1},\quad 0\le i,j<n,
\]
so
\[
\boxed{\det H=(-1)^{n(n-1)/2}\ne0.}
\]
For \(n=0\), the zero seed and zero correspondence satisfy cyclicity on the zero Hodge fiber (the empty determinant is conventionally 1). For \(n=1\), choose \(\Gamma=0\) and the one nonzero seed, giving \(H=(1)\). Wolfram independently checked the exact anti-identity and determinant for all \(n=1,\ldots,12\); the displayed shift formula proves **every finite \(n\)**.

Therefore, in the category of all genuine Chow correspondences on an arbitrary smooth projective original \(X\), **universal rational Hodge algebraicity is equivalent to a genuine one-seed, one-fold cyclicity certificate**, and the full scalar Hankel-determinant condition can be met *explicitly* without independent simple-spectrum/eigenvalue/Gram hypotheses. Forward implication is the construction just given; reverse is the owner's existing canonical cycle-class preservation/orbit argument.

**API firewall:** the repository's current `RealizedFiniteClosedCorrespondence` requires finite fibers under the left projection. A rank-one term \(W_j\times Z_{j+1}\) typically has positive-dimensional fibers over the supporting \(W_j\) when \(0<p<d\); for example on \(X=\mathbb P^1\times\mathbb P^1\) with \(p=1\), its left fibers are curves. Thus the constructed \(\Gamma\) is not automatically a valid instance of that restricted Lean type. A full-Chow-correspondence realization type with a proved canonical push–pull square is required before treating this as a proof of the EXACT existing `NativeGSTSingleFoldOrbitLaw`; either actual finite-left-fiber reachability must be established, or a mathematically motivated additive full-Chow target must be formalized without silently replacing the old target.

## The remaining universal GST hit after these upgrades

The only *geometric-existence gap* for the full-Chow variant is now the prescribed-alpha **nonzero source-response event** of Theorem A on arbitrary original \(X\) for every residual Hodge direction. The intrinsic finite-dimensional source construction (basis, duals, one fold, one seed and nonzero Hankel determinant) is mathematically solved by Theorem B. The strict finite-fiber Lean interface is a separate formal-semantics issue, not an independently necessary open geometric theorem for general Chow correspondences.

**Executed checks:** exact Wolfram integer/rational shift-Hankel matrix for \(n=1\ldots12\); prior Clifford-idempotent geometric detector checks in codimension \(p=1,2,3\); no Lean files modified and no new Lean CI claims. This derivation is evidence that the graph's missing `hNew` detector can be weakened to one nonzero scalar per step, not a proof of universal `hNew` existence.