# GST cross-polarization K₀ birth and first-Chern Todd cancellation

- **Date:** 2026-10-19 (IST)
- **Kind:** bounded geometric source-construction attempt and kernel theorem
- **Base checkpoint:** `b6ed3ad55e40aaed1d3d5eed8de7ce1aeab14a18`
- **Current Lean module:** `GSTUniversalResolvedSupportHodge.lean`
- **Goal:** independently construct original-X native algebraic classes with nonzero primitive projection, without supplying a Chow representative of a prescribed rational Hodge class.
- **Evidence:** exact ring/K₀ identities committed and GitHub Actions checked at revision-matched source; scheme-level higher-codimension Betti realization not claimed by those identities.

## A. Correct two-polarization source and type discipline

For an actual finite-flat projection (f:X\to\mathbb P^n), take (R=K_0(\mathbb P^n)_\mathbb Q), (M=K_0(X)_\mathbb Q), (u_f=f_*[\mathcal O_X]), and (u_f^{-1}\in R). The projective projection formula makes (M) an (R)-module through (f^*), with (f_*) and (f^*) (R)-linear in this selected action. Define

\[
P_f(E)=E-f^*(u_f^{-1} f_* E).
\]

The exact Lean additions prove:
1. (P_f(f^* a)=0) for all (a\in R);
2. (P_f(E)=0\iff E\in\operatorname{im}(f^*));
3. (f_*P_f(g^*a)=0) and (P_f(g^*a)\ne0) whenever an independently constructed second-polarization source (g^*a) is outside the (f^*)-image.

**Important corrected type:** (g^*:R\to M) is **not** generally (R)-linear under the (f^*)-module action. Requiring it to be so would suppress the intended transverse geometry. The Lean statement deliberately uses `pullG : R → M` without false linearity; actual (g^*) must still be geometrically instantiated. This correction is in commit `0bc8ea25e88db17f576090476057d50a8766f6ca`.

The all-X source is actual K₀ algebra when its inputs are actual finite maps and algebraic line bundles; the nonambient condition is a genuine geometric independence test, not an assumed nonzero pairing with a Hodge target. Its existence for every arbitrary primitive residual is **not** established.

## B. Exact degree-one GRR cancellation, no Todd shortcut

On the degree-at-most-one truncation of rational base K₀/Chow, write
\[
u_f=d+t,\qquad \operatorname{ch}(f_*L)=d+t+q,
\]
where (t) represents the relative-Todd correction, (q=f_*c_1(L)) in degree one, and (t^2=tq=0). Since (d\ne0),
\[
(d^{-1}-d^{-2}t)(d+t+q)=1+d^{-1}q.
\]
The full product differs from the RHS by precisely (-d^{-2}(t^2+tq)); hence nilpotence, not an unjustified assumption (\mathrm{Td}=1), provides the cancellation.

Therefore the degree-one Chern source, after the usual algebraic GRR interpretation, is
\[
c_1(P_f(L))=c_1(L)-\frac{1}{d}f^*f_*c_1(L).
\]
The Lean theorem `GSTNativeFiniteFlatToddBridge.first_chern_finite_flat_Todd_cancel` proves the ring identity for every commutative ring with unit inverse and the two explicit nilpotence conditions. The degree-one scheme GRR comparison is a separate standard geometric input not encoded into this abstract ring lemma.

## C. Independent actual original-X test: a quadric surface

Take (X=\mathbb P^1\times\mathbb P^1), with divisor classes (a,b) satisfying (a^2=b^2=0), (ab=1). Let (H=a+b), which is very ample; a suitable linear projection of the Segre quadric gives a finite flat (f:X\to\mathbb P^2) of degree (d=H^2=2).

A second geometric polarization gives (D=a+2b=c_1(\mathcal O(1,2))), realized by an actual algebraic line bundle. Its (f)-primitive trace-zero divisor is
\[
Z=P_f^{CH}(D)=D-\frac{D\cdot H}{H^2}H
=D-\tfrac32H=\tfrac12(b-a).
\]
Direct exact intersections give
\[
H\cdot Z=0,\qquad -Z^2=\tfrac12>0.
\]
Thus this second-polarization source creates a genuine nonzero primitive algebraic direction that the intrinsic tangent (c_1(T_X)=2H) does not provide under the (f)-projector: (P_f^{CH}c_1(T_X)=0).

The computation is exact, checked in Wolfram Language using intersection matrix `{{0,1},{1,0}}`, (H=(1,1)), (D=(1,2)), resulting in (d=2), coefficient (3/2), (Z=(-1/2,1/2)), primitive pairing zero, signed norm (1/2).

## D. Uniform codimension-one geometric statement

For a smooth projective (n)-fold with a finite flat (f:X\to\mathbb P^n), (H=f^*h), (d=H^n>0), and any independently constructed divisor (D), the actual Chow trace-zero divisor is
\[
D_{\mathrm{prim},f}=D-\frac{D\cdot H^{n-1}}{d}\,H.
\]
It is a genuine algebraic cycle on the original (X). It is nonzero in rational numerical cohomology when (D) is not numerically proportional to (H); its primitive signed polarization is governed by Hodge index. This supplies an all-X algebraic *constructor* with geometric input (D), not a universal source-detection theorem for all codimensions.

## E. Handoff checkpoint

- **What changed:** a precise cross-polarization source construction and a universal degree-one Todd cancellation algebra identity added to an existing GST Lean file; the (R)-linearity error for (g^*) was caught and corrected before treating it as genuine geometry.
- **First remaining implication:** independently produce analogous primitive-detecting native sheaves in higher codimension for an arbitrary prescribed residual (r_\alpha), prove (Q(r_\alpha,\operatorname{cl}Z)\ne0), and connect the exact output to the canonical original-X Betti class.
- **Scope:** nontrivial divisor source and general K₀ formal mechanism, not an all-Hodge-classes algebraicity assertion. No universal Hodge-surjectivity premise has been added.
- **Continuation:** test incidence/Hilbert perfect-complex sources that are not generated merely by divisors and finite-flat base pullbacks. Check both the GRR grade and residual coupling before attempting an all-X theorem.
