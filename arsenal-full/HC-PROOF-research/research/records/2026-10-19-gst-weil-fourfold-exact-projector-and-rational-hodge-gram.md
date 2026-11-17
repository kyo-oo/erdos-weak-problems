# Mathbox GST — exact Weil fourfold rational classes and algebraic CM projector

- **Date:** 2026-10-19
- **Kind:** proof-grade symbolic derivation, exact numerical audit, original-X counterexample candidate
- **Program:** full rational Hodge conjecture Gate 3, falsification attempt
- **Base:** \`94348292e339c997cd8fb4f2342e2d5e112497af\` and preceding [zero-or-full counterexample record](2026-10-19-gst-rational-hodge-weil-counterexample-zero-or-full-test.md)
- **Live Lean edit:** \`GSTUniversalCMArithmeticObstruction.lean\`, code commit \`71c998d59ec692d89342fbd77b65aa27c27632f3\`; official [Pinned Hodge Geometric Integration #39235308461](https://github.com/kyo-oo/HC-PROOF/actions/runs/39235308461) **SUCCESS**
- **Goal:** find or rule out an ACTUAL rational \((2,2)\) Hodge class not in the canonical Chow class image of a smooth projective complex fourfold. This computation alone does not produce a counterexample.

## A. Explicit rational Hodge candidates, not merely formal named Hodge sheets

Consider a genuine Weil-type abelian fourfold \(A\), \(K=\mathbf Q(i)\), with balanced signature (2,2). In a \(K\)-basis for the eight-dimensional rational \(H^1(A,\mathbf Q)\), let \(e_j,f_j\) (j=1..4) satisfy \(J e_j=f_j,\ Jf_j=-e_j\). The pure K-eigen wedge
\[
  \Omega=\bigwedge_{j=1}^4(e_j+i f_j)
\]
has Hodge type (2,2) because the relevant K-eigen H1 sector contains two (1,0) and two (0,1) dimensions. Define the two rational classes
\[
   W_R=\operatorname{Re}\Omega,\qquad W_I=\operatorname{Im}\Omega.
\]
Their 16-term expansion has rational \(\pm1,0\) coefficients in \(\bigwedge^4 H^1(A,\mathbf Q)\); both are rational canonical cohomology classes and are primitive for any K-compatible ample (1,1) class because wedging a full K-eigen fourth exterior power with a mixed (1,1) polarization forces five vectors in a four-dimensional K-eigenspace.

**Independent exact Wolfram computation.** The rational 16-coordinate vectors obtained from the ordered wedge of \((e_j+if_j)\) have rank 2. With exterior-volume orientation \(e_1\wedge e_2\wedge e_3\wedge e_4\wedge f_1\wedge f_2\wedge f_3\wedge f_4\), a direct exterior sign/inversion count gives
\[
 Q(W_R,W_R)=8,\quad Q(W_I,W_I)=8,\quad Q(W_R,W_I)=0,
 \quad \det Q|_{W}=64.
\]
Equivalently \(\Omega^2=0,\ \Omega\overline\Omega=16\mathrm{vol}\). Each real/imag part has eight nonzero monomials. These are genuine explicit rational Hodge candidate classes; their algebraic/nonalgebraic status is not decided by the intersection computation.

## B. Actual K-isogeny and exact rational polynomial projector

The algebraic isogeny \(f=[2+i]\) acts on the two K-pure fourth exterior powers with eigenvalues \((2+i)^4=-7+24i\) and \((2-i)^4=-7-24i\). Its degree-four cohomology spectrum has rational factors
\[
  G_W(t)=t^2+14t+625,\quad
  G_{\mathrm{mixed}}(t)=t^2-30t+625,\quad
  G_{\mathrm{ambient}}(t)=t-25.
\]
An independently computed Chinese-remainder projector is
\[
\boxed{
 P_W(t)=-
 \frac{(t-25)(39t-79)(t^2-30t+625)}{44\,000\,000}.
}
\]
It satisfies
\[
 P_W\equiv1\pmod{G_W},\quad
 P_W\equiv0\pmod{G_{\rm mixed}},\quad
 P_W(25)=0,\quad
 P_W^2\equiv P_W\pmod{G_WG_{\rm mixed}(t-25)}.
\]

**Exact all-rank algebraic verification in existing Lean module:**
- \`cmWeilTwoPlusIProjectorScalar\`
- \`cmWeilTwoPlusIProjector_fixes_Weil\`
- \`cmWeilTwoPlusIProjector_kills_mixed\`
- \`cmWeilTwoPlusIProjector_kills_ambient\`
- \`cmWeilTwoPlusIProjector_idempotent_on_spectrum\`.

The key integer polynomial identity is
\[
 (t-25)(39t-79)(t^2-30t+625)+44\,000\,000
 =(t^2+14t+625)(39t^2-2770t+72375).
\]

The actual operator \(P_W(f^*)\) is an algebraic rational correspondence on \(A\times A\) because it is a finite \(\mathbf Q\)-linear combination of pullbacks by iterates of the genuine isogeny f, represented by transpose graphs. A scheme/canonical-Betti functoriality instance is needed to interpret the scalar Lean polynomial as such a correspondence; the operator is NOT a one-sided algebraic cycle representing an arbitrary prescribed Weil Hodge class.

## C. The zero-or-full falsification criterion

For the canonical algebraic Chow image \(S = P_W\,\mathrm{cl}_A(CH^2(A)_\mathbf Q)\subset W_\mathbf Q\), the existing algebraic isogeny preserves S. The kernel-proved \`cmWeilStableSourceDichotomy\` says \(S=0\) or \(S=W_\mathbf Q\), since the companion action
\[
 T(x,y)=(-625y,x-14y),\qquad
 \det[z,Tz]=(x-7y)^2+576y^2>0
\]
for z≠0 has irreducible minimal polynomial \(t^2+14t+625\).

A single explicitly constructed algebraic surface Y with \(P_W\operatorname{cl}_A[Y]\ne0\) would force the full Weil plane to be algebraic by the genuine CM-isogeny orbit. Conversely a genuine proof that \(P_W\operatorname{cl}_A[Y]=0\) for **every algebraic surface Y on one actual A** would yield a rational Hodge counterexample, e.g. \(W_R\).

This is an all-surface statement. NS rank 1 and the absence of projected polarization products establish vanishing only for the divisor-generated subalgebra. The framework's tangent/Adams/divisor source channels are insufficient by themselves; all coherent/incidence/Hilbert/perfect-complex native sources must be considered before any nonalgebraicity claim.

## D. Reproduction and careful evidence boundaries

Two independently structured exact Wolfram calculations were run, using the stateless \`mcp__Wolfram__WolframLanguageEvaluator\`:
1. A fourfold Kronecker product of \(\bigl(\begin{smallmatrix}2&-1\\1&2\end{smallmatrix}\bigr)\) on 16 selected rational exterior monomials yielded a 2×2 matrix \(\bigl(\begin{smallmatrix}-7&-24\\24&-7\end{smallmatrix}\bigr)\), rank 2 of the rational frame and eigenpower \((2-i)^4=-7-24i\).
2. Independent orientation-aware exterior multiplication, multiplying the explicit 16 monomials and counting the inversions needed to sort eight indices, yielded Gram diag(8,8), cross 0, \(\Omega^2=0\), \(\Omega\overline\Omega=16\). The 2×2 companion calculation gave charpoly and irreducibility as above.
3. Direct rational CRT solve for 5 polynomial coefficients gave \((-79/2816,\ 359/22000,\ -527/400000,\ 139/2750000,\ -39/44000000)\) and confirmed \((P^2-P)\bmod G_WG_{\rm mixed}(t-25)=0\).

The rational exterior arithmetic is computationally exact; realizing the chosen Hodge signature by a particular smooth projective abelian variety is genuine abelian geometry, and **absence of any algebraic surface** representing a Weil class is NOT established. This is a **counterexample candidate/test, not a rational Hodge counterexample**.

## E. Continuation

A decisive bounded next experiment must work at the level of actual canonical Chow classes: construct intrinsic Hilbert/incidence codimension-two surfaces or perfect complexes on a genuine generic Weil-type abelian A, apply the exact algebraic projector \(P_W(f^*)\), and compute their canonical Weil periods. A nonzero period proves the exceptional sector algebraic; proving the projector zero for every possible algebraic surface would disprove rational Hodge. Merely observing a zero output for finitely many tests does not settle the latter.
