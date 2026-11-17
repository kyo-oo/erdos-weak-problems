# Prescribed-residual source construction: spectral candidate tested directly

**Work package:** `GST-PRESCRIBED-RESIDUAL-SPECTRAL-SOURCE-20261020`.  
**Base:** `782f4c9d180836afed481c477a8a4cb52eaec4d6`.  
**Target:** for every prescribed original X and nonzero rational primitive Hodge residual r, construct an actual algebraic bundle E with a nonzero ch_p period against r, then apply the already established smooth-center constructor.  
**Outcome:** the residual-defined spectral bundle below exists algebraically but fails the required period test. The universal source construction is **not proved**. No new Lean helper theorem, added source-existence hypothesis, Hodge counterexample, or universal no-go is claimed.

This is a direct construction attempt, not another extension of the [bundle-to-center conversion](2026-10-20-original-x-smooth-incidence-center-construction.md). The prior conversion remains unchanged.

## 1. Build the bundle from r itself

Use the balanced Weil-type abelian-fourfold chart already in the research program. Translation-invariant holomorphic forms trivialize

\[
 \Omega_A^2\simeq O_A^{\oplus6}.
\]

The real Weil form, expressed in complex coordinates compatible with the opposite K embeddings in the last two slots, is a nonzero scalar multiple of

\[
 r=z_1z_2\bar z_3\bar z_4+z_3z_4\bar z_1\bar z_2.
\]

It defines a Hermitian symbol by the top coefficient of r wedge z_I wedge bar(z_J), for ordered pairs I,J in (12,13,14,23,24,34). Normalize the harmless nonzero scalar so that its matrix is

\[
 M=E_{1,6}+E_{6,1},\quad M^3=M.
\]

The code derives this matrix independently by exterior multiplication of the displayed Hodge tensor. The spectral projectors are actual constant algebraic bundle endomorphisms

\[
 P_+=(M^2+M)/2,\qquad P_-=(M^2-M)/2,\qquad P_0=I-M^2.
\]

Their ranks are 1,1,4; they are pairwise orthogonal idempotents whose sum is I. They provide a genuine nonzero target-sensitive matrix detector:

\[
 \operatorname{Tr}\bigl(M(P_+-P_-)\bigr)=2.
\]

Thus this proposal constructs an algebraic object **from the prescribed Hodge tensor**, without taking a detecting bundle as an input.

## 2. Test the actual native Chern class

The positive and negative image bundles have explicit global nowhere-zero frames e_12+e_34 and e_12-e_34. Both are trivial line bundles. P_0 has the other four constant frames. Hence

\[
 E_+\simeq O_A,\quad E_-\simeq O_A,\quad E_0\simeq O_A^{\oplus4},
 \qquad \operatorname{ch}_{>0}(E_i)=0.
\]

In particular [E_+]-[E_-]=0 in actual algebraic K0 even though the matrix detector is nonzero. Matrix eigenvalue labels have not produced a higher native Chern class.

Twisting an image bundle of rank a by the polarization line L^k gives

\[
 \operatorname{ch}_2(E_i\otimes L^k)=\tfrac12a k^2\theta^2,
 \qquad c_2(E_i\otimes L^k)=\binom a2 k^2\theta^2.
\]

The actual primitive Weil class satisfies r theta=0, so both source periods vanish. The exact real exterior calculation independently gives

\[
 \int_A r^2=8,\qquad\int_A\theta^4=24,\qquad r\theta=0.
\]

The target is nonzero and has positive primitive norm. This is therefore a failure of the proposed constructor on a valid nonzero target, not a test on the zero class.

The conclusion holds for any finite word of constant spectral matrices and termwise constant idempotents on these trivial bundles: their images are constant subspaces, hence trivial bundles. Adding polarization powers keeps their Chern characters in Q[theta]. Arbitrary finite fiber multiplicity does not alter this calculation. This statement does not cover nonparallel geometric correspondences or arbitrary homotopy idempotents in a derived category.

## 3. Test a nonconstant evaluation-kernel continuation

One possible repair is to select a subspace V of H0(L^k) using the residual symbol, then use its evaluation kernel M_V. When the evaluation is basepoint-free, its actual exact sequence is

\[
 0\longrightarrow M_V\longrightarrow V\otimes O_A
       \longrightarrow L^k\longrightarrow0.
\]

It follows that [M_V]=dim(V)[O_A]-[L^k], so its primitive ch_2 period is again zero. This conclusion is independent of the matrix used to select V.

A rank-changing evaluation with a nonempty base locus can leave this exact sequence, but then the additional cycle class comes from that actual base-locus geometry. Nothing computed here proves that a residual-selected subspace has the necessary nonambient base-locus component. That continuation remains open; it is not silently excluded by the basepoint-free calculation.

## 4. Preserve the topological class: exact integrability check

The alternative of starting with the topological K-class carrying a multiple of r retains the desired characteristic class, but requires an algebraic/holomorphic realization. Hodge type of the characteristic classes alone does not prove integrability of a chosen Dolbeault operator.

A direct local test is N=[[0,1],[0,0]], A^(0,1)=N bar(z_1)dbar(z_2). Then

\[
 \bar\partial A+A\wedge A=N\,d\bar z_1\wedge d\bar z_2\ne0,
 \qquad \operatorname{Tr}(N^j)=0\quad(j\ge1).
\]

The latter assertion follows from Tr(N)=0 and N^2=0, not from a finite sample. A bump-supported version globalizes this example on a trivial smooth bundle in a coordinate patch of a projective variety of complex dimension at least two. Its Chern-character traces vanish while that chosen Dolbeault operator is nonintegrable.

This does **not** say that the trivial bundle admits no integrable structure; it plainly does. It checks only the proposed implication from cancellation of trace/Chern obstructions to integrability of the chosen structure. It supplies no obstruction to all possible realizations of the prescribed r.

## 5. Research disposition and verification

The matrix-to-eigenbundle construction and its basepoint-free evaluation-kernel continuation fail the requested native period test in the stated scope. The universal goal remains open. The topological-class route still needs a genuine Hodge-sensitive algebraic realization; the rank-changing incidence continuation still needs a constructed component with computed nonzero r-period. Neither is assumed as a new theorem.

No Lean source was changed in this attempt. The surviving construction must be proved before adding it to the source-birth interface. Existing green center-conversion files are not evidence for universal source existence.

- [Exact executable test](../computations/gst_residual_defined_spectral_source_attempt.py).
- [Recorded output](../computations/gst_residual_defined_spectral_source_attempt.output.json).
- [Version-2 computation manifest](../computations/gst_residual_defined_spectral_source_attempt.manifest.json).

The executable uses rational matrices and an independently constructed eight-generator exterior algebra. It checks all nine spectral-projector products, derives M from the Hodge tensor, checks the nonzero residual norm and polarization orientation, tests 36 rank/twist combinations and 24 basepoint-free evaluation-kernel twists, and checks the trace-nilpotent calculation. The all-word and all-power statements above have the stated structural proofs; the finite checks do not replace them. Review provenance is adversarial self-review; no subagents, public web search or local Lean installation were used.
