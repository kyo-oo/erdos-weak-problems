# Mathbox — actual geometric Lefschetz primitive orbit and nonzero-period detector

- **Date:** 2026-10-19
- **Kind:** direct all-rank mathematical theorem, original-scheme geometry discrimination, exact Wolfram test
- **Program:** GST Hodge Gate 3, all-original-X geometric primitive source construction
- **Base checkpoint:** `046eacc2c0df9c78173ce9f12304ddfbf5af1223` on `research/gpt6-native-point-primitive-span-20261017`
- **Target:** every rational primitive (p,p) Hodge class on any smooth projective complex X must admit a genuine native codimension-p Chow representative, with the true canonical Betti class. Auxiliary operator identities do not replace this requirement.
- **Input theorem family:** `GSTClassicalHodgeRankFreeLefschetzPoincareGeneration`, `GSTClassicalHodgeGlobalSheetSaturation`, `GSTClassicalHodgeGeometricKrylovMomentDeterminant`, `GSTUniversalResolvedSupportHodge`.
- **Live Lean file edited in place:** `GSTClassicalHodgeRankFreeLefschetzPoincareGeneration.lean`.
- **Lean receipts:** [GST Geometric Lefschetz Primitive Rank #39219585896](https://github.com/kyo-oo/HC-PROOF/actions/runs/39219585896) **SUCCESS** for revision `84f8c6cf0050a551d93be8e19ff47e77833aa9ae`; [#39220270089](https://github.com/kyo-oo/HC-PROOF/actions/runs/39220270089) **SUCCESS** for `25a8925492d17200f1aeda5251584831b1c80a1b`.

## 1. All-rank geometric no-rotation theorem

The existing GST two-slot word compiler constructs every abstract Hodge-basis matrix unit by **coordinate localization**. That is rigorous as rational linear algebra. Its unproved additional step is realizing the chosen coordinate embedding as an ACTUAL algebraic correspondence on arbitrary X.

For a middle primitive vector v on a polarized smooth projective complex 2p-fold (p≥1), actual cup-L and its true Kähler adjoint Lambda annihilate v. If L(v)=Lambda(v)=0, every nonempty word W(L,Lambda) kills v and every finite rational linear combination of words satisfies

\[
  A(L,\Lambda)v \in \mathbb{Q}\,v.
\]

Lean theorems in the existing rank-free GST file:

- `geometricLPWord_nonempty_kills_joint_primitive`
- `geometricLPFiniteCombination_mem_source_line`
- `geometricLPFiniteCombination_cannot_hit_missing_direction`

All are stated in ANY rational module with two endomorphisms; interpreting them as genuine geometric L/Lambda requires the actual graded total cohomology, not the artificial GST two-coordinate model. These theorems DO NOT refute the abstract two-slot identities. They show that identifying their matrices with bare genuine L/Lambda words, without geometric source-specific localization, is impossible in primitive multiplicity >1.

## 2. All-rank projective-degree moment blindness

Suppose an actual rational endomorphism T preserves ker(L), and the degree functional is `trace=ell∘L`. This factorization holds for primitive middle (p,p) cohomology with p≥1: projective degree is integration against h^p, so ell integrates against h^(p-1).

Then for every n≥0,

\[
 L(T^n v)=0,\qquad \mathrm{trace}(T^n v)=0,
\]

and the full projective-degree Hankel matrix is **exactly the zero matrix at EVERY rank**:

\[
  H^{\mathrm{deg}}_{ij}=\mathrm{trace}(T^{i+j}v)=0.
\]

This is true even when `v,Tv,T²v,...` span a high-dimensional genuine algebraic primitive subspace. Therefore **positive degree of initial effective point cycles cannot serve as the moment functional for primitive target detection** after primitive normalization. Required replacement: rational primitive intersection pairing with a separately constructed nonzero primitive cycle.

Lean theorems (same existing file):
- `geometricPrimitiveOrbit_stays_primitive`
- `geometricPrimitiveOrbit_degree_trace_zero`
- `geometricPrimitiveDegreeHankel_eq_zero`

## 3. Positive route: actual algebraic primitive-mixing correspondence

The right extra geometric operation is a correspondence capable of mixing independent primitive directions. Wolfram exact-arithmetic computation uses genuine Chow ring of X=(P¹)^4:

\[
 \mathbb{Q}[a,b,c,d]/(a^2,b^2,c^2,d^2),\quad \int_X abcd=1.
\]

Set u=a+b, v=c+d, h=a+b+c+d and genuine algebraic classes

\[
 P=u^2-uv+v^2,\qquad Q=(a-b)(c-d).
\]

Both are Lefschetz-primitive, hP=hQ=0; both are in the kernel of genuine lowering Lambda. They are independent, with polarized intersection matrix diag(12,4).

A GENUINE ALGEBRAIC AUTOMORPHISM swapping the second and third P¹ factors induces the rational action

\[
  T(P)=-\tfrac12P+\tfrac32Q,\qquad
  T(Q)=\tfrac12P+\tfrac12Q
\]
and therefore

\[
 [T]_{P,Q}=\begin{pmatrix}-1/2&1/2\\3/2&1/2\end{pmatrix},
 \quad T^2=I, \quad T^T \operatorname{diag}(12,4)T=\operatorname{diag}(12,4).
\]

Thus ONE ACTUAL primitive source P and ONE ACTUAL primitive-mixing algebraic correspondence T produce the full two-dimensional primitive sector. The two-point Hankel matrix for the GENUINE PRIMITIVE intersection detector q(x)=∫P x is

\[
 H^{\mathrm{prim}}=\begin{pmatrix}12&-6\\-6&12\end{pmatrix},
 \quad \det(H^{\mathrm{prim}})=108\neq0.
\]

But projective-degree moments q_deg(T^k P)=∫h² T^kP vanish for k=0..4 and all k by the general primitive theorem. Its Hankel determinant is exactly zero. Wolfram independently verified: primitive dimension 2, cup and lowering vanish on both P,Q, polarization isometry True, primitive Krylov rank 2, determinant 108, degree Hankel determinant 0.

**This is a positive source-correspondence construction on that concrete original X, NOT a proof that any arbitrary X admits such a primitive-mixing correspondence or primitive seed.**

## 4. Mathematical disposition and exact universal residual

- **Proved (Lean kernel):** formal all-rank geometric raising/lowering joint-kernel no-rotation; every-rank projective-degree Hankel zero on an invariant primitive kernel; source-span obstruction. No `sorryAx` in the checked revision's new declarations.
- **Verified finite example (Wolfram exact rational):** genuine factor-swap automorphism produces independent primitive orbit with positive polarized Hankel determinant 108; ordinary degree Hankel is zero.
- **Not proved:** for every X and every nonzero rational primitive Hodge residual alpha orthogonal to known algebraic sources, independently construct a native geometric primitive source Z with Q(alpha,Z) != 0, or a genuine correspondence with an existing source whose primitive orbit reaches alpha. For an X having no known primitive Chow source, even the positive rank-2 construction above cannot start.
- **Gate 1:** the abstract supplied `H.cycleClass` still must be authenticated as canonical rational Betti fundamental class.
- **Gate 3:** remains open. The crucial false shortcut is treating formal two-slot "Lefschetz" matrices or positive projective-degree moments as genuine source-generating operators on unknown primitive Hodge directions.
- **Next high-impact route:** geometric incidence/Hilbert/closed-correspondence birth, with genuine primitive polarization readout, on the SAME original X. It must produce a new source independent of the old algebraic image, not merely apply a degree-preserving operator to a known ambient hyperplane class.
- **Outcome:** proved necessary operator restriction and a concrete valid nontrivial algebraic workaround on an explicit original variety; unconditional all-X conjecture unestablished. **Route stays open.**
