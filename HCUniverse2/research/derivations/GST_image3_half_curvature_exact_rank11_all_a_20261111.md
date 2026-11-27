# GST Image-3 — exact rank ELEVEN at half-CM curvature, for every rational direct strength

Date: 2026-11-11.
Original operator family: \`F_(a,b)=U+J+a M+b[J,M]\`, with the
OWNER-ORIGINAL 4x3 shuffle U, signed CM mirror J, Wave-I SURVIVE
diagonal M, and original mixed seed \`v=e_(0,0)+e_(0,1)\`.
All arithmetic is exact over Q.

**Claim (native source):**

\[
\boxed{
\forall a\in\mathbb Q,\quad
\dim_{\mathbb Q}\operatorname{span}
\{v,F_{a,1/2}v,F_{a,1/2}^2v,\ldots\}=11.
}
\]

The previously established native Lean theorem
\`GSTImageThreeCurvatureResonance.resonanceOrbitSpan_ne_top\`
gave failure to span the 12-cell carrier. This derivation
identifies the exact loss: **ONE dimension, never two or more,
for ANY rational source coefficient a.**

## 1. Universal upper bound 11

Let \`t=(3,2)\` be the ORIGINAL maximum-information cell. The
source law already proved in Lean is

\[
(F_{a,b}u)(t)=(1+2a)u(t)+(2b-1)u(s),
\]

where \`s=(0,0)\` is the original null cell.

At \`b=1/2\`, the input coupling vanishes, leaving

\[
(F_{a,1/2}u)(t)=(1+2a)u(t).
\]

The original mixed seed has \`v(t)=0\`. Inductively every
\`F_{a,1/2}^n v\` has t-coordinate 0; so the rational span
is contained in the 11-dimensional hyperplane \`ker(eval_t)\`.
Thus its dimension is **at most 11** for every rational a.

## 2. Exact LOWER bound 11 via original 1+10 decomposition

Remove the maximum cell t. The remaining eleven original cells
form an invariant world subspace. The null cell s is now a
true eigencharacter of eigenvalue 1, and the remaining TEN
original N-cohomology wave cells carry a genuine 10x10 block
\`D_a\` of the SAME original fold (not an invented operator).

The original seed restricts to \`(1,v10)\` with
\`v10=e_(0,1)\`. Exact symbolic construction gives the
following 11x11 Krylov determinant:

\[
\boxed{
\det K_{11}=\frac{P_8(a)Q_2(a)}{512},
}
\]

where

\[
\begin{aligned}
P_8(a)={}&11583665+66174720a-44920944a^2
-19478232a^3\\
&-1670652a^4-2895936a^5+666144a^6\\
&-82944a^7+36864a^8,\\
Q_2(a)={}&69-72a+20a^2.
\end{aligned}
\]

The computation separately verified the structural factorization

\[
\det K_{11}
=
\underbrace{\det[v10,D_av10,\ldots,D_a^9v10]}_{P_8(a)/256}
\cdot
\underbrace{\det(D_a-I_{10})}_{Q_2(a)/2}.
\]

The first factor proves ten-cell controllability; the second
ensures the surviving fixed eigencharacter 1 does not collide
with the ten-cell spectrum.

## 3. No rational roots: uniform arithmetic certificates

First, \`Q2\` is strictly positive on ALL real and rational a,
by the exact square identity

\[
5Q_2(a)=(10a-18)^2+21>0.
\]

Second, the leading integer coefficient of \`P8\` is
\`36864\`, nonzero mod 13. The exact complete table

\[
(P_8(0),P_8(1),\ldots,P_8(12))\pmod{13}
=(2,9,2,1,9,8,3,6,6,8,1,12,11)
\]

contains NO zero. By the rational-root theorem, any rational
root in lowest terms has denominator dividing 36864 and hence
not divisible by13. Reducing that supposed rational root mod13
would produce one of the excluded thirteen elements. Therefore
\`P8(a)≠0\` for every rational a.

Consequently \`P8(a)Q2(a)/512≠0\` for every rational a.
The first eleven original iterates are linearly independent in
the invariant 11-cell subspace. Thus orbit dimension >=11.
Combined with the upper bound, it is **exactly 11** for all a.

## 4. Verification and formalization boundary

The complete Wolfram script
\`research/computations/GST_image3_half_curvature_exact_rank11_all_rational_20261111.wl\`
reconstructed the original U/J/M matrices, verified both
determinant factors, checked the positive square identity and
all 13 finite-field residues, and returned \`allPassed -> True\`.

At a=0, the 11x11 determinant is \`799272885/512 != 0\`.

Lean additions in
\`GSTImageThreeFiniteFieldSourceCertificates.lean\` encode
the mod13 finite-field nonroot leaves and rational quadratic
positivity (kernel status tracked by integrated CI).
The native upper bound was already compiled in
\`GSTImageThreeCurvatureResonance.lean\`.

The **full quantified rank11 theorem** currently has a source-level
proof with an exact computation, but not a single Lean declaration
integrating the 11x11 determinant identity and rational-root argument.
Do not call it Lean-kernel-certified until that formalization exists.

**Geometric scope:** This establishes an exact native GST
information-space orbit defect. It does not itself construct
cycles for arbitrary rational Hodge classes of smooth projective X.
