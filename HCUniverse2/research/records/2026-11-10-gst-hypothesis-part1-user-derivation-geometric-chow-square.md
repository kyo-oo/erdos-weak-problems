# GST Hodge hypothesis — Part 1, canonical original-X Chow fold

Date: 2026-11-10. **Provenance:** User-uploaded one-page \`HYPOTHESIS PROOF, PART 1.pdf\`. Independent source: existing repository at branch \`research/gpt6-gst-wave-curvature-spectral-birth-20261110\` and its GST Hodge conditional. New scoped branch: \`research/gpt6-gst-hypothesis-part1-chow-square-20261110\`.

## User's exact insight (preserved)

The user proposed an algebraic original-X correspondence \(\Gamma\), native cycle action \(N\), Betti action \(T\) satisfying \(\operatorname{cl}(NZ)=T\operatorname{cl}(Z)\); then \(Z=Z_0+N(Z_0)\) gives \(\operatorname{cl}(NZ_0+N^2Z_0)\). Their aim was to iterate over \(n=0,1,2,\ldots\), connect infinity control / N-cohomology / curvature / wave laws, and obtain a geometric fold for every original smooth projective \(X\) and codimension \(p\).

**Correct first lemma:** \(NZ=NZ_0+N^2Z_0\) and \(\operatorname{cl}(NZ)=T\operatorname{cl}(Z_0)+T^2\operatorname{cl}(Z_0)\), *provided* the commuting square already holds. This is not by itself a proof of the commuting square; it invokes it. Index \(n=0\) means \(N^0=\mathrm{id}\), not zero. For a zero cumulative base define \(S_0=0\), \(S_n=\sum_{k=1}^nN^kZ_0\).

## Exact new theorem: universal genuine Chow correspondence and commuting square

Let \(X\) be a smooth connected projective complex variety, \(\dim_\mathbf C X=d\), \(0\le p\le d\), \(h\in\mathrm{CH}^1(X)_\mathbf Q\) ample, \(q=\int_X h^d>0\).

Set

\[
\Pi_{h,p}=\frac{1}{q}\mathrm{pr}_1^*h^{d-p}\cdot\mathrm{pr}_2^*h^p\in\mathrm{CH}^d(X\times X)_\mathbf Q,\qquad
\boxed{\Gamma_{X,p}=\Delta_X+\Pi_{h,p}}.
\]

The corresponding *actual* Chow native action on codimension-p algebraic cycles and Betti action on rational degree-\(2p\) cohomology are

\[
\boxed{N(Z)=Z+\frac{\deg(Z h^{d-p})}{q}h^p},\qquad
\boxed{T(\alpha)=\alpha+\frac{\int_X\alpha\cup\operatorname{cl}(h)^{d-p}}q\operatorname{cl}(h)^p}.
\]

These satisfy \(\boxed{\operatorname{cl}_X^{\mathrm{can}}(N Z)=T(\operatorname{cl}_X^{\mathrm{can}} Z)}\) **for every** \(Z\in\mathrm{CH}^p(X)_\mathbf Q\) on **every** original \(X\) as above, without assuming the Hodge conjecture or unknown target cycles. The cycle \( \Gamma_{X,p}\) is a genuine codimension-\(d\) Chow cycle on the self-product, not an arbitrary abstract endomorphism. Proof: the algebraic diagonal is the Chow identity; push-forward along the second projection and the projection formula give the native formula. Betti proper push-forward, pull-back and cup product give the Betti formula. The canonical cycle-class map respects these operations, proving the square independently of the user's orbit expansion.

### Exact all-natural-number and formal-infinite transport

Let \(P=N-\mathrm{id}\) and \(E=T-\mathrm{id}\) denote the normalized Chow/Betti ample-source projectors. They satisfy \(P^2=P\), \(E^2=E\) and \(\mathrm{cl}\circ P=E\circ\mathrm{cl}\). Thus for every natural \(n\ge0\),

\[
N^n=(I-P)+2^n P,\quad T^n=(I-E)+2^n E,\quad
\operatorname{cl}(N^nZ)=T^n\operatorname{cl}(Z).
\]

A literal finite geometric \emph{cumulative} correspondence is \(\Gamma^{[n]}=\sum_{k=0}^n\Gamma^{\circ k}\in\mathrm{CH}^d(X\times X)_\mathbf Q\), acting by

\[
\sum_{k=0}^n N^k=(n+1)(I-P)+(2^{n+1}-1)P.
\]

Every finite noncommutative polynomial word in any set of actual Chow correspondences obeys the same native--Betti square. In particular a commutator \( [N_1,N_2]\) transports to \([T_1,T_2]\) on classes.

The infinity-control interpretation that is always algebraically legitimate is a **formal** correspondence series in \(\mathrm{Corr}^0(X)[[t]]\),

\[
\mathcal G(t)=\sum_{n\ge0}\Gamma^{\circ n}t^n=(\Delta_X-t\Gamma)^{-1}
=\frac{\Delta_X-\Pi_{h,p}}{1-t}+\frac{\Pi_{h,p}}{1-2t}.
\]

The coefficientwise commuting square is exact. This formal infinity is not automatically a single finite Chow correspondence at \(t=1\); an infinite physical/geometric limit must be defined separately.

### Exact no-go for the single ample projector

For every seed \(Z_0\), the Betti orbit of \(N=I+P\) lies in a space of dimension at most TWO:

\[
T^n\operatorname{cl}(Z_0)=(I-E)\operatorname{cl}(Z_0)+2^n E\operatorname{cl}(Z_0).
\]

For the canonical \(Z_0=h^p\), it lies in a space of dimension ONE and equals \(2^n\operatorname{cl}(h^p)\). Therefore infinite coefficients do not imply independent directions or the universal GST single-fold hypothesis. The first 9 exact powers and cumulative folds were checked in Wolfram. A three-dimensional countermodel with \(P=\operatorname{diag}(1,0,0)\), seed \(v=(1,1,1)\) has orbit rank 2 and zero 3x3 Krylov determinant for all n. This refutes the claim that the rank of this particular orbit automatically keeps increasing, NOT the Hodge conjecture or the user's broader GST framework.

## Stronger geometric wave/curvature route: two actual Chow projectors

For any two ample divisors \(h,k\), \(\Gamma_{h,k,p}=\Delta_X+\Pi_{h,p}+\Pi_{k,p}\) and \([\Pi_{h,p},\Pi_{k,p}]\) are actual Chow correspondences. Their genuine native and canonical Betti operators obey naturality for every cycle; the commutator gives a geometric version of GST's noncommutative curvature.

On the concrete original \(X=\mathbf P^1\times\mathbf P^1\), with basis \(H_1,H_2\) satisfying \(H_1^2=H_2^2=0,\ H_1H_2=1\), take \(p=1\), \(h=H_1+H_2\), \(k=H_1+2H_2\). Exact matrices are

\[
P_h=\begin{pmatrix}1/2&1/2\\1/2&1/2\end{pmatrix},\quad
P_k=\begin{pmatrix}1/2&1/4\\1&1/2\end{pmatrix},\quad
[P_h,P_k]=\begin{pmatrix}3/8&0\\0&-3/8\end{pmatrix}.
\]

The actual geometric \(T=I+P_h+P_k=\begin{pmatrix}2&3/4\\3/2&2\end{pmatrix}\) with seed \(h=(1,1)^T\) has

\[
K=[h,Th]=\begin{pmatrix}1&11/4\\1&7/2\end{pmatrix},\quad \det K=3/4\ne0.
\]

The rational dual detector \(\ell=(-4/3,4/3)\) gives \(M_{ij}=\ell(T^{i+j}h)=\begin{pmatrix}0&1\\1&4\end{pmatrix}\), \(\det M=-1\ne0\). Thus this original smooth projective surface really satisfies the strong single-fold cyclicity condition (already independently true by its divisor geometry), without assuming a Hodge-to-Chow inverse as input.

## Exact status and scope

- **PROVED in full Chow intersection theory:** actual codimension-d \(\Gamma_{X,p}\) on every original smooth projective \(X\); native and canonical Betti actions; commuting square for every cycle and all natural iterates; algebraic finite sums/compositions/commutators; formal series; a genuine full-cyclic two-projector surface example.
- **NOT PROVED:** identify \(\Gamma_{X,p}\) with the owner's original twelve-cell seven-axis \(U+J+M\) fold on every \(X\); achieve full Hodge cyclicity on arbitrary X and all p; show the full Chow correspondence belongs to the narrower repo \`RealizedFiniteClosedCorrespondence\` datatype (the latter requires finite closed correspondence geometry). These are *additional* geometric realization/rank goals; do not label Part 1's naturality as Hodge solution.
- **Computational evidence:** [executed exact Wolfram source](../computations/GST_hypothesis_part1_original_X_fold_20261110.wl) returned all ten exact tests True, \`allPassed -> True\`, after re-fetch of the committed file. Those tests validate the rational matrices and 0..8 iterations, not the universal geometric theorem; that theorem is established by the projection-formula proof above.

This is a Mathbox-style bounded attempt record whose verdict is **proved as written after typing correction** for universal *existence and naturality of a full Chow fold*. The user's stronger intended *literal GST universal realization and full cyclic-source birth* remains an unproved dependent proposition. Neither statement is replaced or dismissed.
