# GST verification — smooth hypersurface primitive construction

## Mathematical construction
For degree \(d\ge2\) and even complex dimension \(2m\), let \(X\subset\mathbb P^{2m+1}\) be a smooth degree-\(d\) hypersurface containing a maximal plane \(P\cong\mathbb P^m\). The normal sequence

\[
0\to N_{P/X}\to\mathcal O_P(1)^{m+1}\to\mathcal O_P(d)\to0
\]

gives \(q_{m,d}=c_m(N_{P/X})\) and

\[
d q_{m,d}-1=-(1-d)^{m+1}.
\]

The algebraic primitive cycle \(Z=d[P]-h^m\) is orthogonal to \(h^m\), with exact self-intersection

\[
Z^2=(-1)^m d(d-1)^{m+1}.
\]

## Geometry and kernel results
The explicit equation \(F_{m,d}=\sum_i(y_ix_i^{d-1}+y_i^d)\) contains \(P=\{y_i=0\}\). Its projective Jacobian admits a direct all-dimensional nonsingularity certificate.

**Verified:** [run #39019438469](https://github.com/kyo-oo/HC-PROOF/actions/runs/39019438469), commit `60208401ac749d7fa4513a6fe078d8f34f5cec6f`. `GSTCubicFourfoldPlanePrimitive.lean` compiled with its kernel axiom audit. Artifact 12095189946.

The independent all-dimensional normal-top-Chern recurrence was already in `GSTMaximalLinearHypersurfacePrimitive.lean`. This route adds the explicit smooth geometric source and coordinate Jacobian certificate.

## Next construction
Integrate projective scheme intersection and the canonical Betti fundamental-class pairing as Lean-native geometric operations; apply the source-construction approach across arbitrary smooth projective carriers.
