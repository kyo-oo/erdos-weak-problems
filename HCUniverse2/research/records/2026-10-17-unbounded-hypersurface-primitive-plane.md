# GST research route — primitive algebraic planes in all even dimensions

## Goal
Construct non-Lefschetz algebraic middle-Hodge classes on explicit original smooth projective varieties in arbitrary even dimensions, and use the resulting native geometry as building blocks for the universal program.

## Uniform family
Let \(X_d^{2m}\subset\mathbb P^{2m+1}\) be a smooth degree-\(d\) hypersurface containing \(P=\mathbb P^m\), \(d\ge2,m\ge1\). Put \(H=h^m\). The true geometric intersection numbers are

\[
H^2=d,\quad HP=1,\quad P^2=q_{m,d}=[t^m]\frac{(1+t)^{m+1}}{1+dt}.
\]

The exact Gram determinant is

\[
\det\begin{pmatrix}d&1\\1&q_{m,d}\end{pmatrix}
=(-1)^m(d-1)^{m+1}.
\]

The constructed native algebraic cycle

\[
Z_{m,d}=d[P]-H
\]

has \(ZH=0\) and \(Z^2=(-1)^m d(d-1)^{m+1}\), certifying its primitive, geometrically nonzero direction.

## Smooth source and verification
One explicit hypersurface family is \(\sum_i(y_ix_i^{d-1}+y_i^d)=0\). The simultaneous Jacobian equations force all homogeneous coordinates to vanish, hence each projective hypersurface is smooth.

The normal Chern and Gram identities were computed exactly in Wolfram and proved uniformly in `GSTCubicFourfoldPlanePrimitive.lean` and `GSTMaximalLinearHypersurfacePrimitive.lean`.

**Kernel check:** [run #39019438469](https://github.com/kyo-oo/HC-PROOF/actions/runs/39019438469), green.

## Geometric extension
Build independent component families on the same carrier and connect their primitive intersection measurements with canonical analytic cycle classes; extend the construction to arbitrary smooth projective varieties.
