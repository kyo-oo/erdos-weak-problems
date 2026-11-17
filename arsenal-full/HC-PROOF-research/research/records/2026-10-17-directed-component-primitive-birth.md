# GST construction — primitive cycles from directed algebraic components

## Source construction
Consider a smooth cubic fourfold containing a projective plane \(P\), and let \(H=h^2\). Their middle intersection lattice has Gram

\[
\begin{pmatrix}3&1\\1&3\end{pmatrix}.
\]

A hyperplane-square cycle decomposes into a plane component and residual degree-two surface \(Q=H-P\). The total cut has primitive component zero, while each individual component can have a nonzero primitive projection.

With the integral primitive numerator \(\pi_3(W)=3W-(H\cdot W)H\),

\[
\pi_3(P)=3P-H,\qquad
\pi_3(Q)=H-3P,\qquad
\pi_3(P)+\pi_3(Q)=0.
\]

Moreover, \((3P-H)^2=24\), certifying a nonzero primitive algebraic class.

## Verified methods
- Wolfram checked the exact rational and integral lattice arithmetic.
- Lean `GSTCubicFourfoldPlanePrimitive.lean` establishes the component identities and self-intersection formulas.
- [GitHub Actions #39017260670](https://github.com/kyo-oo/HC-PROOF/actions/runs/39017260670) verified the original cubic source; later geometric and Fermat extensions were also kernel-checked.

## Research advance
Directed component extraction separates algebraic subvarieties whose primitive contributions cancel inside a complete cut. It provides a geometric route for manufacturing multiple native primitive classes.

## Next construction
Generalize component separation and its cohomological intersection detectors on arbitrary original varieties, then prove full geometric rank in each rational primitive Hodge sector.
