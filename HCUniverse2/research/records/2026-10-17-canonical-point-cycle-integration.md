# GST construction — native subvarieties to point-generated Betti geometry

## Pinned objective
For each smooth projective complex variety \(X\), codimension \(p\), and rational primitive Hodge class \(\alpha\), construct an actual algebraic cycle on \(X\) whose canonical Betti class equals \(\alpha\).

## Exact native-to-Betti mechanism
A `CodimensionPoint X p` describes a genuine irreducible codimension-\(p\) subvariety. Its native algebraic generator is `codimensionPointCycle X p x`. The map `cycleClassFromPointGeometry` extends its Betti fundamental class uniquely and linearly to all native rational cycles through the finite point-presentation theorem.

For the explicit Fermat source family, take the genuine native cycle

\[
Z_i=d\,[P_i]-H,\qquad H=h^m,
\]

and intersection measurements

\[
\langle\operatorname{cl}(Z_i),\operatorname{cl}(Z_j)\rangle
=d^2q_{m,d}\,\delta_{ij}-d.
\]

The Gram detector's trivial kernel proves independence of these native geometric Betti classes.

## Implemented files
- `GSTFermatCanonicalPointRankBridge.lean`: native point-cycle construction and exact measurement-to-rank theorem.
- `GSTCanonicalPointGeometryStage2G.lean`: all-codimension cycle-class map assembled from point fundamental classes.
- `GSTClassicalHodgeGeometricCycleClassPointRigidity.lean`: finite presentation and uniqueness of point-class extension.

## Verification
- Arithmetic and cohomological detector: [kernel run #39022986348](https://github.com/kyo-oo/HC-PROOF/actions/runs/39022986348).
- Native-point and full-module checks: use the latest runs on [the research branch](https://github.com/kyo-oo/HC-PROOF/actions) after the dependency-root repair.

## Next theorem
Produce the analytic fundamental classes as Lean objects, discharge their intersection comparisons geometrically, and establish full primitive cycle generation on an arbitrary original \(X\).
