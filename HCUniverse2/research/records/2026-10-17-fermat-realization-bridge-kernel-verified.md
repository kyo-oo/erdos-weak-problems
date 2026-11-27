# GST kernel verification — geometric Fermat measurement bridge

## Construction
For every \(m\ge1,d\ge3\), the Fermat hypersurface \(X_{m,d}\subset\mathbb P^{2m+1}\) carries \(d\) disjoint maximal linear planes \(P_i\). Their primitive algebraic classes \(Z_i=d[P_i]-h^m\) have exact intersection Gram

\[
M_{ij}=d^2q_{m,d}\delta_{ij}-d,\qquad
q_{m,d}=[t^m]\frac{(1+t)^{m+1}}{1+dt}.
\]

The normal-top-Chern recurrence proves \(q_{m,d}\notin\{0,1\}\), so the Gram matrix is invertible.

## Lean bridge
`GSTMaximalLinearHypersurfacePrimitive.fermatGeometricMeasuredFamily_independent` proves that whenever the rational Betti classes have these exact geometric intersection measurements, every rational linear relation among the classes has zero coefficients. The proof works uniformly in \(m,d\).

**Verified:** [GitHub Actions #39022986348](https://github.com/kyo-oo/HC-PROOF/actions/runs/39022986348), commit `00c81a6920c0e9fa1d0e3843a31b9f44582a89c7`, green. The workflow's kernel axiom audit passed. Evidence artifact 12097363368.

## Integration target
Instantiate the intersection measurements using canonical analytic fundamental classes. Then promote the source-generation mechanism from Fermat hypersurfaces to arbitrary smooth projective varieties, and prove complete primitive Hodge spanning.
