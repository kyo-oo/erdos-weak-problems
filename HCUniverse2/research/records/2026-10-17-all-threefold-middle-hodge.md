# GST construction — all smooth projective threefolds, codimension two

## Target
Given a smooth projective complex threefold \(X\) and rational Hodge class \(\alpha\in H^4(X,\mathbb Q)\cap H^{2,2}(X)\), construct an algebraic codimension-two cycle representing \(\alpha\).

## Geometric construction
Hard Lefschetz gives \(\beta=(h\smile)^{-1}\alpha\in H^2(X,\mathbb Q)\cap H^{1,1}(X)\). The Lefschetz \((1,1)\) theorem constructs a divisor \(D\) with \(\operatorname{cl}(D)=\beta\). The concrete algebraic cycle \(h\cdot D\) satisfies

\[
\operatorname{cl}_X(h\cdot D)=h\smile\beta=\alpha.
\]

The threefold primitive test is cup product by \(h^0=1\). The primitive remainder therefore vanishes identically, and the full class is represented by the native Lefschetz correction.

## Lean results and evidence
`GSTUniversalCodimensionTwoPrimitiveExtraction.lean` contains `threefold_primitive_hodge_remainder_zero` and `every_threefold_hodge_two_class_has_native_cycle`, built from the specified geometric Hard Lefschetz, cycle-class compatibility, and divisor representation interfaces.

**Kernel result:** [GitHub Actions #39019810931](https://github.com/kyo-oo/HC-PROOF/actions/runs/39019810931), green.

## Next theorem
Extend the construction of native primitive representatives to higher-dimensional varieties, beginning with codimension-two classes on fourfolds, and connect every representation to the canonical analytic cycle-class implementation.
