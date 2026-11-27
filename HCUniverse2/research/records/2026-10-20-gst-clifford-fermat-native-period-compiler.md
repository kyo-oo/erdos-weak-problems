# GST Clifford–Fermat native period compiler in every middle dimension

- **Date:** 2026-10-20
- **Kind:** constructive original-world algebraic-source frame and exact rational period compiler
- **Program:** full original-X rational Hodge conjecture, Gate 3, blowup/cosmology/native K0
- **First mathematical checkpoint:** `77622eec0f12210c070d22dc863a8ca61ab05afd`
- **Final focused compiler checkpoint:** `87e43839d893846f42e368c2b1bdb0e58251a5f7`
- **Source:** [GSTMaximalLinearHypersurfacePrimitive.lean](../../GSTMaximalLinearHypersurfacePrimitive.lean)
- **Lean focused CI:** [#39406562118](https://github.com/kyo-oo/HC-PROOF/actions/runs/39406562118), **success** at `87e43839d893`
- **Descendant full pinned integration:** [#39406606804](https://github.com/kyo-oo/HC-PROOF/actions/runs/39406606804), **success** at `6f4b0632c712`, which includes the exact compiler theorem; no `sorryAx` was reported by its integration audit.
- **First coupled-source focused and pinned integration CI:** [#39404114096](https://github.com/kyo-oo/HC-PROOF/actions/runs/39404114096) and [#39404114109](https://github.com/kyo-oo/HC-PROOF/actions/runs/39404114109), **both success** at `77622eec0f12`.
- **Review:** direct mathematical derivation, exact independent Wolfram checks, self-review. Scheme-level perfect-complex/Betti comparison remains a separate geometric instantiation, not supplied as Lean axioms.

## Geometry from equations, not from a target preimage

Let `m≥1` and `d≥3`. On the smooth Fermat degree-d hypersurface
`X_(m,d) ⊂ P^(2m+1)` take the d pairwise disjoint maximal linear m-planes
`P_i` arising from the d-th roots of unity. Put `h=c1(O_X(1))` and
`Z_i=d[P_i]-h^m`. The existing normal sequence derives the signed
self-intersection coefficient

```
s_(m,d) = sum_(k=0)^m binomial(m+1,k) (-d)^(m-k),
d*s_(m,d)-1 = -(1-d)^(m+1).
```

Each defining decomposition `F=sum l_i q_i` gives an authentic graded
Clifford/Shamash perfect-complex source `E_i`. The graded free resolution
fixes its middle-character contribution, rather than stipulating a
Hodge-class preimage:

```
m! ch_m(E_i) = A_(m,d) h^m + B [P_i],    B=(-1)^m m!.
```

Pairing against `Z_j` removes the ambient coefficient `A_(m,d)`.
Consequently the exact source-to-primitive-period matrix is

```
M_(m,d) = B (d s_(m,d) I_d - J_d).
```

This combines two separate GST native geometric inputs: the equation-born
K0 source and the original-scheme plane intersection law. Its entries are
not abstract target-supplied Gram data.

## Exact rank and complete measured period reconstruction

The eigenvalues of `M_(m,d)` are `B d s` on the (d−1)-dimensional
coordinate-sum-zero sector and `B d(s−1)` on the all-ones sector. Since the
normal-Chern law forces `s≤-1` for odd m and `s≥2` for even m, both
are positive, and the determinant is

```
det(M_(m,d)) = (B*d)^d * s^(d−1) * (s−1) ≠ 0.
```

For an *arbitrary rational period vector on this source frame*
`beta=(beta_j)_(j<d)`, the source coefficients are explicitly

```
a_j = beta_j/(B*d*s) +
      (sum_i beta_i)/(B*d^2*s*(s−1)).
```

Direct substitution gives `M a = beta`. This has no full-rank premise;
the nonzero denominator proof is the existing `normalTopCoeff_ne_zero_one`.
The two Lean declarations are
`fermat_clifford_native_period_kernel_trivial` and
`fermat_clifford_period_compiler_exact`; the latter was surgically repaired
after exact GitHub log inspection, and the final focused kernel compile is green.

**Exact independent Wolfram test:** all 25 combinations
`1≤m≤5, 3≤d≤7` satisfy the determinant formula; all 36 combinations
`1≤m≤6, 3≤d≤8` invert the constructed matrix on an integer test vector.
At `m=2,d=3`,

```
M = [[16,-2,-2],[-2,16,-2],[-2,-2,16]]
beta = (5,-1,0),  a=(17/54,-1/54,1/27),  M*a=beta.
```

## Combination with GST smooth-center and exceptional birth

The previous original-X `K0 → native Chow → smooth incidence center`
construction applies to rational linear combinations of actual equation-born
sources after the correct Adams/leading-character normalization. For
`dim X=2m`, its center is smooth inside the **same** X and its
exceptional pushforward has a nonzero scalar multiple of the prescribed
source-frame period vector. The mechanism therefore links *equations →
perfect complexes → d independent primitive periods → target coefficients →
one smooth original-world center → blowup exceptional feedback*.

The universal-X research task is now **not** to rederive an inverse of this
concrete matrix, but to construct a comparable nonambient geometric packet
for a prescribed primitive residual on an arbitrary smooth projective X.
An arbitrary Hodge class is not known to lie in the displayed finite
Fermat frame, and existence of its original-X source cannot be obtained
by assuming a Chow preimage or by algebraically contracting a cohomological
class through an exceptional correspondence.

**Status:** proved integral/rational Lean coefficient and matrix identities
for the declared source frame; finite independent computational checks;
scheme-level and canonical Betti realization remain exact geometric checks.
No claim of universal rational Hodge surjectivity or counterexample.
