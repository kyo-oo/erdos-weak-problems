# GST blowup Picard/K₀ filtration obstruction and diagonal escape

- **Date:** 2026-10-20
- **Kind:** exact geometric constructor discriminator and formally specified infinite-parametric source test
- **Base checkpoint:** `5624ea2817430b879cf2ca655079144f0d3ed098`
- **Source commit:** `22846297a30abd38649e46407143502d8a96dd6a`
- **Lean source:** `GSTK3PrimitiveGram.lean`
- **Focused kernel check:** [#39409868180](https://github.com/kyo-oo/HC-PROOF/actions/runs/39409868180), in progress when recorded; verdict awaits revision-matched success
- **Exact computation:** Wolfram Language symbolic calculation for algebraic indeterminates d,u,v,l with d≠0, returned zero primitive diagonal pairing identically
- **Mathematical evidence:** direct universal rational polynomial identity; geometric formula uses exceptional projective bundle and normal-tangent Chern identity; Lean compile result pending
- **Route:** determine whether increasing GST blowup arity, adding Picard twists, or using nonsplit *extensions of line bundles* can produce the missing primitive diagonal period.

## 1. Genuine test geometry

Let S be any smooth projective K3 surface, h ample with d=∫_S h²>0, and let original X=S×S. Embed X in P^N with normal codimension c=N-4≥2. Take the **actual smooth rational ambient blowup** Y=Bl_X(P^N), with hyperplane pullback H and exceptional Cartier divisor E; write l=N+1.

The native primitive diagonal D=Δ−A−B−U/d has `Q(D,D)=21` and
[
Q(D,H_X^2)=0,qquad Q(D,c_2(T_X))=0.
]
The diagonal sheaf defines an independently algebraic non-tautological K₀ source with nonzero D period; this contrast measures whether an alleged universal constructor actually escapes the divisorial world-birth sector.

## 2. Exact ALL-PARAMETER blowup return

For the genuine line bundle L=O_Y(uH+vE), where u,v∈Z (the checked polynomial formula extends to all rational u,v), its degree-three Chern character is

[
\operatorname{ch}_3(L)=\frac{(uH+vE)^3}{6}.
]

For the exceptional original-X Chow return R(W)=−q_*(ξ^{c−2}j^!W),

[
R(H^2 E)=h^2,quad
R(H E^2)=-h\,s_1(N)=l h^2,quad
R(E^3)=s_2(N)=\frac{l(l+1)}{2}h^2+c_2(T_X).
]

These equations follow from c(N)c(T_X)=(1+h)^l and c₁(T_X)=0, with the project's convention s₁=−c₁ and s₂=c₁²−c₂.

Thus
[
\boxed{
R(\operatorname{ch}_3(L))=A(u,v,l)h^2+B(v)c_2(T_X)
}
]
with
[
A=\frac{3u^2v+3lu v^2+\frac{l(l+1)}2v^3}{6},
qquad B=\frac{v^3}{6}.
]

For EVERY u,v,l and d≠0, we have the **exact zero period**
[
\boxed{Q(D,R(\operatorname{ch}_3(L)))=0.}
]
No numerical truncation, genericity or rational orthonormality is used.

## 3. General finite Picard-filtered perfect complexes

For each finite list (u_i,v_i) and every rational coefficient λ_i, additivity implies
[
Q\left(D,\sum_i\lambda_i R(\operatorname{ch}_3(O_Y(u_iH+v_iE)))\right)=0.
]

A perfect complex with a finite filtration by these line bundles has, in rational K₀, the same alternating sum of graded line-bundle classes. Therefore ANY SUCH filtered perfect complex, even when the extensions are nonsplit as sheaves, remains invisible to D under this GRR/exceptional return.

This is a strictly stronger failed-constructor certificate than testing hyperplane/ex-divisor monomials in a bounded degree or computing one special twist. It closes **the entire Picard-generated K₀ constructor sector** for this discriminator. It does NOT close all perfect complexes, all coherent sheaves, or GST's more general nonsplit geometric births.

## 4. Kernel-targeted declarations and exact independent test

Added to `GSTK3PrimitiveGram.lean`:

- `k3AmbientBlowupLineBundleCh3Return`
- `k3_ambient_blowup_line_bundle_diagonal_period_zero`
- `k3_ambient_blowup_finite_line_bundle_packet_period_zero`

The coordinate definition uses genuine K3 intersection formulas h²=d(A+B)+2U and c₂(T_X)=24(A+B). The Lean theorems establish the rational identities in that geometric coefficient model, not a formal universal Chow→Betti comparison of all K3 schemes.

Independent exact Wolfram results:
```text
Q(D,h²)=0
Q(D,c₂)=0
Q(D,A h²+B c₂)=0   (identically, all d≠0,u,v,l)
```

## 5. Changed construction decision

One can no longer reasonably seek the missing primitive diagonal in the rational span of ambient hyperplane/ex-divisor line-bundle Chern classes, arbitrary new twists, or their filtered extensions. An actual K₀ source must escape the Picard-generated subgroup—such as the independently constructed diagonal sheaf, a genuine graph/Clifford source, or a sufficiently nontrivial moduli/sheaf construction. The ongoing GST exceptional GRR original-X compiler then checks this new object's nonzero residual period and immediately produces an independent original-X Chow direction.

**Outcome:** unconditional polynomial zero-period theorem for the exact K3 source model; counterexample to the *claimed universal efficacy of the Picard-filtered constructor*, not a counterexample to rational Hodge. The wider full-X non-tautological source route remains open.
