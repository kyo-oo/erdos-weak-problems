# GST Tate blowup / cosmology descent discriminator

- **Date:** 2026-10-20
- **Kind:** Exact geometric computation and structural proof attempt
- **Target:** Full canonical rational Hodge representatives on every original smooth projective complex X, or a genuine counterexample.
- **Base checkpoint:** `77622eec0f12210c070d22dc863a8ca61ab05afd`; continuing `GSTQuadricPrimitiveRulingGeometry.lean`, `GSTGraphV2SelfExpandingCosmology.lean`, and the October 20 interacting-blowup research record.
- **Mechanism:** Combine actual GST exceptional births, connected primitive rank gain, native Chow/K0 source conversion, and finite-degree geometry descent. Compute exactly what Hodge directions can occur before asserting arbitrary-original-X transport.
- **Evidence:** Rational Hodge/Chow blowup and projective bundle decomposition, exact symbolic Wolfram computation, GitHub Lean theorem `FiniteDegreeNativeDescent.finite_degree_hodge_pull_injective`; latter included in the later successful Graph V2 run 39405037695 on revision `213136a3fd4de5c7b8fd6104c067517be1089f1e`.
- **Status:** Uniform mathematical proof under the actual geometric blowup/projective bundle formula; finite-degree map application requires an instantiated nonzero-degree morphism and canonical cohomology pull-push comparison. This does NOT decide rational Hodge for arbitrary X.

## Exact connected-world Hodge polynomial

Let `X_0 = Bl_{Q^2}(P^4)`, where the smooth split quadric surface is `Q^2=P^1 x P^1`. Perform r additional disjoint smooth codimension-two blowups, each along a ruled surface `S_i`, a `P^1`-bundle over `P^1`, as constructed in the existing interacting GST birth family. With `t` marking Hodge bidegree (1,1), projective space and each center have rational diagonal Hodge polynomials

```
P(P^4,t)=1+t+t^2+t^3+t^4,
P(Q^2,t)=P(S_i,t)=(1+t)^2.
```

The codimension-two exceptional Chow/Betti term shifts bidegree by (1,1). Thus after r+1 blowups,

```
P(X_r,t) = 1+t+t^2+t^3+t^4 + (r+1)t(1+t)^2
         = 1 + (r+2)t + (2r+3)t^2 + (r+2)t^3 + t^4.
```

In particular `b_4=2r+3`, `b_6=r+2`, and the middle primitive dimension for an ample class is `b_4-b_6=r+1`. This agrees with the exact complete cup reconstruction in `GSTQuadricPrimitiveRulingGeometry.lean`; the numerical rank is not an independent source-span premise.

**Important algebraic conclusion:** Since `P^4`, `Q^2` and the ruled `S_i` have complete rational Chow/Betti Tate bases, iterated projective-bundle and blowup maps construct algebraic representatives for **all rational Hodge classes of each X_r**. Therefore this specific interacting blowup family cannot itself furnish a rational-Hodge counterexample, for ANY r; its unbounded primitive rank consists of genuine algebraic directions. The statement does not exclude non-Tate or intrinsically new GST world births.

## A direct nonzero-degree descent discriminator

The actual GST `FiniteDegreeNativeDescent.DegreePacket` carries a Hodge pullback and pushforward with `f_* f^* = d \cdot id`, `d != 0`. Consequently `f^*` is injective: if `f^*alpha=f^*beta`, apply `f_*` and multiply by `d^{-1}`. This was added as the Lean theorem `finite_degree_hodge_pull_injective` in `GSTGraphV2SelfExpandingCosmology.lean` at commit `673b93f1b87735b7e12ff631b0e68c5d8cba0747`.

The world `X_r` has `H^1(X_r,Q)=0` because its original projective space and all center blowup contributions are concentrated in even degrees. Any smooth abelian fourfold `A` has `dim_Q H^1(A,Q)=8`. Therefore an actual nonzero-degree generically finite map `X_r -> A` cannot exist: otherwise the compatible pullback `H^1(A,Q) -> H^1(X_r,Q)` would be injective from a nonzero space into zero.

This is a **specific no-go for a proposed descent from these complete Tate GST worlds to an arbitrary X**, not a statement that all GST cosmos births or all correspondences fail. It directs the source-generation effort toward non-split geometry arising on or from the arbitrary original X, not from finite-degree descent of the already-complete Tate worlds.

## Reproducible independent exact check

Wolfram expression (stateless kernel; integer r>=1):

```wl
Clear[t,r];
P=Expand[Sum[t^k,{k,0,4}]+(r+1)t(1+t)^2];
{P,Table[Coefficient[P,t,j],{j,0,4}],
 Coefficient[P,t,2]-Coefficient[P,t,3]}
```

Exact output: `{1+(r+2)t+(2r+3)t^2+(r+2)t^3+t^4,{1,2+r,3+2r,2+r,1},1+r}`. The symbolic computation checks coefficient algebra only; the uniform theorem comes from the actual geometric blowup formula.

## Source-generation target retained

The exact remaining task is to construct, for a prescribed original smooth projective X, p, and nonzero primitive rational Hodge residual alpha, a genuine algebraic perfect-complex/Chow source `z in CH^p(X)_Q` with nonzero genuine canonical Betti polarized pairing. The existing one-center K0 converter then supplies a smooth center and factorial-scaled exceptional return. A new source on the blown-up ambient space representing the exceptional lift would also work **only if born independently of a target Chow preimage on X**; the new `exceptional_lift_range_iff` in the same GST cosmology file precisely verifies the algebraic-equivalence test.

- **Attempt outcome:** Proved exact Tate blowup family Hodge rank and algebraicity from standard blowup geometry, and verified GST finite-degree injectivity law; no Hodge counterexample was constructed.
- **Route disposition:** Combined blowup/cosmology route remains OPEN for an intrinsic original-X non-Tate source; the naive all-X descent from this Tate-only family is excluded.
- **Next discriminating operation:** Produce an original-X sheaf/center whose canonical primitive period is provably nonzero independently of the target cycle's algebraic existence, and apply the already-verified GST K0/center exceptional return.
