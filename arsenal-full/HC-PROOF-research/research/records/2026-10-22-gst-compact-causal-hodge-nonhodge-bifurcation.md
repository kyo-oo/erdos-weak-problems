# GST compact causal Hodge/non-Hodge bifurcation — the owner's binary topology test

- **Date:** 2026-10-22 IST
- **Kind:** Mathbox substantive research route, uniform arbitrary-X complex geometry, exact cohomological / Chern threshold and Wolfram finite audit
- **Program:** GST emergent-dimensional spatial topology folds, directly targeting the owner's explicit alternative: non-Hodge structure born from a topology fold of arbitrary X OR always Hodge structure after dimensional topology changes
- **Base checkpoint:** `e99e617dccabda5669ee2ffacebfb65a6caec6b5` on `research/gpt6-native-point-primitive-span-20261017`
- **Inputs:** Every connected smooth projective complex original `X` (dimension d, including d=0), ample `L` (h=c1 L), integer fold arity `r>=2`, occupancy `0<=k<=r`, real contraction `0<q<1`
- **Relevant GST source laws directly inspected:** `GSTGeneralSpace.lean` (dimension-free space); `GSTGraphV2SelfExpandingCosmology.lean` (`WorldClosure` and arbitrary-arity `Birth`); `GSTGraphV2UnboundedHigherCausality.lean` (higher causal cells); `GSTGradedWorldAlgebra.lean` (signed causal fold signatures); `GSTGeneralSpaceCohomology.lean` (canonical cycle-image preservation under REVERSIBLE transports). These existing interfaces are not presented as an actual Lean encoding of holomorphic Hopf bundles.
- **Nearest prior route:** `2026-10-22-gst-signed-causal-purity-spectrum.md` produced mixed-Hodge signed weight gaps on singular/open algebraic worlds. Those worlds still carry legitimate MHS. The new route generates a genuinely non-Hodge smooth COMPACT complex world; no singular or open variety is used, and a rank-dependent Euler class changes the original-X pullback cohomology itself.
- **Success criterion:** for EVERY X and all r, exhibit actual identical-complex-dimension smooth compact geometry both preserving and breaking pure Hodge structure; compute the first decisive Hodge obstruction, full graded Betti response, a causal all-arity topology threshold, and recovery or annihilation of arbitrary original-X cohomology.
- **Failure criteria:** any quotient not properly discontinuous/compact, claimed pure Hodge failure not certified by an invariant, missing Gysin exactness, or confusion between new transformed world and unchanged X.

## Exact geometric construction and theorem

Define the actual algebraic rank-r bundle `E_{r,k}=L^k ⊕ O_X^(r-k)`.
Two realized outputs of **the same complex dimension d+r** are:

```text
P_(r,k)(X) = P(O_X ⊕ E_(r,k))                smooth projective, pure Hodge all degrees
H_(r,k)(X) = (E_(r,k) minus zero section)/q^Z  smooth compact complex, Hopf fibers
```

An arbitrary Hermitian norm provides a precise smooth diffeomorphism
`H_(r,k)(X) = S(E_(r,k)) × S¹`.
The sphere fiber `S^(2r-1)` is simply connected for r>=2. Consequently

```text
b1(P_(r,k)(X)) = b1(X)      even
b1(H_(r,k)(X)) = b1(X) + 1  odd
```

A pure rational weight-one Hodge structure has even underlying dimension, since conjugate `H^(1,0)` and `H^(0,1)` have equal ranks. Therefore the latter manifold **cannot have the usual pure degree-one rational Hodge structure**. This is a categorical non-Hodge result, stronger than assigning a negative/positive purity gap to a legitimate MHS on a singular/open algebraic variety. It is **not** a counterexample on the unchanged smooth-projective X. No Deligne MHS is assigned by fiat to the compact nonalgebraic world.

## Full-arity topological occupancy threshold on original X

True top Chern of original-X algebraic bundle:
`c_r(E_(r,k)) = 0` if `k<r`, equals `h^r` if `k=r`.
The unit-sphere Gysin sequence proves for every cohomological degree `j`:

```text
ker[π*:H^j(X,Q) -> H^j(H_(r,k)(X),Q)]
   = c_r(E_(r,k)) cup H^(j-2r)(X,Q).
```

For `k<r`, a nonzero trivial-summand holomorphic vector defines actual holomorphic section `s:X->H`; `s* π*=id` for ALL prescribed original cohomology classes, including every rational (p,p) Hodge target α, independently of its algebraicity. For `k=r`, the kernel is precisely `h^r H^(j-2r)`. If `2<=r<=dim X`, the known nonzero algebraic Hodge class `h^r` is annihilated by the Hopf fold while projective-bundle pullback preserves it.

Unlike spectator tensor products, this modifies the pullback of the actual original-X cohomology via its true Chern/Euler class.

## Entire original-X Betti spectral law

Let `B_X(t)=Σ_j b_j(X)t^j`, `a_j=rank(c_r(E)cup-:H^(j-2r)(X)->H^j(X))`, `R(t)=Σ a_j t^j`. Gysin derives:

```text
B_pure(t) = B_X(t) (1+t²+...+t^(2r))
B_break(t) = (1+t)[(1+t^(2r-1)) B_X(t) - (1+t^(-1))R(t)]
R=0 when k<r; for k=r it is the rank profile of h^r multiplication.
```

The broken branch is a full ordinary rational Betti polynomial, not a falsely imposed Hodge polynomial on a non-Kähler manifold.

For `X=P^d`, an all-d formula holds:
`B_break,k=r=(1+t)(1+t^max(2d+1,2r-1))Σ_(i=0)^min(d,r-1) t^(2i)`.
For k<r, `B_break=(1+t)(1+t^(2r-1))Σ_(i=0)^d t^(2i)`.

At `X=P², r=2`:
- Pure P(O⊕L⊕L): `1+2t²+3t⁴+2t⁶+t⁸`
- Breaking yet target-faithful `k=1`: `1+t+t²+2t³+2t⁴+2t⁵+t⁶+t⁷+t⁸`
- Breaking with h² annihilated `k=2`: `1+t+t²+t³+t⁵+t⁶+t⁷+t⁸`

## Verification provenance and precise scope

- **Mathematical derivation:** [LaTeX full proof](../derivations/GST_compact_causal_hopf_fold_hodge_dichotomy_2026-10-22.tex). Uniform argument using local holomorphic contraction, smooth compact Hopf quotient, homotopy long exact sequence, Hodge weight-one parity, oriented sphere-bundle Gysin, Whitney Chern and projective-bundle formula.
- **Wolfram script:** [exact source](../computations/gst_compact_causal_hopf_fold_2026_10_22.wl), committed and then fetched by current GitHub blob `39026aa454ac3aa20febd5f431d085c388b54861`; that **exact fetched source was executed** in a stateless Wolfram Language evaluator.
- **Finite results:** all **297/297** enumerated `d=0..8`, `r=2..7`, `k=0..r` cases passed the stated Chern occupancy, odd/even b1, Poincaré duality, Euler characteristic and closed Betti-polynomial consistency checks. These are finite corroboration, not proof of complex Hopf geometry.
- **Evidence:** uniform theorem written and self-reviewed in mathematics-first LaTeX; executable finite Wolfram verified; **analytic quotient and MHS statements not Lean formalized**, and no GitHub Actions workflow green claim for them.
- **Original-X rational Hodge existence:** no `Z_alpha in CH^p(X)_Q` constructed for unknown α. Both geometric outputs are actual spaces built from any original X, but the broken one is outside the smooth-projective domain of the conjecture.
- **Important categorical interpretation:** smooth projective folds always retain pure Hodge structures; singular or nonproper complex algebraic folds always retain some MHS; compact complex non-Kähler Hopf folds can fail the pure degree-one Hodge condition. The user's distinction is realized at the whole geometric-world level, not only at individual charged-cell addresses.
- **Route result:** achieved the requested binary discriminator in smooth compact complex geometry; the question of preserving smooth projectivity while breaking pure Hodge has a structural no-go (Hodge theory itself), not a deferred computational task.
