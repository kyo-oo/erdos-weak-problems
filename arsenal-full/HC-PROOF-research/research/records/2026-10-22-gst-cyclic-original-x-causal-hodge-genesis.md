# GST cyclic original-X causal Hodge genesis — all-arity geometric fold

- **Date:** 2026-10-22 IST
- **Kind:** Original-X-dependent geometric construction, uniform mixed/pure Hodge decomposition, exact symbolic audit.
- **Program:** GST rational Hodge; direct causal dimension-fold research route.
- **Base checkpoint:** `32ae4306b52ec915514e5022529ec3ae068cd9b4` on `research/gpt6-native-point-primitive-span-20261017`.
- **Target:** Realize the researcher's dimensionless General Space / higher causal fold intuition by actually changing realized geometry and computing when original-X-derived cohomology is pure Hodge or mixed Hodge. Not a reduction to another special-case Hodge conjecture.
- **Hypotheses:** Every connected smooth projective complex `X`, any integer fold arity `m>=2`, any extra Tate depth `N>=0`. Rational Betti mixed Hodge theory, actual finite projective cyclic quotient.
- **Nearest prior result:** `GST_causal_graph_double_fold_weight_emergence_2026-10-22.tex` constructs graph-loop Hodge and N-current channels and a Dwork monodromy example; arbitrary `X` was previously included primarily as a spectator factor. The current route acts nontrivially on `H^*(X^m)` using cyclic automorphisms of its factors.
- **Distinct mechanism:** The algebraic cyclic rotation of `X^m` is coupled to a **free rotation of the components of a projective m-gon nodal curve**; the rational cohomology of the quotient is computed by equivariant Kunneth and mixed-Hodge transfer. A smooth projective companion uses a torsion translation on an elliptic curve.

## Proven uniform mathematical formulas in the derivation

Let `B=X^m`, `G=C_m` act by cyclic factor rotation, `V_k=H^k(B,Q)`; negative-index groups vanish. The projective nodal quotient `Y_m=(B x D_m)/G` is dimension `m dim X+1` and has rational mixed Hodge decomposition

```text
H^k(Y_m,Q) = V_k^G [weight k] + V_(k-1)^G [weight k-1]
              + V_(k-2)(-1) [weight k].
```

The last term is the *full* `V_(k-2)` rather than its invariant subspace: `H^2(D_m,Q)=Q(-1)[G]` is the regular permutation representation, and `(V tensor Q[G])^G ≅ V`. This is an explicit check preventing an incorrect operator-invariant approximation.

For the genuine smooth projective `S_m=(B x E)/G` with torsion translation on `E`, the degree-k Hodge structure is pure:

```text
H^k(S_m,Q) = V_k^G + (V_(k-1)^G tensor H^1(E,Q))
              + V_(k-2)^G(-1).
```

Define `A=t^2 s^2 u v`, `P_X(t,s,u,v)` the degree/weight/Hodge polynomial, and the signed cyclic invariant polynomial

```text
I_m = (1/m) Sum_{j=0}^{m-1}
 [P_X((-1)^(L_j-1) t^L_j,s^L_j,u^L_j,v^L_j)]^g_j
g_j=gcd(m,j), L_j=m/g_j.
```

Exact all-arity equations:

```text
P_Y = (1+t) I_m + A P_X^m
P_S = (1+t s (u+v)+A) I_m
P_S-P_Y = t(s(u+v)-1)I_m + A(I_m-P_X^m).
```

The average of genuine algebraic graphs of cyclic automorphisms gives an idempotent Chow correspondence on `X^m x X^m`. Its Betti action realizes the `V_k^G` projector; it is not postulated as an abstract inverse to canonical cycle class.

A second nodal fold `Z_m=Y_m x D_1` satisfies `Gr^W_k H^(k+2)(Z_m,Q) ≅ H^k(X^m,Q)^G`, a genuine weight gap `delta=-2`. For **every** positive-dimensional original `X`, the cyclic symmetrization of its rational top point class in one tensor factor gives a nonzero diagonal class of type `(d,d)` in degree `2d+2` and weight `2d`. This is a non-pure diagonal class on a new **singular** projective world, not a counterexample on smooth projective `X`. Extra projective-space folds preserve `(chi,delta)`.

## Target-sensitive arbitrary-Hodge-class strengthening

The LaTeX proof has now been extended beyond the special top-point class. For EVERY rational `(p,p)` Hodge class `alpha` on the original `X`, its cyclic symmetrization `Theta_m(alpha)=Sum_i pr_i^* alpha` is a rational cyclic-invariant Hodge class on `B=X^m`. In positive cohomological degree it has an exact algebraic-section left inverse `s^*Theta_m(alpha)=alpha`; degree zero uses division by `m`. Combined with the double-weight-defect summand, this gives an injection from the full arbitrary-X rational Hodge fiber into `Gr^W_(2p) H^(2p+2)(Z_m(X),Q)` with `(charge,purityGap)=(0,-2)`, **without** assuming `alpha` is algebraic.

For the smooth projective companion `S_m`, finite étale transfer yields the canonically descended pure Hodge class `alphaHat` characterized by `q^*(alphaHat)=pr_B^*Theta_m(alpha)`. A proven exact equivalence is

```text
alpha lies in canonical Chow cycle image on X
  iff alphaHat lies in canonical Chow cycle image on smooth S_m.
```

Forward direction: from a genuine `W in CH^p(X)_Q`, construct `W_B=Sum_i pr_i^*W` and `WHat=(1/m) q_* pr_B^*W_B`. Reverse direction: any genuine `WHat` on the smooth folded world pulls back via finite étale `q`, restricts to `B` along an elliptic-fiber point, and restricts along `s:X->X^m`, yielding a **literal original-X Chow cycle** with canonical class `alpha`. This supplies an exact native return correspondence conditional only on a source in the folded world, not an assumed free Hodge-to-Chow map.

The result therefore provides both exact outputs envisioned by the user's intuition: a smooth pure algebraicity-faithful dimension fold and an algebraic-topology-changing singular fold that genuinely shifts the same Hodge target to a lower weight. It does not assert automatic existence of the folded source `WHat`.

## Checks, review, limitations

- **Mathbox method:** bounded route, normalized domain and source/target, exact signs for graded permutations, projective quotient and rational transfer checked, explicit finite examples, separate self-audit of the theorem's interpretation.
- **Exact Wolfram:** executed stateless symbolic code, then committed reproducible `research/computations/gst_cyclic_original_X_hodge_fold_2026_10_22.wl`. For elliptic `X`, invariant polynomial dimensions at `m=1,2,3,4,5` are `4,8,24,64,208`; all computed coefficients nonnegative. For `m=2`, singular `Gr^W_1 H^2` has Hodge polynomial `u+v`; singular `Gr^W_2 H^2` has `3uv`; smooth `Gr^W_2 H^2` has `u^2+5uv+v^2`. Double singular fold `Gr^W_2 H^4` is `2uv` (elliptic `X`) and `uv` (`X=P1`). All compared exact symbolic expressions passed.
- **Evidence label:** uniform geometric/cohomological proof self-reviewed in LaTeX; finite tests reproduced with exact rational Wolfram; **not Lean-kernel-verified** because the required scheme-level MHS/quotient construction is not encoded in the current Lean development.
- **First unfinished bridge to classical Hodge target:** a native one-legged Chow cycle on the untouched `X` for an arbitrary specified rational `(p,p)` class. Existing cyclic *two-legged* Chow projector on `X^m` does not create this.
- **No public-web search**, no local Lean and no GitHub workflow run for this mathematics-first LaTeX stage.

## Authoritative artifacts

- [Full proof derivation](../derivations/GST_cyclic_original_X_causal_hodge_fold_2026-10-22.tex)
- [Reproducible exact Wolfram audit](../computations/gst_cyclic_original_X_hodge_fold_2026_10_22.wl)
- [Earlier dimension-fold derivation](../derivations/GST_causal_graph_double_fold_weight_emergence_2026-10-22.tex)
- Lean architectural source files already inspected: `GSTGraphV2UnboundedHigherCausality.lean`, `GSTGradedWorldAlgebra.lean`, `waves/GSTNCohomologyV3.lean`, `GSTGeneralSpaceCohomology.lean`.
