# GST atomic source surgery: internal diagonal birth versus characteristic/self-diagonal closure

Date: 2026-10-21 (IST). Branch: `research/gpt6-native-point-primitive-span-20261017`. User-directed Mathbox research and Wolfram exact checking. No generic public-web search, no subagents, no local Lean.

**Correction (same-day adversarial review):** The first version conflated the tangent Chern divisor with its numerical degree as an identity in CH¹. The revised proof requires only canonical rational Betti/numerical equality. It does not assert the false Chow equality on arbitrary curves; the graph-source birth and verified rational intersection identities are unchanged.

## Target and direct result

The original target is the full rational Hodge conjecture on every original smooth projective complex X with the genuine canonical cycle-class map. This specific route tested the claim that GST's diagonal projector, Newton/Euler positivity, polarization and tangent-characteristic operations can force a new one-legged actual source.

**Outcome:** A sharp scheme-level no-go for the restricted characteristic/self-diagonal source recipes **and an independently constructed algebraic non-split graph source** on X=C×C, all genera g>0. This corrects the mistaken identification of a diagonal kernel on X×X with a new internal-graph cycle on X. It does not prove universal original-X source birth or refute Hodge.

## Real geometry and proof

Let C be smooth projective genus g>0, A=[point×C], B=[C×point], H=A+B, delta=[Delta_C], D=delta-A-B on X=C×C. Normal bundle N_(Delta_C/X)=T_C and genuine fiber intersections give

- A²=B²=0, A B=1, delta A=delta B=1, delta²=2-2g.
- H D=0, D²=-2g, signed primitive energy +2g.
- Under genuine rational Betti realization, cl(c1(T_X))=(2-2g)cl(H). For all rational a,b, the NUMERICAL intersection integral of (aH+b c1(T_X)) with D is zero. This is not rational Chow equivalence for arbitrary C: Pic0 differences may survive in CH1 while vanishing in Betti cohomology.

Theorem: start from O_X, O_X(H), T_X, and use finite rational K0 combinations, tensor, dual, Adams, exterior powers (on true vector bundles), and self-diagonal kernels (Delta_X)_*F with F from this generated algebra. Every output E from the unit has cl(ch1(E)) in Q cl(H) under canonical Betti realization. This is proved by rank/ch1 identities for tensor, dual, Adams and exterior powers and the exact projection formula T_((Delta_X)_*F)(G)=F tensor G. Hence all such outputs have zero numerical/Betti pairing with D and cannot have even the same Betti ch1 as D when g>0. No arbitrary graph/correspondence F is allowed as a concealed extra generator in this no-go.

**Explicit repair:** The actual internal diagonal graph is independent geometry. Let L_D=O_X(D). The rational algebraic virtual perfect-complex source E_D=([L_D]-[L_D^{-1}])/2 has ch(E_D)=D in CH*(X)_Q, since X is a surface and the even-degree Chern character cancels. Thus -int_X ch1(E_D) D=2g>0. This source is not an alpha-selected Chow witness; it is built directly from a specific actual graph subscheme.

Genus-zero discriminator: numerical D²=0 and the separation test correctly vanishes. At genus 1, norm=-2; genus 3, norm=-6.

## Wolfram exact independent check

Stateless Wolfram Language evaluator, exact symbolic inputs: `pair[u_List,v_List]:=Expand[u[[1]]v[[2]]+u[[2]]v[[1]]+u[[1]]v[[3]]+u[[3]]v[[1]]+u[[2]]v[[3]]+u[[3]]v[[2]]+(2-2g)u[[3]]v[[3]]]`, `h={1,1,0}`, `dGraph={-1,-1,1}`, `ct={a+(2-2g)b,a+(2-2g)b,0}`. Results: `pair[h,dGraph]=0`, `pair[dGraph,dGraph]=-2g`, `pair[ct,dGraph]=0`, `pair[ct,ct]=2(a+2b-2bg)^2`, `GramDet=-4g(a+2b-2bg)^2`. Pure-odd Chern test `((1+z+z^2/2)-(1-z+z^2/2))/2=z`. First scratch call accidentally used protected Wolfram symbol `I` and was rejected; immediately reran with `pair`, whose exact output had no messages. No numerical inference is used in place of the uniform proofs.

## Formal artifacts and revision-matched proof scope

- Existing `GSTPrimitiveProductTowerStabilization.lean` surgically extended with five Lean statements: `curvePair_tautological_graph_period_zero`, `curvePair_internalGraph_square`, `curvePair_internalGraph_escapes_tautological_periods`, `curvePair_internalGraph_native_period_nonzero`, and `curvePair_internalGraph_genus_zero_period`, with `#print axioms` checks. Lean verifies rational intersection algebra in the existing curve-divisor carrier, rather than constructing an arbitrary scheme.
- Lean commit: `0c22d62d43ab6fed1eb0c5e8c586bd14180b7c14`.
- GitHub Actions `GST Primitive External Product Birth` [#39516704173](https://github.com/kyo-oo/HC-PROOF/actions/runs/39516704173) — completed SUCCESS at `0c22d62`.
- GitHub Actions `GST Universal Surface Graph Primitive Augmentation` [#39516704179](https://github.com/kyo-oo/HC-PROOF/actions/runs/39516704179) — completed SUCCESS at `0c22d62`.
- [Existing LaTeX derivation extended](../derivations/GST_universal_source_existence_attempt.tex) with full real-scheme proof, generic characteristic-word closure, and construction of E_D; LaTeX commit `55553498b35ba0f43c9d8ac57803b6a92ee1387f`. No new LaTeX compiler or full scheme-level Lean geometry claim.

## Research decision

**Close the restricted self-diagonal/polarization/tangent-Chern-only route** as universally sufficient: it fails even on real C×C with g>0 although D is genuinely algebraic. Keep genuine *internal* graph, incidence, non-tautological perfect-complex, and arbitrary-X source routes open. Any purported upgrade must exhibit actual new input geometry and a nonzero one-legged canonical residual period; adding more diagonal-only operator iterations is no repair.

Self-review covered signs, genus=0 boundary, dimensions, distinction of Delta_X versus Delta_C, rational virtual K0 semantics and why the new graph is not an all-X theorem. No independent proof reviewer or universal Hodge proof is asserted.
