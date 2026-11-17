# GST all-graph higher causal holonomy: verified arithmetic and geometric source birth

- **Date:** 2026-10-22 IST
- **Kind:** Mathbox research-program + bounded research-attempt + self proof-audit + Wolfram exact computation
- **Program/route:** Full rational Hodge conjecture via GST original-X causal-dimensional geometry
- **Base checkpoint:** `31e86c2126118e7783af216430a7b4d1be584579`; branch `research/gpt6-native-point-primitive-span-20261017`
- **Target:** Turn GST's dimensionless General Space / arbitrary causal world births into genuine geometric Hodge-type production, acting nontrivially on complete rational cohomology of arbitrary original smooth projective X. Do not replace the immutable original-X canonical Chow cycle target.
- **First uncertain implication:** Can multiple actual twisted graph identifications create full arbitrary-original-X cohomological directions when their common holonomy-invariant subspace is zero? Can those signals be recovered rather than just counted?
- **Changed input:** Earlier single cyclic world fold and Dwork monodromy only; now arbitrary connected causal graph with independently twisted node identifications induced by genuine algebraic automorphisms of X^m, plus reciprocal-loop return. This is not another finite CM/K3 testbed.
- **Types:** Original smooth connected complex projective X; B=X^m; H^q(B,Q) rational pure Hodge structure; finite holonomy graph Γ (r vertices, e nodes, g=e-r+1); actual projective pinched scheme Y; mixed-Hodge Gr^W of ordinary rational singular Betti cohomology; genuine algebraic automorphisms preserving canonical Chow classes.
- **Status:** mathematical derivation self-reviewed; finite rational computations executed in Wolfram; targeted Lean edit committed and its current GitHub Actions outcome must be matched by SHA.

## Exact derived all-graph law

For twisted Hodge-incidence `delta_q: H^q(B,Q)^r -> H^q(B,Q)^e`, the actual normalization sequence gives only the following mixed-Hodge **associated graded** decomposition:

```text
Gr^W_(k-1) H^k(Y,Q) = coker delta_(k-1)
Gr^W_k H^k(Y,Q) = ker delta_k + H^(k-2)(B,Q)(-1)^r.
```

No unproved mixed-Hodge splitting is asserted. Rank-nullity plus spanning-tree holonomy gives, for EVERY q,

```text
dim coker delta_q = (g-1)*dim H^q(B,Q) + dim H^q(B,Q)^Hol(Γ).
```

Even when joint holonomy fixed-space vanishes, two causal loops produce at least dim V independent new nonpure sectors.

For total degree/weight/Hodge polynomial `P_B`, let `A=t²s²uv` and `P_K` denote invariant-sector polynomial. Then

```text
P_Y = (1+t) P_K + (r*A + (g-1)*t) P_B.
```

For cyclic factor permutations on B=X^m, `P_K` is explicitly computed from the complete graded Koszul-signed totient character average (equation 5 in derivation). A **genuine smooth projective** genus-g companion defined via an étale cyclic cover and the same holonomy has pure Hodge polynomial

```text
P_S = (1+A)*P_K + t*s*(u+v)*((g-1)*P_B+P_K).
```

These are two geometric realizations of the input holonomy, not an asserted flat smoothing.

## Original-X arbitrary Hodge target and all-depth result

For reciprocal causal holonomies T and T^{-1} on two independent loops define `delta(v)=((T-I)v,(T^{-1}-I)v)`, `return(a,b)=a+Tb`, `section(v)=[(v,0)]`. Exact identities:

```text
return . delta = 0
return . section = id.
```

The resulting cokernel contains the **whole** Hodge structure of H^q(B), not only invariant vectors. The map from **every rational (p,p) class alpha on arbitrary original X** by `pr_1^*`, followed by section and geometric normalization boundary, injects into `Gr^W_(2p) H^(2p+1)(Y,Q)`, with exact return on X via a point-insertion. For every h>=1, product with h−1 actual nodal rational curves gives degree `2p+h`, weight `2p`, signed charge 0 and **unbounded purity gap −h**, with full polynomial `P_Y (1+t+A)^(h-1)`. This is a genuine mixed-Hodge realization and does not constitute a Hodge counterexample for smooth projective X.

The original-X algebraic-edge-label class image has a precise equivalence under reciprocal section and return: a class is algebraically labelled on source node B iff its embedded cokernel class admits algebraic edge labels. This does **not** make the weight-shifted ambient class the canonical Chow class of a singular projective variety. It preserves the unknown original-X native Chow existence question.

## Adversarial test with zero common invariant vectors

Let E elliptic, B=E×E and V=H¹(B,Q) of dimension four. The distinct genuine algebraic involutions `swap` and `[-1]∘swap` induce T1=S and T2=−S on V. The common fixed space is ZERO, whereas `rank delta=4` and `dim coker=4`; the explicit exact rational projectors `P_+=(I+S)/2`, `P_-=(I-S)/2` give `R(a,b)=P_+ a−P_- b`, `section(v)=(P_+v,−P_-v)`, `R delta=0`, `R section=I`. This rejects the incorrect belief that absence of invariant vectors forces an empty causal-birth sector.

## Reproducibility and evidence

- [Full geometric LaTeX derivation](../derivations/GST_all_graph_causal_holonomy_hodge_birth_2026-10-22.tex)
- [Executed exact Wolfram script](../computations/gst_all_graph_causal_holonomy_2026_10_22.wl)
- [Existing GST causal Lean module modified](../../GSTGraphV2UnboundedHigherCausality.lean) — `reciprocalCausalFoldBoundary`, `reciprocalCausalFoldReturn`, `reciprocalCausalFoldSection`, `reciprocalCausalFold_return_boundary_zero`, `reciprocalCausalFold_return_section`, `reciprocalCausalFold_section_not_boundary`.
- **Wolfram:** 24/24 exact cyclic holonomy rank trials (`m=2..7,g=2..5`), 12/12 exact elliptic full-polynomial pairs (`m=2..4,g=1..4`), exact distinct-involution matrices and return/section identities. No random seeds, approximations or floating point.
- **Mathbox proof-audit:** The geometric output is a weight-graded mixed Hodge structure on a **singular projective** scheme, not a pure rational Hodge class on smooth X. The rank law only establishes cohomological directions, not native cycle existence. Cyclic-cover smooth companion formula requires finite cyclic holonomy; noncyclic involution example is used only for the graph rank and return laws. No original-X Chow-to-Betti equality is invented.
- **Lean:** GitHub Actions compilation must be audited at the exact Lean-source commit `eabd746b5863bf073ece33981585163697350350`; neither a new mathematical-geometric theorem in LaTeX nor symbolic Wolfram checks count as a Lean kernel proof of mixed Hodge theory. GitHub Actions job `39773216733` was **in_progress** on first observation, not yet claimed green.
- **Next mathematical implication:** A noncircular truly algebraic one-legged original-X cycle born from the causal geometry, rather than a new mixed-Hodge carrier for an arbitrary cohomological class. The full rational Hodge target remains unchanged.

**Disposition:** Successful all-graph causal/MHS and rational-return mathematical route under stated geometric inputs; original target not claimed proved. **No local Lean installation and no public web search.**
