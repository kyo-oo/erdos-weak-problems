# GST arbitrary-bundle Hopf Euler law and canonical original-X Chow-defect reflection

- **Date:** 2026-10-22
- **Research branch:** `research/gpt6-native-point-primitive-span-20261017`
- **Source revision:** `cc54c00bcdb0d879d751299138232673ea0d4d49`
- **Mathematical source:** [Extended original compact-causal LaTeX derivation](../derivations/GST_compact_causal_hopf_fold_hodge_dichotomy_2026-10-22.tex), section “Arbitrary-bundle GST parity law and canonical Chow-defect reflection”
- **Verification scope:** Geometric proof written and self-reviewed from standard oriented sphere-bundle Gysin, projective bundle Chow formula and canonical Betti functoriality. No Lean files changed or GitHub Actions compilation claimed for this geometric extension.

## Sharp full-original-X generalization

Let `X` be any connected smooth projective complex variety, `E` any algebraic rank `r>=2` vector bundle, and `0<q<1`. Construct both equal-complex-dimensional worlds:
- `P_E=P(O_X ⊕ E)`: smooth projective, pure rational Hodge structure.
- `H_E=(E\0_X)/q^Z`: smooth compact complex, smoothly `S(E) × S1`, with odd `b1(H_E)=b1(X)+1`.

For every `j`, true rational cohomology satisfies

`ker(pi_H^*:H^j(X,Q)->H^j(H_E,Q))=c_r(E) cup H^(j-2r)(X,Q)`.

Thus **all** original-X rational cohomology is retained under Hopf pullback **if and only if** the rational top Chern class `c_r(E)` vanishes. This is stronger than the original sufficient trivial-summand condition. Exact example: `X=P1`, `E=O(-1)⊕O(-1)` has no global holomorphic vector section, yet `c2(E)=0`, all original Betti cohomology survives and `b1(H_E)=1`.

## All-codimension canonical defect identity

For `Hdg_Q^p(X)=H^(2p)(X,Q)∩H^(p,p)`, let `D^p(X)=Hdg_Q^p(X)/im(cl_X^canonical)`. The *actual projective-bundle formula in both rational Chow and rational Hodge theory* yields

`D^p(P_E) ≅ ⊕_(i=0)^r D^(p-i)(X)`,

where negative/out-of-range codimensions contribute zero. Thus the full rational Hodge conjecture is true on `P_E` **if and only if** it is true on `X`. Moreover, the distinguished algebraic section `s:X->P_E` from `O_X⊕E->O_X` satisfies `s^*pi_P^*=id`; if an algebraic Chow representative `Z` for `pi_P^*(alpha)` is genuinely constructed upstairs, the actual original-X cycle `s^*Z` represents `alpha` canonically downstairs.

## Logical consequence for the original target

This sharp theorem pinpoints why the compact Hopf bifurcation does **not** itself certify original-X universal rational Hodge algebraicity or rule out its counterexamples: the Hopf branch's parity obstruction exists independently of `D^p(X)`, and the projective branch preserves `D^p(X)` exactly. The positive original-X return is a *real Chow pullback*, not a fictitious Hodge-to-Chow choice; using it to settle the universal problem requires a separately established algebraic source for `pi_P^*alpha`, not merely the existence of a pure Hodge structure on `P_E`.

**Outcome:** all-X arbitrary-bundle geometric upgrade proved in LaTeX, no new universal Hodge source claimed; exact canonical return available once an independently produced genuine upstairs cycle exists.
