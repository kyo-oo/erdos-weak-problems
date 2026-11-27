# Mathbox GST — the projected integral CM Weil class forces massive Serre self-Ext pressure

- **Date:** 2026-10-20 (IST)
- **Kind:** new necessary geometric obstruction / bounded proof attempt
- **Branch:** `research/gpt6-native-point-primitive-span-20261017`
- **Proof base:** `641cd1e450d23fb820a38eb0f8ecf02a444ffdc5`
- **Lean implementation:** existing `GSTUniversalCMArithmeticObstruction.lean`, commit `427e2e7590c494fb7b706deb66026c81bd042af5`
- **Formalization scope:** exact eight-graph signed intersection fingerprint, numerical self-Euler, and conditional dimension inequalities proved in Lean. Geometric HRR, Serre-duality interpretation, and existence of a perfect object with the specified class are not instantiated by these integer theorems.
- **Original program target:** construct genuine canonical rational Chow representatives for every rational Hodge class on every original smooth projective complex variety, every codimension. This result concerns only the specialized abelian-sixfold projected-source route.

## The integral K0 source and its real Euler invariant

The three-operator CM graph frame on the central abelian sixfold (A=E^3\times E^3) has eight actual full Gaussian-kernel graph cycles (Z_v\subset A) and integer coefficients (n_v) with projected middle-Chern numerator

[
\Gamma=\sum_{v=0}^{7} n_v[Z_v],\qquad \Gamma/19200=\alpha.
]

The exact previously green 8-by-8 intersection fingerprint establishes, using the complex orientation,

[
\Gamma^2=-737280000,\qquad \alpha^2=-2.
]

Each graph is a union of translates of abelian threefolds with trivial normal bundle; under the standard scheme GRR identification, `ch(O_{Z_v})=[Z_v]` is concentrated in codimension three. A signed direct sum of shifted graph structure sheaves is a genuine central-fibre perfect complex representing the **integral** class \(\sum n_v[O_{Z_v}]\in K_0(A)\). Coupling by K0-neutral incidence summands does not change this class or its Chern character.

For **any** perfect complex \(F\) with precisely this Chern character (no other Chern grades), the tangent bundle of the abelian sixfold has Todd class one and the dual changes the codimension-three sign. Hirzebruch–Riemann–Roch therefore implies

[
\chi(F,F)=\int_A \operatorname{ch}(F^\vee)\operatorname{ch}(F)
=-\int_A\Gamma^2=737280000.
]

This is a structural invariant of the entire prescribed integral projected K0 class, not a property of one particular choice of incidence differential.

## The sixfold Serre-duality inequality

As (K_A\simeq\mathcal O_A), Serre duality for a perfect complex gives \(e_i=\dim_{\mathbf C}\operatorname{Ext}^i_A(F,F)=e_{6-i}\). Hence

[
737280000=2e_0-2e_1+2e_2-e_3.
]

Since \(e_1,e_3\ge0\),

[
\boxed{e_0+e_2\ge368640000}.
]

If the projected object is **simple** (\(e_0=1\)), then

[
\boxed{e_2\ge368639999}.
]

The complete raw Buchweitz–Flenner semiregularity target on this abelian sixfold has dimension

[
\sum_{k=0}^{4}\binom6k\binom6{k+2}=495.
]

Therefore any map from this self-Ext² space to that raw target has, **for a simple projected realization**, a kernel of dimension at least

[
\boxed{368639999-495=368639504}.
]

Even without simplicity, if \(e_2\le495\) then necessarily \(e_0\ge368639505\). Thus one cannot simultaneously insist on a low-dimensional endomorphism algebra and raw semiregularity injectivity for this entire exact integral class. The Lean theorems `cmWeilSixfoldThreeOpGraph_projectedSelfEuler`, `_CY6SerreExtPressure`, `_smallExtTwo_forcesLargeEnd`, `_simpleExtTwoLowerBound`, `_simpleRawSemiregularity_noInjection`, and `_simpleSemiregKernelPressure` certify these exact numeric consequences **of the stated Euler identity**.

## Interpretation and limits

- The earlier raw unprojected derived-pair test produced 576>495 candidate self-Ext² dimensions, conditional on derived descent. The present invariant is much stronger and applies to *every perfect object with the full integral projected pure Chern character*, irrespective of incidence architecture, provided the geometric HRR and Serre comparison are correctly instantiated.
- This is **not** evidence that the rational Hodge conjecture is false. Even within this CM source route, it does **not** show that the actual Atiyah–Kodaira–Spencer obstruction \(\operatorname{At}(F)\lrcorner\kappa\) is nonzero: the specific obstruction image could vanish inside an enormous raw Ext² space.
- The enormous dimension depends quadratically on the chosen integral numerator. The normalized rational class \(\alpha\) has square `-2`, but a rational divisor `1/19200` of a perfect complex is not itself necessarily a genuine integral perfect complex. A different, independently constructed smaller integral source frame could evade the particular numerical magnitude; the existing minimal-denominator theorem applies only to the stated eight-graph source frame.
- The central connected rank-144 lci incidence model may realize the requisite K0 class but cannot establish *raw* semiregularity injectivity in the simple-object regime. The correct next discriminating mathematical target is the actual **Atiyah obstruction image**, possibly after taking an independently justified reduced/trace-free obstruction theory, and then the full arbitrary-X original-Chow source.

## Evidence / continuation

- **Lean:** new mathematical implication compiled by the GitHub pinned workflow only when a completed run on exact commit `427e2e7590c494fb7b706deb66026c81bd042af5` is confirmed; pending at record creation. A historical GREEN is not verification of the new declarations.
- **Independent arithmetic:** \(2\cdot19200^2=737280000\); \(19200^2=368640000\); \(368640000-1-495=368639504\).
- **Review:** Mathbox-guided self-audit; no independent scheme-theoretic referee validation.
- **First unresolved implication:** construct a global central genuinely coupled projected perfect object and establish direct vanishing of the concrete Atiyah obstruction for the named nonsplit Weil tangent, without replacing this step by abstract semiregularity injectivity.
- **Program disposition:** specialized raw-semirergularity-injection route excluded in the specified simple integral-numerator setting; direct obstruction and the all-original-X primitive algebraic construction remain open.
