# GST Mathbox — exact three-operator graph-source uniqueness and tensor-rank two

- **Date:** 2026-10-20 (IST)
- **Kind:** actual CM projector source-complexity theorem
- **Base:** `b06812cf73bea53adb4720e0a53d3e1811ae914d`, active `research/gpt6-native-point-primitive-span-20261017`
- **Source module:** `GSTUniversalCMArithmeticObstruction.lean`
- **Proof commits:** `00f3952830db94994dcc452fde12beb40e6e1f9c` (insertion, parsing repaired at `81de6ca1cfe1d9bdf7abe02cd2e58f7655fb938e`), `3d0f73f14c056f0d8f01ec5597a42293f8dde064` (tensor-rank two theorem)
- **Revision-matched GH CI:** [#39313814935](https://github.com/kyo-oo/HC-PROOF/actions/runs/39313814935), **GREEN** for the uniqueness theorem at `81de6ca1cfe1d9bdf7abe02cd2e58f7655fb938e`; [#39314326642](https://github.com/kyo-oo/HC-PROOF/actions/runs/39314326642), **GREEN** for the full rank-two upgrade at `3d0f73f14c056f0d8f01ec5597a42293f8dde064`
- **Review:** Mathbox self-review, independent exact symbolic rank/determinant computation via Wolfram (`Det=20000`, `MatrixRank=2`)
- **Target contract:** universal rational Hodge cycles on every original smooth projective complex X. This record proves only a bounded CM-source coefficient theorem.

## The exact algebraic CM operators and simultaneous spectral interpolation

Let (T=[2+i]^*), (S=[1+i]^*) and (U=[i]^*) be genuine algebraic endomorphism pullbacks on the central CM abelian sixfold. After the parity filter ((1-U)/2), the pure Weil and even mixed spectral pairs may be chosen as

- pure Weil: ((T,S)=(-117+44i,-8i));
- even mixed: ((T,S)=(75+100i,8i)).

Seek an exact rational numerator (A(T,S)=a+bT+cS+dTS) normalized by (A|_{\rm Weil}=1), (A|_{\rm mixed}=0). Real and imaginary parts produce four scalar equations:

\[
\begin{aligned}
a-117b+352d&=1,\\
44b-8c+936d&=0,\\
a+75b-800d&=0,\\
100b+8c+600d&=0.
\end{aligned}
\]

They have the **unique** rational solution

\[
\boxed{
(a,b,c,d)=\left(\tfrac12,-\tfrac1{300},
\tfrac7{384},\tfrac1{3200}\right)
=\frac1{9600}(4800,-32,175,3).
}
\]

Every coefficient is nonzero, so all four basis words (1,T,S,TS) are necessary within **this fixed four-word frame**. This is exactly the preexisting successful projector

\[
\mathcal P(T,S,U)
=\frac{1-U}{19200}(4800-32T+175S+3TS).
\]

Lean formalizes the exact real/imag complex evaluation and the unique coefficient solution as `cmWeilSixfoldBilinearTSComplexEval`, `cmWeilSixfoldThreeOpBilinear_exact`, `cmWeilSixfoldThreeOpBilinearCoefficient_unique`, and `cmWeilSixfoldThreeOpBilinearAllFour_required`.

## A sharp tensor-rank obstruction

The numerator's coefficient matrix in the monomial bases (1,T) and (1,S) is

\[
M=\begin{pmatrix}4800&175\\-32&3\end{pmatrix},\qquad
\det M=4800\cdot3-175(-32)=20000\ne0.
\]

If it had one separated factorization ((a+bT)(c+dS)), then its matrix would have the form ((a,b)^{\rm T}(c,d)) and determinant zero. This contradicts the exact coefficient determinant. The corresponding Lean theorem is `cmWeilSixfoldThreeOpNumerator_not_one_separable_product`.

Conversely the explicit identity

\[
4800-32T+175S+3TS=(4800-32T)+(175+3T)S
\]

shows that **exactly two separable terms** suffice; `cmWeilSixfoldThreeOpNumerator_two_separable_terms` proves this as rational algebra.

**Precise nonclaim:** two separable algebraic operator words are not a semiregular perfect complex. The matrix rank does not prevent a genuinely coupled nonseparable sheaf, a more efficient construction with other endomorphisms, or a different representation of the same K₀ class.

## Interaction with real geometry

The existing seven opposite-sign CM graph incidence edges and their actual two-divisor W geometry supply known Ext² inputs. Our [graph structure-sheaf parity audit](2026-10-20-gst-graph-sheaf-ext-three-shift-parity-no-go.md) shows that a direct differential between opposite-parity *bare graph sheaves* cannot be made from their transverse Ext³ crossing classes. Thus the available geometric problem is genuinely to construct a complex incorporating the suitable auxiliary incidence supports and a square-zero Yoneda-compatible differential, and check its pure projected Chern character and Atiyah obstruction on the nonsplit period tangent.

The prior raw derived ideal (F) fails that Hodge-type tangent test by exact coefficient 124; algebraic rank-two interpolation does not circumvent the obstruction automatically. The full arbitrary-X target remains the same and has no new universal source-existence theorem from these computations.

## Attempt and evidence status

- **Outcome:** proved as written in Lean for the finite rational spectral system; independently exact arithmetic checked.
- **Source geometry:** named actual CM isogenies, with the existing repository geometric-comparison conditions, not unconstrained operators.
- **Route disposition:** short CM graph-word interpolation and rank-one tensor product route resolved; the 7-edge auxiliary-incidence coupling and arbitrary-original-X cycle generation remain active obligations.
- **Next discriminating construction:** an actual nonseparable derived incidence packet whose complete K₀ character is the existing 19,200-denominator pure Weil projector, followed by a non-split Atiyah/Kodaira–Spencer obstruction computation and canonical Betti comparison.
