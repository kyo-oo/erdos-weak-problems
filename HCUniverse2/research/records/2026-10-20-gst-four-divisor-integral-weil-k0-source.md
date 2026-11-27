# Mathbox GST — four integral CM divisor products and a pure perfect-K₀ Weil source

- **Date:** 2026-10-20 (IST)
- **Kind:** direct algebraic source construction, exterior proof, and geometric deformation discriminator
- **Branch:** `research/gpt6-native-point-primitive-span-20261017`
- **Proof base:** `0619f57b71ffb5328c5ade2ddb617ff34bb91958`
- **Edited Lean file:** existing `GSTUniversalCMArithmeticObstruction.lean`; mathematical additions at commits `713a5f04610f2ea81a0f4d78d5c034ecdb1dd0f6` and `71503b1a9c6b2b11fffbf7fc7d5983c1e6f132de`
- **Target:** the universal original-X canonical rational Hodge-to-Chow theorem. This record proves a new split-CM **source** result, not its nonsplit family extension or any arbitrary-X Chow existence.
- **Provenance:** exact exterior calculation with a separate pure-arithmetic exterior enumerator; Mathbox-style self-audit, not independent geometric referee review. GitHub Lean exact-SHA CI to be checked.

## 1. Actual algebraic divisor inputs

Let `E` be a complex elliptic curve with multiplication by `i`; let `A=E^6`, grouped into three surfaces `S_j=E_j×E_(j+3)`, `j=1,2,3`. Write `e_j,f_j` for the oriented integral degree-one basis on each elliptic factor.

Define the following **integral** codimension-one cohomology classes on each `S_j`:

[
A_j=e_j\wedge e_{j+3}+f_j\wedge f_{j+3},\quad
B_j=e_j\wedge f_{j+3}-f_j\wedge e_{j+3}.
]

These are classes of actual algebraic divisors, not freely introduced Hodge coordinates. The repository's existing diagonal difference `[F_{j,1}]+[F_{j,2}]-[\Delta_{j,j+3}]` has cross component `B_j`. The genuine CM automorphism `id×[i]` pulls that divisor class to the `A_j` direction. The two natural surface intersection identities follow by wedge expansion in complex orientation `e_j f_j e_{j+3} f_{j+3}`:

[
A_j^2=B_j^2=-2[p_j],\qquad A_j B_j=0.
]

These are integral top-class equalities on each smooth projective abelian surface.

## 2. FULL real/imaginary Weil plane from eight integer divisor products

Set

[
\Omega=\prod_{j=1}^{3}(e_j+i f_j)\wedge
\prod_{j=4}^{6}(e_j-i f_j),\quad
W_R=\Re\Omega,\quad W_I=\Im\Omega.
]

Reordering the six degree-one factors into elliptic **pairs** contributes exactly `-1` (three odd crossings). Each pair contributes `A_j-iB_j`. Thus

[
\Omega=-\prod_{j=1}^{3}(A_j-iB_j).
]

Expanding precisely three Gaussian factors gives two **integral** codimension-three Chow constructions:

[
\boxed{
W_R=-A_1A_2A_3 + A_1B_2B_3 + B_1A_2B_3 + B_1B_2A_3,
}
]
[
\boxed{
W_I=B_1A_2A_3 + A_1B_2A_3 + A_1A_2B_3 - B_1B_2B_3.
}
]

Each class is a sum of four explicit products of **genuine integral CM graph/fibre divisor classes on the original split sixfold**. The Lean ring theorems are `cmWeilCMIntegralFourRealDivisorProducts` and `cmWeilCMIntegralFourDivisorProducts`; the 12-generator exterior-to-Chow interpretation is an independently checked geometric calculation, not yet a Lean concrete Betti cohomology instance.

**Independent exact check:** represent exterior monomials by increasing subsets of the twelve integral symbols `e1..e6,f1..f6`, multiply using inversion signs, compute `Omega`, and compare real/imaginary components with the four divisor products. Each component has precisely 32 nonzero coefficients, all `±1`; there are `0` mismatches in both comparisons. The four-product basis constructions are integral and each contains a coefficient `±1`, proving both basis classes primitive **as elements of the ambient degree-six integral Betti lattice**, once the fixed chosen integral exterior basis is established.

Because each surface has `A_j²=B_j²=-2[p_j]` and `A_jB_j=0`, the distinct four triple products within each formula are mutually orthogonal and each has square `(-2)^3=-8`. Real and imaginary four-product parity types are also orthogonal. Hence, in the complex top orientation on `A`,

[
\boxed{W_R^2=W_I^2=-32,\quad W_R W_I=0.}
]

This matches the full independent 12-symbol exterior top-product enumeration. The entire rational exceptional Weil plane at **this split CM point** is therefore explicitly algebraic, with a signed rational combination of these two integral basis cycles giving any prescribed vector in that plane. This says nothing about the other Hodge classes at the split point.

## 3. Integral rank-zero perfect-K₀ source with NO excess Chern degrees

For either algebraic surface divisor `D=A_j` or `D=B_j`, choose a genuine integral line bundle `L_D` with `c₁(L_D)=D` (possible because `D` is an integral algebraic divisor), and a closed point `p_j` on `S_j`.

As the surface tangent bundle is trivial, `D^3=0` by dimension and `D²=-2[p_j]`, the true rational Chern character satisfies
[
\operatorname{ch}(L_D)=1+D+\tfrac12D²=1+D-[p_j].
]
Therefore the **integral virtual perfect** class
[
\boxed{Q_D=[L_D]-[\mathcal O_{S_j}]+[\mathcal O_{p_j}]\in K_0(S_j)}
]
has **pure** Chern character `ch(Q_D)=D`. No denominator, arbitrary Hodge target selector, or unexpected codimension-two character appears. On the smooth surface, all three terms are perfect, so signed direct sums/shifts produce an actual perfect representative.

External tensor products across the three different surface factors obey multiplicativity of Chern characters. Thus each four-term tensor product expression for `W_R` and `W_I` lifts to an **integral virtual perfect K₀ class on the actual split original** `A=E^6` with pure `ch₃=W_R` or `W_I` and **all other Chern-character grades zero**. The complete expansion uses at most `4×3³=108` elementary integral virtual summands per basis source before cancellations. This is a finite perfect-complex existence construction on the split fibre, not a deformation of an indecomposable or simple object.

The Lean theorem `cmWeilCMIntegralSurfacePointCorrection` proves the exact twice-Chern-character relation in an arbitrary commutative ring under `D²=-2[p]`; geometry that supplies this condition remains an explicit bridge.

## 4. Much smaller self-Euler, but no automatic nonsplit deformation

Previously the eight signed pure graph-source numerator had `ch₃=-4800 W_I`, square `-737280000`, and self-Euler `+737280000`. The new **primitive-integral** split perfect object instead has `ch₃=W_I` (or `W_R`) and thus self-Euler `+32`, under standard abelian HRR. The Lean certificate `cmWeilCMIntegralDirectDivisorEulerScaling` checks `32·4800²=737280000`.

For a *simple* perfect object realizing the smaller class, sixfold Serre duality only yields `dim Ext²≥15`, which is compatible with the 495-dimensional raw semiregularity target. The earlier massive obstruction-dimension bound was intrinsic to the **inflated graph numerator class**, not to the underlying rational Hodge direction. This is a major *architecture discriminator*, NOT an unobstructedness or existence theorem for a simple source.

**Essential limitation:** the individual cross divisors `A_j,B_j` generally cease to be type `(1,1)` in a nonsplit deformation; their *combined* real/imaginary Weil class remains of type `(3,3)` along a Weil-type family. An alternating perfect sum representing that class on the central split fibre does not follow formally to a holomorphic family. The next direct test is the genuine `At(F)⌟κ` on a coupled realization of one of these smaller integral `K₀` sources, together with the full canonical Betti comparison and all-period transport. Universal arbitrary-X primitive source generation remains open.

## Outcome and evidence status

- **Proved exactly in arithmetic/finite exterior algebra:** both four-product identities, 32 real/32 imaginary coefficients, no mismatches, the full `-32 I₂` Gram, and the integer source-scaling factor.
- **Mathematical geometric realization using explicit abelian divisors and standard line-bundle GRR:** both integral Chow cycles at the split CM point and corrected pure virtual perfect K₀ representatives there.
- **Lean kernel scope:** polynomial/Chern cancellation theorems in existing module; the actual CM elliptic schemes, their divisor line bundles, Betti cycle-class map, and K₀ tensor realizations are not yet Lean inhabitants.
- **Still unproved:** nonsplit Atiyah vanishing, compatible semiregular family, Hilbert spread, arbitrary original-X canonical primitive Chow source, and the final exact universal Hodge conjecture.
- **First unresolved implication:** find a genuinely coupled, geometrically realized perfect representative of the **smaller integral** `W_R/W_I` class that deforms over a non-split Weil-type period direction and prove its actual canonical Betti Chern class; don't assume the direct split tensor sums deform.
