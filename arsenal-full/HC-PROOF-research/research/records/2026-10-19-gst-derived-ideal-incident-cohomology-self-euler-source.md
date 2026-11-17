# Mathbox GST — one derived CM graph-ideal source: incidence cohomology, self-Euler cancellation, and exact Weil-period compiler

- **Date:** 2026-10-19
- **Kind:** direct mathematical construction and self-audit
- **Original program target:** the full rational Hodge conjecture on every original smooth projective complex X; this record is a bounded, central Weil-sixfold source construction.
- **Base:** `e356bd44715e8e486941ef7f1ff73c6838981a68`, on `research/gpt6-native-point-primitive-span-20261017`
- **Lean commits:** `1a155500dc14dedee0c454e67940372b2fd84da7`, `66bb014c1306c142b6205aa5ed470c1dddcad5ae`, both in existing `GSTUniversalCMArithmeticObstruction.lean`.
- **Verification:** independent exact Wolfram factorization and 2×2 rational reconstruction. The new revision's pinned GitHub Lean job must be checked by its **own SHA**; a previous GREEN run does not verify these new declarations.

## Actual graph-ideal perfect object on the central CM sixfold

On A=E³×E³, let Z₀ and Z₁ be the two transverse regular codimension-three graph abelian subvarieties defined by the Gaussian slopes 1 and 2+i. Their scheme-theoretic intersection P consists of 4³=64 reduced points. Let I₀ and I₁ be the actual coherent ideal sheaves and construct the genuine perfect complex

`F = RHom_A(I₀,O_A) ⊗^L I₁.`

Grothendieck duality in odd codimension three gives Ext³_A(O_{Z₀},O_A)=O_{Z₀}, and Ext^i=0 for i≠3. Consequently the derived dual I₀^∨ has cohomology sheaves H⁰=O_A and H²=O_{Z₀}. Transversality yields Tor_i^A(O_{Z₀},O_{Z₁})=0 for i>0 and hence Tor_i^A(O_{Z₀},I₁)=0 for i>0. The induced derived tensor spectral sequence therefore gives **the actual incidence cohomology sheaves**

`H⁰(F) = I₁,     H²(F) = I_{P/Z₀},     H^q(F)=0 for q≠0,2.`

The middle object is the genuine ideal of the **64-point intersection inside the graph threefold**, not an abstract signed class. Its alternating K₀ character is

`[F]=[I₁]+[I_{P/Z₀}]=1+[O_{Z₀}]-[O_{Z₁}]-[O_P].`

By GRR and the trivial tangent/normal bundles of the abelian graph subgroups:

`ch(F)=1+z₀-z₁-t,`  with `t=z₀z₁=[P]`, and `z₀²=z₁²=0`.

## New unconditional algebra identity / geometric Euler consequence

Set `C=1+z₀-z₁-z₀z₁`. Codimension-three duality changes the signs of z₀,z₁ and preserves their degree-six intersection term. Hence

`C·C^∨=(1+z₀-z₁-z₀z₁)(1-z₀+z₁-z₀z₁)=(1-z₀²)(1-z₁²)=1.`

As Todd(T_A)=1, Hirzebruch–Riemann–Roch on the genuine sixfold gives

`χ_A(F,F)=∫_A ch(F^∨)ch(F)=∫_A 1=0.`

The new ring identity and its square-zero specialization are Lean theorems `cmTwoPlusIGraphDerivedIdealPair_selfEuler_factorization` and `cmTwoPlusIGraphDerivedIdealPair_selfEuler_unit`. The geometric inference uses GRR and the graph's actual trivial normal bundles; Lean has not instantiated the full scheme-level derived category in this module.

## Exact target-dependent arithmetic: two honest central-period directions

The source's exact Weil periods are z=(352,944), and the genuine CM [2+i] action gives Tz=(-14750000,-220544). Their determinant is

`det[z,Tz]=13846368512>0.`

For any rational target (a,b), set

`c₀=(-13784 a+921875 b)/865398032,`
`c₁=(-59 a+22 b)/865398032.`

An exact symbolic verification gives `c₀ z+c₁ Tz=(a,b)` identically. The new Lean theorem is `cmTwoPlusIGraphDerivedIdealPair_exactWeilPeriodCompiler`. These are coefficients of actual algebraic **central graph-derived K₀ sources** once the already-described central GRR/Betti comparison is instantiated; they are not a selector of unknown target Chow preimages.

## Consequence for the NONSPLIT construction route

The existing seven-bridge/eight-graph signed projector is no longer required to *generate a nonzero central Weil orbit*. The single connected derived tensor F already has two rationally independent genuine central Weil period directions, and it carries an explicit two-term incidence cohomology description. This is a narrower potential deformation input.

The precise remaining test is the Atiyah/Kodaira–Spencer obstruction in **actual Ext²_A(F,F)**, with its 64-point incidence Postnikov coupling, and the semiregularity map. `χ(F,F)=0` is an index identity, not Ext²-vanishing or smoothness of the relative moduli. If F deforms with its canonical Chern character across the nonsplit Weil period family, its CM orbit and these rational coefficients construct the Weil-sector cycles there; proving that deformation is the genuine unsupplied geometric implication. The global all-X goal has stronger quantifiers.

- **Outcome:** exact K₀/Chow identities and explicit rational period reconstruction; geometrically derived two-term incidence carrier; deformation claim still conditional.
- **Review:** self-audit only, exact algebra also Wolfram-checked.
- **Next discriminating computation:** calculate trace-free Ext²_A(F,F) from the actual two-term incidence Postnikov complex and test the Atiyah obstruction under a non-split Weil-type Kodaira–Spencer direction, rather than comparing χ or a 2×2 Gram determinant.
