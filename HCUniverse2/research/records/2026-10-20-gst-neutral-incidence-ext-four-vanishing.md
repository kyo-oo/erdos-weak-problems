# Mathbox GST — a K₀-neutral CM incidence packet with vanishing first Yoneda obstruction

- **Date:** 2026-10-20 (IST)
- **Kind:** bounded, explicit derived-geometric construction route and obstruction test
- **Program target:** construct canonical original-X Chow representatives for every rational Hodge class on every smooth projective complex variety; this record concerns only a CM central sixfold test
- **Branch and starting checkpoint:** `research/gpt6-native-point-primitive-span-20261017`, `7ecb19aba52b17753e97d17f9a56f6f94f450c5a`
- **Lean developments:** `GSTUniversalCMArithmeticObstruction.lean`, `6d983f7b5d1663a0156d23c876fa206109d8ab07` (projector frame and all-pairs Ext³ parity), `fd8b62b7731d636a6d67ded172c50a874d285f15` (three-step Ext² parity and cancelling intermediate K₀ pair)
- **Verification:** [GitHub run #39324907507](https://github.com/kyo-oo/HC-PROOF/actions/runs/39324907507) and [#39325431670](https://github.com/kyo-oo/HC-PROOF/actions/runs/39325431670), both GREEN on their exact proof SHAs. The scheme-level Ext and twisted-complex construction below are mathematical derivations, **not Lean-derived-category formalizations**.
- **Previous restrictions:** [bare graph Ext³ parity](2026-10-20-gst-graph-sheaf-ext-three-shift-parity-no-go.md), [transverse graph ideals](2026-10-20-gst-transverse-graph-ideal-ext-local-to-global.md), and [raw graph-derived Hodge leak](2026-10-20-gst-derived-cm-graph-hodge-variation-obstruction.md)
- **Review provenance:** Mathbox-guided self-review only; no independent review of the derived-category enhancement

## 1. The actual fourfold auxiliary carrier

Work on the central CM abelian sixfold `A=E_x^3 × E_y^3`, where `End(E)` contains `Z[i]`.

Define actual graph abelian threefolds

`Z₊={x₁=y₁,x₂=y₂,x₃=y₃}` and

`Z₋={(2-i)xₖ=(2+i)yₖ, k=1,2,3}`.

Choose the actual codimension-two abelian fourfold

`W={x₁=y₁,x₂=y₂} ⊂ A`.

Thus `Z₊⊂W`. Meanwhile the intersection `Y=W∩Z₋` satisfies `(-2i)x₁=(-2i)x₂=0` and the independent third-pair graph relation. Since `|-2i|²=4`, there are four two-torsion solutions in each of the first two pairs. The remaining third pair is a connected elliptic graph (the Gaussian coefficients `2-i`, `2+i` generate the unit ideal). Hence, as a reduced complex scheme,

`Y ≅ E[2]² × E ≅ ⨿_{16} E`.

This is an **actual one-dimensional intersection**, not a 16-dimensional vector-space surrogate.

## 2. The key Ext²/Ext³/Ext⁴ calculation

`W→A` is a regular immersion of codimension two with trivial normal bundle. Its two defining equations restrict to a regular sequence on `Z₋` because `Y` has the expected codimension two inside `Z₋`. Dualizing the actual two-variable Koszul resolution gives

`sheafExt_A^q(O_W,O_Z₋)=O_Y` for `q=2`, and zero for `q≠2` (the trivial normal bundle removes a line twist).

Only one row of the local-to-global spectral sequence survives. Since `Y` is a disjoint union of 16 elliptic curves,

`Ext_A²(O_W,O_Z₋)=H⁰(Y,O_Y)≅C¹⁶`,

`Ext_A³(O_W,O_Z₋)=H¹(Y,O_Y)≅C¹⁶`,

and decisively

**`Ext_A⁴(O_W,O_Z₋)=H²(Y,O_Y)=0`.**

For `Z₊⊂W`, the same Koszul resolution becomes a *zero-differential* complex after restricting to `Z₊`. Its top normal exterior component supplies a nonzero class `α∈Ext_A²(O_W,O_Z₊)`. Restricting to `W` itself likewise supplies a nonzero top normal class `ψ∈Ext_A²(O_W,O_W)`. Choose any nonzero `β∈Ext_A²(O_W,O_Z₋)`.

These are conditional only on the stated standard scheme/Koszul/cohomology identifications for the explicitly defined smooth subgroups; no target Hodge preimage is an input.

## 3. A minimal four-object connected twisted packet

Use four true perfect objects with cohomological shifts:

- `O_W[-1]` (negative K₀ sign);
- `O_W[0]` (positive K₀ sign);
- `O_Z₊[0]` (positive K₀ sign);
- `O_Z₋[1]` (negative K₀ sign).

The classes `α,ψ,β` define candidate total-degree-one arrows

`O_W[-1] --α--> O_Z₊[0]`,

`O_W[-1] --ψ--> O_W[0] --β--> O_Z₋[1]`.

The only composable pair is `β∘ψ`, which has total degree two and lies in

`Hom²(O_W[-1],O_Z₋[1])=Ext_A⁴(O_W,O_Z₋)=0`.

Therefore the composite is **nullhomotopic**. In a standard dg enhancement of `Perf(A)`, a chosen nullhomotopy provides the direct higher correction `O_W[-1]→O_Z₋[1]` needed for the Maurer–Cartan / square-zero twisted differential. There are no longer directed paths in this four-object pattern. This supplies a concrete mechanism for satisfying the first differential-composition equation; it is not a free assertion that all abstract Ext² elements automatically glue.

The associated alternating Grothendieck class, independent of the chosen differential, is exactly

`-[O_W]+[O_W]+[O_Z₊]-[O_Z₋]=[O_Z₊]-[O_Z₋]`.

Thus the two auxiliary incidence copies are **K₀-neutral**, while their nonzero Ext² arrows can produce an actual nonsplit derived incidence packet. The presence of arrows does not alone prove indecomposability or smooth deformation of the resulting object.

## 4. Why this does not yet deform or prove Hodge

This single-edge packet has the unprojected graph difference as its middle Chern character. Its recorded first-order non-`(3,3)` Hodge leakage of 124 persists, because altering differentials without changing K₀ cannot change the rational Chern character. So this packet **cannot itself be the nonsplit all-period Weil source**.

To obtain a candidate with the right invariant Chern character, the same incidence construction must be adapted to the complete eight-support *pure projected* class

`(4800,-32,175,3,-4800,32,-175,-3)/19200`.

For each opposite-sign edge the truncated positive graph equations give a candidate `W_e`; when its intersection with the negative graph is 16 elliptic components, the same `Ext⁴(W_e,Z_-)=0` mechanism can address local Yoneda products. But the large graph multiplicities demand a genuine **full-coupling / no-leftover-split-summands** check, plus the complete global Atiyah/Kodaira–Spencer obstruction and canonical Betti identification. Seven incidence supports with only one connecting copy each do not prove that 10,020 graph summands are all coupled, semiregular or transportable.

## 5. Result classification and continuation

- **Proved mathematically under explicit regular-immersion/Koszul facts:** the central intersection `Y≅⨿₁₆E`; the `Ext²=C¹⁶`, `Ext³=C¹⁶`, and `Ext⁴=0` profile; the resulting nullhomotopy condition and K₀ cancellation for a four-object incidence packet.
- **Lean proved and GitHub CI passed:** minimal coefficient denominator in the chosen source frame, all eight-graph parity restriction, two-/three-Ext²-step parity, and two-copy K₀ cancellation; these are algebraic/finite statements, **not** the geometric Ext identifications.
- **Still unproved:** an eight-graph strongly coupled semiregular family, all-period algebraic pure Weil cycles, canonical cycle-class comparison, and the arbitrary-X all-Hodge-class assertion.
- **Next discriminating mathematical step:** construct a rank-aware incidence diagram in which each signed multiplicity block is genuinely coupled; compute `At(G)⌟κ` for the complete projected object under the known mixed nonsplit tangent. Any such packet must preserve the projector's entire K₀ character and prove actual vanishing of deformation obstruction; trace/Chern cancellation alone is insufficient.

**Disposition:** this bounded local square-zero incidence route has a nontrivial constructive mechanism; full projected all-period and arbitrary-X routes remain open.
