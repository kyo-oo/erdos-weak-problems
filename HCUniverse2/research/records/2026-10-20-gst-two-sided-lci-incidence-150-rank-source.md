# Mathbox GST — two-sided lci incidence and connected rank-150 CM source packet

- **Date:** 2026-10-20 (IST)
- **Kind:** new geometric source candidate, exact rank optimization, explicit coefficient realization, and bounded obstruction audit
- **Program target:** the original full rational Hodge conjecture on every smooth projective complex original (X), every (p), and every rational Hodge α; this record constructs only a central-CM-sixfold incidence candidate
- **Branch:** `research/gpt6-native-point-primitive-span-20261017`
- **Base:** `0702e922c01fca4082e995de4aca39120a20945b`
- **Lean module (modified in place):** `GSTUniversalCMArithmeticObstruction.lean`
- **Proof commits:** `33290a883d08dd0299fe81bf4c7024193abdcf56` (rigid 503 smooth-incidence rank), `8ca324b6dcee5db47d834ccafb13f09075692323` (new 150 lci budget), `35ff814a9e0817b484bcfb10acc4363968b5d136` (explicit injective 35-channel addresses; corrected one redundant tactic), `a06a935c0dad92244c2afac8ff596412fb326731` (all-edge occupancy)
- **Pinned GitHub Lean CI:** [#39328526813](https://github.com/kyo-oo/HC-PROOF/actions/runs/39328526813), [#39329235244](https://github.com/kyo-oo/HC-PROOF/actions/runs/39329235244), [#39330235233](https://github.com/kyo-oo/HC-PROOF/actions/runs/39330235233), [#39330646306](https://github.com/kyo-oo/HC-PROOF/actions/runs/39330646306): successful at their corresponding source revisions. Earlier draft `7ae2fed` failed on an inert `dsimp` tactic and was repaired in `35ff814`.
- **Review:** Mathbox-guided self-review, not independent derived-category review. The CI checks Lean arithmetic/linear encodings; the scheme-level Ext groups and twisted-complex interpretation below are geometrical derivations, not Lean-inhabited derived-category objects.

## 1. Geometric change, not a rewording of the previous 503-bound

The previous smooth incidence abelian fourfold `W={x1=y1,x2=y2}` contained the positive graph and met the negative one in 16 elliptic curves. Its two endpoint `Ext²` capacities were 10 and 16, giving a sharp connected numerical rank budget **503**. The new theorem `cmWeilSixfoldIncidence_optimal_rank_forces_backbone` further proves every 503-unit assignment needs at least **295** units on edge 04, and exactly saturates its four positive vertex ranks. That calculation has not been reinterpreted as a bound on all incidence sheaves.

For an opposite-sign edge `e=(v,w)` between two actual codimension-three CM graph abelian subvarieties `Z_v,Z_w` on `A=E_x³×E_y³`, let `D_{v,i}`, `D_{w,i}` be their graph-kernel divisors on the `i`th coordinate pair. Define a different algebraic carrier

`W_e = (D_{v,1}+D_{w,1}) ∩ (D_{v,2}+D_{w,2})`.

The equations come from two **different** elliptic coordinate pairs, so their product sections form a regular sequence. This is a codimension-two local complete intersection in smooth `A`, although it can be reducible and singular. Both `Z_v` and `Z_w` are contained in `W_e`, and `O_{W_e}` is perfect by its length-two Koszul resolution.

The branch's exact Gaussian winding-one tree certificate establishes the transverse degree-four intersection on an elliptic coordinate for each of the seven edges. On either graph `Z ≃ E³`, the two restricted Koszul-dual line bundles have degree 4 on the respective first and second elliptic factors. Their differentials **vanish on Z** because both defining sections vanish there.

## 2. Exact two-sided Ext profile, including the obstruction target

Writing `L1=pr1*L4`, `L2=pr2*L4` on `E³` and using elliptic Riemann–Roch and Künneth, the resulting actual global Koszul hypercohomology candidate is

```
Ext^k_A(O_We,O_Z)
  = H^k(Z,O_Z) ⊕ H^(k-1)(Z,L1 ⊕ L2)
                 ⊕ H^(k-2)(Z,L1⊗L2).
h^k(O_E³)    = C(3,k)
h^k(Li)      = 4 C(2,k)
h^k(L1⊗L2)  = 16 C(1,k)
Ext profile  = (1,11,35,25,0,0) for k=0,...,5.
```

In particular, at **either** endpoint `dim_C Ext²=3+16+16=35` and `Ext⁴=0`. The exact numeric profile is already proved in `cmWeilSixfoldMinimalIncidence_fullExtProfile`; its identification with the newly specified lci `W_e` is a separate geometric formalization obligation. A 35-dimensional coefficient space does **not** by itself guarantee a family of geometrically compatible arrows.

## 3. Sharp connected seven-edge rank: 150

The tree edges in the fixed repository order are `01,04,12,34,45,06,07`. Positive multiplicities at vertices `0,2,3,5` are `4800,175,3,32`; negative ones at `1,4,6,7` are `32,4800,175,3`. A rank-`r` two-sided `W_e` supplies 35 formal `Ext²` coefficient slots at **each** incident endpoint.

Every connected allocation with each edge rank at least one must satisfy

```
r01 >= 1
35*r12 >= 175   => r12 >= 5
35*(r04+r34+r45) >= 4800 => r04+r34+r45 >= 138
35*r06 >= 175   => r06 >= 5
35*r07 >= 3     => r07 >= 1.
```

These *disjoint* constraints give **total rank >= 1+5+138+5+1 = 150**. They are achieved by the exact allocation

`(r01,r04,r12,r34,r45,r06,r07)=(1,136,5,1,1,5,1)`.

Thus the connected numerical rank minimum is exactly **150 for this lci tree-capacity model**, not 503. Its K₀-neutral two-copy version needs 300 auxiliary `W` summands instead of 1006, a saving of 706. Theorems: `cmWeilSixfoldLCIIncidence_connected_rank_lower_bound`, `_connected_rank_feasible`, `_copy_saving`.

## 4. Actual slot assignment, rather than an unexplained rank premise

The Lean maps `cmWeilSixfoldLCIIncidence_channel_encode` and `_channel_row` send each coordinate `i<m<=35r` to its unique quotient/remainder pair `(i/35,i%35)`. `_channel_encode_injective` proves the addresses have no collisions, and `_channel_kronecker` proves their one-hot coordinate readout is exactly `δ_ij`. This is an explicitly independent **coefficient** matrix, not a postulated determinant.

Additionally, the theorem `cmWeilSixfoldLCIIncidence_allSevenEdges_active` checks this explicit edge assignment:

| Graph vertex | Adjacent-edge occupancy | Required total |
| --- | --- | ---: |
| positive 0 | 01: 35; 04: 4759; 06: 5; 07: 1 | 4800 |
| positive 2 | 12: 175 | 175 |
| positive 3 | 34: 3 | 3 |
| positive 5 | 45: 32 | 32 |
| negative 1 | 01: 1; 12: 31 | 32 |
| negative 4 | 04: 4730; 34: 35; 45: 35 | 4800 |
| negative 6 | 06: 175 | 175 |
| negative 7 | 07: 3 | 3 |

Every edge receives at least one slot at **both** ends, and all per-edge counts fit within 35 times its rank. Over a choice of genuine endpoint `Ext²` bases, the same one-hot assignment gives full-row-rank incidence coefficient arrays, so no constant coefficient combination of identical graph copies can be invisible to **all** chosen incidence arrows at that endpoint. This does NOT prove the entire derived object is indecomposable.

## 5. Twisted-perfect packet and square-zero compatibility

For a rank-one edge, take the four perfect terms

`O_We[-1], O_We[0], O_Zpositive[0], O_Znegative[1]`.

Their Grothendieck character is

`-[O_We]+[O_We]+[O_Zpositive]-[O_Znegative]`.

An arrow from `O_We[-1]` to either `O_We[0]` or `O_Zpositive[0]`, and one from `O_We[0]` to `O_Znegative[1]`, is represented by an underlying `Ext²) class: `Hom¹(A[s],B[t])=Ext^(1+t-s)(A,B)`. The only composable pair is `O_We[-1]→O_We[0]→O_Znegative[1]`. Its product is in `Ext⁴(O_We,O_Znegative)=0`, so one can choose a degree-one nullhomotopy correction for the Maurer–Cartan twisted differential. There are no length-three paths in this directed pattern.

Taking 150 K₀-neutral auxiliary pairs with graph terms of the given multiplicities retains precisely the integral signed eight-graph `K₀` class of the existing three-operator pure-Weil numerator. All constituents are perfect on the central smooth sixfold. A nonzero self-`Ext²(O_We,O_We)` connector is available in the expected geometry: `We` has a full `E²` third-coordinate factor, supplying a nonzero `H²(We,O_We)` summand. The full sheaf-level construction, including the dg enhancement and compatibility of selected bases and maps, has **not** been instantiated in Lean.

Crucial distinction: a central perfect complex with this `K₀` class, even coupled, need not deform over all nonsplit Weil periods. The pure Weil Chern-character test removes the first-order *Hodge-type* obstruction of the raw unprojected pair, but not necessarily the actual `At(F)⌟κ ∈ Ext²(F,F)` obstruction.

## 6. Discriminator and exact program status

The four acceptance gates remain fixed: canonical original-`X` cycle-class semantics, full-class Lefschetz reduction, independent universal primitive Chow source generation on arbitrary original `X`, and the exact unconditional Lean theorem. This specialized construction is a **Gate-3 geometry experiment**, not completion of that quantified goal.

**Next discriminating step:** realize the explicit `We` and all its `Ext²` bases in the central scheme/derived category, form the global 150-rank connected twisted packet with actual chain-level differential, and test `At(F)⌟κ` for a named nonsplit (K)-linear polarized Kodaira–Spencer direction. If the obstruction is nonzero, record a source-specific no-go; if it vanishes with sufficient semiregularity/spread, attempt a genuine relative source. Neither outcome alone establishes the arbitrary-`X` conjecture.

**Outcome:** new sharp numerical rank reduction and explicit independent coefficient assignment are Lean-proved at pinned CI revisions. The lci/Ext and dg-perfect geometric interpretation is a reasoned construction route pending scheme-level Lean realization and independent audit. The full original-X Hodge target remains unchanged.
