# GST Weil fourfold: exact deformation of graph supports and cohomology-flat obstruction

**Date:** 2026-10-21. **Base HEAD:** `e3371c379be7c1d514fec23cea942bacb3e3f319`. **Corrects/extends:** [ten-node Ext² coupled pure-Weil source](2026-10-21-gst-weil-fourfold-connected-ext2-source.md), because its zero total Weil Hodge leakage was not enough to determine actual derived deformation. **Primary LaTeX:** [new 314-line section, same mathematical file](../derivations/GST_Weil_fourfold_bipartite_Ext2_connected_pure_Hodge_source_2026-10-21.tex).

## Exact deformation and embedded normal obstruction

On the true split Weil abelian fourfold A=E^4 with Gaussian CM action, take the specific allowed balanced deformation `u1(t)=u1+t V2`, `v2(t)=v2+t U1` and its conjugates, as in the prior derived record. For the actual graph surface `Z_(lambda1,lambda2)={v1=lambda1 u1, v2=lambda2 u2}`, the true first-order antiholomorphic conormal restrictions are `−lambda1*conj(lambda2)*conj(u2)` and `+conj(u1)`. The normal obstruction in `H¹(Z,N_(Z/A))` is the exact 2×2 matrix

`R_lambda = [[0,−lambda1*conj(lambda2)],[1,0]]`.

This is nonzero for EVERY one of the nine distinct graph supports, regardless of the slopes. For eight Gaussian-unit supports it has rank2, and for auxiliary lambda=(0,0) it has rank1. Consequently none of the nine supports admits an embedded flat first-order deformation over this genuine nonsplit tangent. The actual graph normal bundle is trivial rank2; the normal class is not an abstract type-free coefficient.

## NEW first-order Hodge test of ACTUAL cohomology sheaves, not just virtual K₀

The twisted Ext² perfect object F_conn has cohomology sheaves `H⁰(F_conn)=M=⊕_{a=1}^5 O_{Z_(P_a)}`, `H⁻¹(F_conn)=N=⊕_{b=1}^5 O_{Z_(N_b)}`. Their difference [M]−[N] has pure Weil Chern character 4 W_R, flat of Hodge type (2,2) along all balanced Weil deformations.

But BOTH Hodge characters **separately leak**. Use the genuine graph Chern-form product `(v1−lambda1 u1)(V1−conj(lambda1) U1)(v2−lambda2 u2)(V2−conj(lambda2) U2)` and the inverse first-order substitutions `u1=u1(t)−t V2(t)`, `v2=v2(t)−t U1(t)`, plus their conjugates. The coefficient of ordered genuine `(1,3)` exterior monomial `m=u2∧U1∧U2∧V2` in the deformation is

`[m] delta cl[Z_(lambda1,lambda2)]^(1,3) = −c |lambda1|² |lambda2|²`,

where c is the same nonzero normalization factor for every graph surface (Wolfram/standalone exact exterior arithmetic uses c=1).

Each of the eight unit-slope sources has coefficient −c. The auxiliary zero slope contributes 0. Thus `[m]delta ch₂(M)=[m]delta ch₂(N)=−4c≠0`, while their **virtual difference** has cancellation `[m]delta ch₂(M−N)=0` exactly.

**Consequent proved theorem:** no relative perfect complex over this genuine first-order Weil tangent can have central fiber F_conn AND both relative cohomology sheaves **flat over the base**, specializing to M and N. Indeed a flat relative coherent sheaf has horizontal rational Betti Chern character of Hodge type on every fiber, whose infinitesimal (1,3) leakage must be zero, contradicting the explicit nonzero coefficient. This rules out the **cohomology-flat two-stage deformation mechanism**; it does not automatically rule out a derived deformation whose cohomology sheaves acquire base torsion/jump.

## Reverse-Ext matrix check

For distinct irreducible surfaces Z_a,Z_b with neither included in the other, Hom(O_Za,O_Zb)=0. Thus among positive/negative original graphs the only reverse Hom^0 is at the coincident auxiliary pair Z_(0,0). That auxiliary pair has no transverse Ext² differential to itself. An exact symbolic 5×5 bipartite calculation of the 16 forward arrows against this single possible reverse-Hom^0 entry gives ALL TEN diagonal commutator corrections zero. This is an **Ext-algebra model necessary-condition audit**, NOT an independent rigorous hyperExt determination of the total Atiyah class. We do not promote it to a false proof of total obstruction nonvanishing.

## Exact computations and provenance

- Wolfram exact complex symbolic normal matrices for all nine supports: rank2 on eight nonzero unit graph slopes; rank1 on auxiliary; none vanishing.
- Wolfram exact algebraic coefficient `−lambda1 conj(lambda1)lambda2 conj(lambda2)` at the target exterior monomial: each positive and each negative graph source contributes −1; positive sum −4, negative sum −4, virtual difference 0.
- Independent local exterior-algebra wedge expansion (ordered basis u1,u2,v1,v2;U1,U2,V1,V2) checked all first-order (1,3)/(3,1) terms: four nonzero first-order monomials for each sign sum, their difference identically zero, and the chosen monomial coefficient −4. Unlike the abstract tensor model, these are explicit first-order Betti representatives on the actual split abelian fourfold.
- Wolfram 16-arrow bipartite Ext² vs aux reverse Hom⁰ symbolic matrix commutator: ten diagonal entries exactly zero. Initial Wolfram scratch used protected symbol D and was rejected; corrected separate symbols `dd,rev` returned success.
- The LaTeX manuscript is mathematical self-review, not a GitHub Lean check or formal independent proof. No local Lean installation and no external web search.

## Research interpretation

This directly evaluates the named geometric first-order obstruction instead of relabeling the Euler matrix or using a more convenient K3 family. It closes a *specific* deformation category (flat cohomology sheaves preserving the current Postnikov layering) for all 16 coupling edges. A genuinely deforming total perfect source, if present, would have to violate that layering and prove the **full** hyperExt² Atiyah–Kodaira–Spencer equation, not merely the Hodge trace. This record does not infer a statement about arbitrary smooth projective X or manufacture target Chow representatives.
