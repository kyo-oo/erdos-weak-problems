# GST Weil fourfold: full curved-dg Atiyah test and corrected ideal-sheaf Yoneda repair

**Date:** 2026-10-21 IST. **Base SHA:** `e3371c379be7c1d514fec23cea942bacb3e3f319`. **Main source:** [the amended mathematics-first LaTeX derivation, Sections 6–8](../derivations/GST_Weil_fourfold_bipartite_Ext2_connected_pure_Hodge_source_2026-10-21.tex). **Corrects:** [earlier total Atiyah left unresolved](2026-10-21-gst-weil-fourfold-connected-ext2-source.md) and extends [the cohomology-flat obstruction](2026-10-21-gst-weil-fourfold-normal-obstruction-cohomology-flat-no-go.md). No Lean file changed, no local Lean installation, no public web search.

## 1. First-order actual vertex Atiyah class

The original scheme is the split Gaussian Weil-type abelian fourfold A=E^4. Its actual balanced nonsplit first-order deformation is u1(t)=u1+t V2, v2(t)=v2+t U1, with the conjugate variation and other coordinates fixed. The original ACTUAL abelian graph supports Z_(lambda1,lambda2) have graph equations yj=lambda_j xj.

Their first-order normal obstructions in H¹(Z,N_(Z/A)) are the exact matrix `R_lambda=[[0,−lambda1 conjugate(lambda2)],[1,0]]`. For the eight Gaussian unit-slope graph surfaces the rank is two, and for auxiliary zero-slope graph the rank is one. EVERY support has nonzero obstruction. Independently the canonical Betti ch₂ of each unit graph has coefficient −c≠0 of the ordered (1,3) wedge monomial u2∧U1∧U2∧V2; c is a fixed nonzero normalization. Therefore the actual coherent-sheaf Atiyah class At(O_Z)⌟κ in Ext²(O_Z,O_Z) is nonzero, with no spectral-degeneration assumption: if zero a holomorphic first-order object lift would force the Chern character to stay Hodge.

The two original cohomology sheaves of the exact 10-node Ext² twisted complex are M=⊕positive O_Z (in degree zero) and N=⊕negative O_Z (in degree −1). Their first-order Hodge leaks have exactly equal nonzero coefficient −4c, while the virtual difference M−N is pure Weil and its leak cancels. Thus cohomology-flat lifts are excluded.

## 2. Full curved-dg obstruction nonvanishing for the *named* 10-node architecture

The strict one-way twisted complex F=(M⊕N[1],δ) has δ consisting of 16 genuine forward degree-one morphisms P_i→N_j[1] representing Ext²(O_Pi,O_Nj), and δ²=0. In the standard first-order curved-dg deformation model its total lift must solve `d_B h + δh + hδ = −a_κ`, with the individual vertex Atiyah curvature classes on the diagonal and any variation of forward maps confined to the forward block.

For every obstructed positive unit graph P_i, the reverse degree-one groups are

`Hom¹(O_Nj[1],O_Pi)=Hom_A(O_Nj,O_Pi)=0` for ALL negative j, since the underlying irreducible graph surfaces are distinct and neither is contained in the other (their intersection cannot support a nonzero subsheaf of the pure sheaf O_Pi). The only coincident opposite-sign support is the auxiliary P5=N5, not a unit vertex.

The reverse block of the first-order curved Maurer–Cartan equation therefore makes every reverse correction into P_i closed, and the zero reverse Hom means it is cochain-exact. The positive-diagonal equation then reduces modulo boundaries to `[At(O_Pi)⌟κ]=0` in Ext²(O_Pi,O_Pi), contradicting the independent nonzero Betti Hodge drift. Therefore **the intrinsic total Ext² Atiyah obstruction of this EXACT 10-node split Weil source is nonzero along this named nonsplit tangent, for any selection of the 16 forward Ext² arrows**. This completes the previously unfinished first-order obstruction calculation for this named geometric candidate. It does not prove a statement about every derived representative of the same K0 class.

Wolfram exactly verified the 16-edge 5×5 bipartite forward operator vs the only possible auxiliary reverse Hom matrix, with all ten diagonal commutators zero. The actual Koszul–Kunneth split graph self-Ext dimension profile is (1,4,6,4,1); Ext² has dimension six with four-dimensional H¹(N) normal-obstruction component.

## 3. The concrete NEW geometric source required for Atiyah cancellation: ideal sheaf

Let i:Z⊂X be ANY actual smooth regular codimension-two embedding into a smooth projective X, with actual ideal I_Z and rank-two normal bundle N. The exact coherent ideal sequence and local length-two Koszul resolution give the TRUE local sheaf Ext profile:

- sheaf Ext⁰_X(O_Z,I_Z)=0;
- sheaf Ext¹_X(O_Z,I_Z)=O_Z;
- **sheaf Ext²_X(O_Z,I_Z)=N (NONZERO)**;
- sheaf Ext^q=0 for q>2;
- sheaf Hom_X(I_Z,O_Z)=N via I/I²=N*.

**Important corrected error during self-audit:** the first draft wrongly dropped the sheaf Ext² row and asserted global Ext²(O_Z,I_Z)=H¹(O_Z). That assertion has been REPLACED in the committed LaTeX, not retained as a theorem. The actual local-to-global spectral sequence has TWO rows. Its surviving H¹(O_Z) filtration piece is represented by cup with the genuine ideal extension e∈Ext¹(O_Z,I_Z); in general there can be an extra H⁰(N) contribution (and a d₂ differential). For the actual graph surfaces, the embedding is algebraically split by the coordinate automorphism (x,y)↦(x,y−lambda x); the Koszul–Kunneth spectral sequence splits and the full group is

`Ext²_A(O_Z,I_Z) ≅ H¹(Z,O_Z) ⊕ H⁰(Z,N)`, dimensions **2+2=4**.

The genuine reverse group `Hom_A(I_Z,O_Z)=H⁰(Z,N)` is dimension two. The actual Yoneda composition restricted to the distinguished H¹(O_Z) subspace maps `H¹(O_Z)⊗H⁰(N)→H¹(N)` by cup product. Because the graph normal bundle is trivial rank two, this is a **4×4 surjective (indeed invertible) geometric map onto the COMPLETE normal-graded Atiyah obstruction sector**. Thus actual ideal sheaves repair the exact reverse-Hom source type that the original forward-only graph sheaves lacked.

For each unit graph the rank-two matrix
`R=[[0,−lambda1 conjugate(lambda2)],[1,0]]`
has the EXACT two-term decomposition
`R=(0,1)^T (1,0)+(-lambda1 conjugate(lambda2),0)^T (0,1)`.
These two rank-one tensors have genuine Yoneda realizations δ_j∈Ext²_A(O_Z,I_Z), h_j∈Hom_A(I_Z,O_Z). The determinant is nonzero, so **two ideal-sheaf bridges are minimal for a unit graph vertex**; one suffices for the auxiliary zero graph. This is an executed exact geometric normal-obstruction-cancellation result, not a full global derived Maurer–Cartan solution with all newly added auxiliary vertices.

## 4. Independent exact computational checks and scope

- Wolfram exact normal matrices for nine graph supports: ranks (2×8,1×1), all nonzero.
- Independent ordered Grassmann exterior expansion of the actual graph Chern wedge: each unit graph contributes −c to u2∧U1∧U2∧V2, positive and negative sums both −4c, difference 0; this is independent of Euler norm.
- Wolfram exact ten diagonal corrections from 16 forward Ext² arrows and auxiliary reverse Hom: all zero, as required by the curved-dg proof.
- Wolfram exact graph self-Ext degrees 0..4: 1,4,6,4,1; `dim H¹(N)=4`.
- Wolfram corrected Koszul–Kunneth global ideal Ext² rank 4 (2+2), reverse Hom rank 2; normal Yoneda cup sector rank 4; exact rank-two outer-product factorization `R` for unit slopes.

**Proof status:** mathematics-first LaTeX with actual coherent sheaves and dg obstruction formula, Wolfram exact algebra checked, self-review only; not Lean-verified or independently refereed. **Result status:** the specific old pure-Weil ten-node forward-graph object cannot deform under the named nonsplit tangent; the new ideal-sheaf bridge has a fully computed local normal-obstruction image but no falsely claimed simultaneous solution on all auxiliary vertices or all smooth projective X. This record maintains the universal Hodge objective without calling any conditional input a source-existence proof.
