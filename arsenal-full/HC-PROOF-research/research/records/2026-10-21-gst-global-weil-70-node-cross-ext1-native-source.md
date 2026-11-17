# GST global Weil native source surgery — 70-node connected integral CM perfect object

**Date:** 2026-10-21. **Live branch:** `research/gpt6-native-point-primitive-span-20261017`. **Starting GitHub SHA:** `5cb07f1e5d3afd16d61b65d8966d11689514b7f0` (another research pass had committed 30-node and minimal integral ten-node CM constructions). **Primary amended derivation:** [GST_Weil_fourfold_bipartite_Ext2_connected_pure_Hodge_source_2026-10-21.tex](../derivations/GST_Weil_fourfold_bipartite_Ext2_connected_pure_Hodge_source_2026-10-21.tex), Sections 14–18. **Target held fixed:** actual canonical rational Chow representative of every (p,p) rational Hodge class on every original smooth projective complex X. No fake abstract cycleClass map / algebraic preimage supplied.

## 1. Actual GLOBAL tests of original source and GST world operations

Full original-F30 local K0 packets of a graph Z with m ideal bridges:
`[O_Z]-m[I_Z]=(m+1)[O_Z]-m[O_A]`.
For the true balanced nonsplit Weil deformation, each nonzero-unit graph packet has first-order selected Hodge leak `∓(m+1)c`, c≠0. Thus NO same-support ideal-bridge packet can deform by itself, whatever its Yoneda normal rank; the thirty-node total passes that necessary Hodge test only because the four positive and four negative charges globally cancel (`m=2: 4(-3c)+4(3c)=0`). This corrects any interpretation of local ideal-bridge surjectivity as a global Atiyah proof.

**New rigorous derived obstruction transport:** for an actual finite flat f:Y→X of nonzero degree d in characteristic 0, the normalized coherent trace gives a splitting `O_X→f_*O_Y→O_X`. For any actual perfect F, derived projection formula and adjunction inject `Ext²_X(F,F)→Ext²_Y(Lf*F,Lf*F)`. For any smooth blowup or projective bundle, `Rf_*O_Y=O_X`, so this map is an **isomorphism**. Under a compatible deformation of the whole morphism, naturality gives `At(Lf*F)κ_Y=f*(At(F)κ_X)`: an existing nonzero obstruction persists for the SAME pulled-back source. For actual finite étale degree d, the true Euler self-pairing scales by d (`8d` for integral minimal Weil, `1152d` for F30), but that is not an obstruction-cancellation mechanism. This is a derived-Ext counterpart to the previously green Lean GST laws `DegreePacket.compose`, `missing_target_hodge_survives_finite_pullback`, `blowupCanonicalCycleBlock_surjective_iff` and `nativeCore_defectAction_zero`.

## 2. Exact actual line-bundle geometric Yoneda source

On ORIGINAL A=E^4 with genuine Gaussian CM, define `M_ab=pr_a^*O_E(o)⊗pr_b^*O_E(o)` for all six coordinate pairs and for any real actual algebraic line bundle L define J_ab=L⊗M_ab^-1. Then genuine Kunneth/Serre groups are `Ext²_A(L,J_ab)=C` and `Hom_A(J_ab,L)=C`. Their true Yoneda products supply precisely the corresponding six independent wedge basis directions in `Ext²_A(L,L)=H²(A,O_A)` (dimension SIX), not an assumed formal obstruction coordinate. Two of these actual bridges factor the previously obstinate line-bundle P1=LV1⊠LV2 curvature `−V2∧V1−U1∧U2`.

A new connected **14-node** actual central perfect source used two neutral pairs Jx[0]⊕Jx[1] and Jy[0]⊕Jy[1], closed degree-one Ext² arrows P1→Jν[1] and Jν[0]→Jν[1]. The central Maurer–Cartan condition holds strictly and `K0=Kmin, ch2=WR, Euler=8`. Its P1 diagonal Ext² equation is solvable. HOWEVER an exact five-vertex cut supertrace isolates P1 because every old cross boundary arrow P1→N_j[1] has reverse Hom(N_j,P1)=0. The neutral pair curvature traces cancel, leaving nonzero `a_P1`. The ACTUAL total fourteen-node Atiyah class is therefore nonzero under the named nonsplit deformation. Wolfram's supertrace weight vector `(1,1,-1,1,-1)` returns precisely `a_P1`. This closes that particular local-only repair.

## 3. NEW original CM geometry: cross-support BIDIRECTIONAL Ext1

Use ACTUAL Gaussian elliptic quotient maps ℓ_v:E^4→E and actual degree-one pulled-back line bundles M_v=ℓ_v^*O_E(o). Four coordinate bundles plus six `R_ij=M_(e_i+e_j)` and six `I_ij=M_(e_i−i e_j)` form a 16-element integral Hermitian--NS lattice basis. Wolfram directly formed its complete 16×16 integer matrix, rank16 and **determinant +1**. This gives explicit INTEGRAL tensor chains between all symmetric line bundles constructed from these classes, including GST's DU/DV sources.

For any L, the *different* actual line bundle J=L⊗M_v has
`dim Ext¹_A(L,J)=3` and `dim Ext¹_A(J,L)=1`, with the true Yoneda products spanning the **3-dimensional** H²(O_A) subspace `ω_v∧H¹(kernel ℓ_v,O)`. If the quotient step is inverted, the dimensions are 1 and3. These are genuine crossed degree-one morphisms in BOTH DIRECTIONS, bypassing the old zero-reverse-Hom cut. Three distinct coordinate anchors are needed to span all six wedge lines (Wolfram corrected a scratch estimate of two anchors).

## 4. Actual 46- and 70-node integral source constructions

The old ten-node integral Weil perfect source had positive vertices `(VV,UO,OU,Vp,pV)`, negative vertices `(UU,VO,OV,Up,pU)`, 17 genuine central Ext² edges, ch₂=WR purely middle, and Euler8. Let (D_i), (R_{ij}), (I_{ij}) be the actual rank-one elliptic-quotient divisor bundles. Hermitian matrices for the symmetric integral inputs are DV=`[[0,1],[1,0]]` and DU=`[[0,i],[-i,0]]` in each CM pair.

Two exact original-GST source chains from P1=VV:
- to N1=UU (12 steps): +Dx1,+Dx1,+Dy1,+Dy1,+Dx2,+Dx2,+Dy2,+Dy2,−R(x1,y1),−I(x1,y1),−R(x2,y2),−I(x2,y2);
- to N2=VO (6 steps): +Dy1,−Dy1,−R(x2,y2),+Dx2,+Dy2,0.

Wolfram verified both full 4×4 Hermitian endpoint identities exactly. For every chain step add the actual neutral pair L_k[0]⊕L_k[1]. Orient degree-one Ext¹ arrows from even-index sources to odd-index sinks; attach each shifted copy by an actual Ext² arrow from an even source, and terminal even copy to the original negative source via genuine Ext². No vertex has both incoming and outgoing central arrows, so δ²=0 **strictly**, with no unverified Yoneda product cancellation. The 46-node network has 55 edges, is connected, and has the **same integral** `Kmin`, complete pure Weil Chow Chern character, canonical Betti class and Euler8.

The full actual crossed Hom table for the five old negative vs five old positive source objects is
`[[0,0,0,0,0],[0,0,0,0,0],[0,0,0,0,0],[0,1,0,0,0],[0,0,1,0,0]]`.
Thus P2=UO and P3=OU also have nonzero line-bundle Atiyah curvatures without old reverse-Hom sources. Two MORE exact 6-step line-bundle paths to N1=UU were constructed:
- UO→UU: +Dy1,−Dy1,+Dx2,+Dy2,−I(x2,y2),0;
- OU→UU: +Dx1,−Dx1,+Dx1,+Dy1,−I(x1,y1),0.

Wolfram verified both exact matrix endpoints and the anchored first Ext¹ Yoneda images. These four genuine chains have lengths 12,6,6,6. They introduce **30 zero-K₀ line-bundle pairs** and yield the ACTUAL **70-node** central perfect source. A COMPLETE separate JS adjacency enumeration checked all 70 vertices, **81** actual Ext-type arrows, one connected graph and ZERO directed paths of length two; hence full CENTRAL dg MC. Its exact K₀, Chow, Betti and Euler data equal the original `Kmin` and 8. For all three obstructed positive line-bundle vertices P1,P2,P3, true first-edge crossed Ext¹/Yoneda products span and cancel their individual diagonal first-order Atiyah classes. This is a substantive global cross-support SOURCE ARCHITECTURE UPGRADE, not a Hodge-to-Chow selector.

## 5. Exact first-order acceptance status

**Completed in geometry and algebra:** every source vertex is a genuine coherent perfect algebraic object on original A, central 70-node chain condition holds, integral K₀ and pure middle canonical Weil character are preserved, actual degree-one Ext¹ and Ext² carriers are calculated, and three original line-bundle diagonal first-order Atiyah equations admit genuine crossed Yoneda corrections.

**Not obtained:** a single compatible cochain (h) solving the TOTAL `D_(δ70)h=−At(F70)κ` simultaneously at the other vertices and all off-diagonal components, a flat holomorphic relative source on a non-split Weil variety, or any all-varieties Chow representative. No arbitrary-X surjectivity or synthetic canonical map is inserted.

**Validation:** Wolfram exact Hermitian determinant +1, four path endpoint identities, six- and three-dimensional wedge Yoneda rank checks, Gaussian Kunneth dimensions, neutral K₀ arithmetic; independent model-local exhaustive directed graph check 70 vertices/81 edges/no 2-step/connected; LaTeX structural checks as final QC. The geometric external inputs are actual elliptic curve cohomology, Kunneth, coherent dg models and HKR/Atiyah functoriality. No new Lean module was edited and no Lean CI result is claimed.
