# GST Weil fourfold: actual connected Ext² source, pure Weil K-theory, and deformation audit

**Date:** 2026-10-21 IST. **Research target:** universal original-X rational Hodge-to-Chow source existence and actual nonseparable Euler-to-one-legged source. **Pinned starting revision:** `4b9f2400207d40f4710ca554300fd4980f4947aa`. **Authoritative new mathematical LaTeX:** [GST_Weil_fourfold_bipartite_Ext2_connected_pure_Hodge_source_2026-10-21.tex](../derivations/GST_Weil_fourfold_bipartite_Ext2_connected_pure_Hodge_source_2026-10-21.tex). No Lean edit, no local Lean installation, and no general web search.

## What was constructed on an ACTUAL original variety

Let E be the genuine Gaussian CM elliptic curve and A=E^4 with Q(i) acting +i on two x factors and −i on two y factors. The authentic smooth abelian graph surfaces `Z_(lambda1,lambda2) = {y1=lambda1 x1, y2=lambda2 x2}` have translation-trivial normal bundles and `ch(O_Z)=[Z]` purely in CH²(A) by GRR.

Define the ACTUAL Chow graph-difference divisors on each pair: `U_j=(G_(i,j)-G_(-i,j))/2`, `V_j=-(G_(1,j)-G_(-1,j))/2`. Their true rational Betti components equal the standard mixed CM forms. The rational exceptional Weil class is `W_R=-U1 U2+V1 V2`, with genuine geometric norm 8. The exact CH identity is

`4 W_R=(G1-G-1)_1 (G1-G-1)_2-(Gi-G-i)_1(Gi-G-i)_2`,

so 4W_R is the **integral** signed combination of eight ACTUAL graph abelian surfaces with positive slopes `(1,1),(-1,-1),(i,-i),(-i,i)` and negative slopes `(1,-1),(-1,1),(i,i),(-i,-i)`. No abstract Hodge class is assumed algebraic to construct those surfaces.

Insert one K0-neutral positive and negative pair, each the same ACTUAL `Z_(0,0)`. The resulting 10-node bipartite graph has **16 genuine transverse crossings and is connected**. For each oriented positive→negative transverse graph pair, its actual finite reduced intersection P has length `N(lambda1-mu1)N(lambda2-mu2)`, with sheaf Ext concentrated in degree 2: `Ext²_A(O_Zlambda,O_Zmu)=H⁰(P,O_P)=C^{length(P)}`, all other degrees zero. Thus the morphism of total dg degree one from `O_Zpositive[0]` to `O_Znegative[1]` is in genuine Ext² and has exactly the **correct opposite-K0-sign parity**. Choose closed nonzero such morphisms on all 16 edges. With NO reverse arrows, the off-diagonal twisted dg matrix squares to zero and gives an ACTUAL perfect complex `F_conn` on split A, with a connected nonzero coupling graph.

Its complete rational algebraic Chern character is `ch₂(F_conn)=4 W_R`, all other grades zero. HRR gives `chi(F_conn,F_conn)=128`. Its rational K0 class divided by 4 is a pure Weil class with self-Euler 8. This is a nontrivially coupled split-fiber perfect-object construction and a direct geometric repair of the sixfold bare-graph Ext³ shift-parity failure in this four-dimensional setting.

## First-order Hodge and TRUE unsolved source obligation

On every K-linear balanced Weil-type polarized deformation, the determinant of the rank-four K-eigen subspace remains Hodge type (2,2). Therefore the flat rational class `4 W_R` has **zero first-order (1,3) and (3,1) Hodge variation**. Exact Wolfram decomposed the real source as `-(P1 P2+Q1 Q2)/2`, confirmed the two determinant-one eigenbasis shears and cancellation of a representative raw graph-divisor first-order leakage coefficient. The genuine Atiyah–Kodaira–Spencer obstruction `At(F_conn) cup kappa ∈ Ext²_A(F_conn,F_conn)` is **not** proven zero. Vanishing traced Chern variation is only a necessary condition; the existence of a holomorphic perfect object on an actual nonsplit Weil-type A remains unproved, as does the all-original-X Hodge conjecture. The connected coupling graph is not a proof of indecomposability, simplicity, or unobstructedness.

If the INTEGRAL class F_conn were simple on the Calabi–Yau fourfold, Serre duality and Euler128 would give `ext²=126+2 ext¹`. The full raw semiregularity codomain dimension is `6+16+6=28`: one cannot claim full semiregularity injection for this inflated integral object. The lower primitive rational class has self-Euler8 but is not automatically represented by a single simple integral complex of that class. These are explicit type-safe guards against repeating prior overclaims.

## Wolfram exact computation and corrected arithmetic

- Exact expansion of eight signed genuine graph products gave four plus and four minus coefficients, each ±1; pure Weil real source algebra checked.
- The 5×5 positive–negative comparison of graph surface slopes produced exactly **16** transverse Ext² edges, a connected graph on all ten nodes. Edge intersection dimensions are 1 or 4.
- **Correction to earlier scratch result and preliminary response:** graph slopes `1` versus `2+i` differ by `−1−i` (Gaussian norm2), so paired-fourfold intersection has **4**, NOT 16 points. Slopes `1` versus `1+2i` differ by `−2i` (Gaussian norm4), giving **16** points on paired E². Wolfram's generic `Norm[2i]` computes the complex absolute value 2, not Gaussian norm squared4; rejected that scratch call and used explicitly `a²+b²`.
- Exact pure Weil Gram: `W_R²=8`, integral `(4W_R)²=128`; Serre and semiregularity dimension equations checked.
- Exact determinant-one Hodge eigenbasis shears and symbolic real/imag source decomposition checked. Wolfram symbols first printed noncritical initialization warnings but numerical/algebraic returned expressions were crosschecked against hand exterior expansions.

**Evidence classification:** derived geometric existence on **split** CM abelian fourfold, actual coherent Ext², dg coupling and Chow Chern character; mathematical self-review, exact arithmetic Wolfram crosscheck, not independently refereed or Lean verified. **Program route remains active:** the first unfixed substantive implication is `At(F_conn) cup kappa =0` for an actual nonsplit Weil deformation and construction of a relative perfect source with canonical Betti class. Universal arbitrary-X source production is not justified by the split result.
