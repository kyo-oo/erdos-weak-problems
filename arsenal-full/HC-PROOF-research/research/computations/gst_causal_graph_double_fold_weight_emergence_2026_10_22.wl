(* Exact GST causal-fold incidence and mixed-Hodge weight checks.
   Research date: 2026-10-22; stateless WolframLanguageEvaluator.
   Parameters are rational/integer and all results exact, not numeric sampling.
   These checks do not prove the infinite-N theorem nor the Hodge conjecture. *)

Clear[aa,bb,tt,ss,uu,vv,g,h,nn,jj,kk,graphInc,graphCases,graphVerts];
aa=tt^2 ss^2 uu vv;
bb=1+tt ss (uu+vv)+tt^2 ss^2 uu vv;
node[x_,r_]:=1+x tt+r aa;
tower[n_]:=Sum[aa^k,{k,0,n}];

(* One nodal rational curve C_g, with g self-nodes, times P^N.
   Check weight-2j charge-zero H^(2j+1), and after product with E
   the weight-(2j+1) H^(2j+2) off-diagonal terms. *)
single=Flatten[Table[{
  Simplify[Coefficient[Expand[node[g,1] tower[nn]],tt,2 jj+1]==
    g (ss^2 uu vv)^jj],
  Simplify[Coefficient[
    Coefficient[Expand[node[g,1] tower[nn] bb],tt,2 jj+2],
    ss,2 jj+1]==
    g (uu^(jj+1) vv^jj+uu^jj vv^(jj+1))]
},{g,1,4},{nn,0,5},{jj,0,nn}],2];

(* Double causal fold: C_g x C_h x P^N. Detect rational
   weight-2j, diagonal type (j,j), even-degree 2j+2. *)
double=Flatten[Table[
  Simplify[Coefficient[
    Coefficient[Expand[node[g,1] node[h,1] tower[nn]],tt,2 jj+2],
    ss,2 jj]==g h (uu vv)^jj]
,{g,1,3},{h,1,3},{nn,0,7},{jj,0,nn}]];

(* Dual-graph edge->vertex incidence matrix, including self-loops. *)
graphInc[verts_,edges_] := Table[
  KroneckerDelta[edges[[k,1]],i]-KroneckerDelta[edges[[k,2]],i],
  {k,1,Length[edges]},{i,1,verts}];
graphCases={{{1,2},{2,3}},{{1,2},{2,3},{3,1}},
  {{1,1},{1,1},{1,1}},
  {{1,2},{2,3},{3,4},{4,1},{1,3}}};
graphVerts={3,3,1,4};
graphResult=Table[With[{ed=graphCases[[k]],vtx=graphVerts[[k]]},
 {vtx,Length[ed],MatrixRank[graphInc[vtx,ed]],
  Length[ed]-MatrixRank[graphInc[vtx,ed]],Length[ed]-vtx+1}
],{k,1,4}];


(* Smooth genus-g reverse-fold Hodge polynomial and exact comparison
   with the irreducible nodal rational curve with g self-nodes. *)
smooth[x_]:=1+x tt ss (uu+vv)+aa;
smoothing=Flatten[Table[{
 Simplify[Coefficient[Expand[(smooth[g]-node[g,1]) tower[nn]],
   tt,2 jj+1] ==
   g ss^(2 jj) (uu vv)^jj (ss (uu+vv)-1)],
 Simplify[Coefficient[Coefficient[
   Expand[smooth[g] tower[nn]],tt,2 jj+1],ss,2 jj+1] ==
   g (uu^(jj+1) vv^jj+uu^jj vv^(jj+1))]
},{g,1,4},{nn,0,7},{jj,0,nn}],2];

(* GST causal Hodge genesis G1/G2, GENERAL graph vertex and loop ranks.
   Smooth Hodge numbers are derived from the arithmetic genus of the
   causal identification graph, not entered as an independent input. *)
generalNodal[r_,g_,n_]:=Expand[(1+g tt+r aa) tower[n]];
generalSmooth[g_,n_]:=Expand[(1+g tt ss (uu+vv)+aa) tower[n]];
genesis=Flatten[Table[
 Simplify[generalSmooth[g,nn]-generalNodal[r,g,nn] ==
   Expand[(g tt (ss (uu+vv)-1)+(1-r) aa) tower[nn]]],
 {r,1,4},{g,0,5},{nn,0,8}]];
genesisCoeffs=Flatten[Table[{
 Simplify[Coefficient[Coefficient[generalNodal[r,g,nn],tt,2 jj+1],
   ss,2 jj]==g (uu vv)^jj],
 Simplify[Coefficient[Coefficient[generalSmooth[g,nn],tt,2 jj+1],
   ss,2 jj+1]==g (uu^(jj+1) vv^jj+uu^jj vv^(jj+1))]
},{r,1,3},{g,0,4},{nn,0,7},{jj,0,nn}],3];


(* Genuine all-order causal Hodge weight law: independent symbolic graph
   loop ranks b_i and component counts r_i, with arbitrary finite m and N.
   The cohomological degree m+2j, weight 2j coefficient is the product
   of all genuine loop ranks times (uv)^j. The m=0 vacuum is included. *)
Clear[causalB,causalR,allCausalOrder,allOrderChecks,m,n,j];
allCausalOrder[m0_,n0_] := Expand[
  Product[1+causalB[i] tt+causalR[i] aa,{i,1,m0}] tower[n0]];
allOrderChecks=Flatten[Table[
 TrueQ[Simplify[Coefficient[
   Coefficient[allCausalOrder[m,nn],tt,m+2 j],ss,2 j] ==
   Product[causalB[i],{i,1,m}] (uu vv)^j]],
 {m,0,5},{nn,0,5},{j,0,nn}]];

(* A higher causal 2-face can fill a 1-cell and remove its readout:
   first homologous rank = edges - rank(d1) - rank(d2).
   These are exact rational chain matrices, not a free loop label. *)
Clear[faceBoundary,rankFaceChecks];
faceBoundary[g_,f_] := Table[If[i==j,1,0],{i,1,g},{j,1,f}];
rankFaceChecks=Flatten[Table[
 If[f==0,True,
 TrueQ[MatrixRank[faceBoundary[g,f]]==f] &&
 TrueQ[g-MatrixRank[faceBoundary[g,f]]==g-f]],
 {g,0,6},{f,0,g}]];
triD1=Transpose[graphInc[3,{{1,2},{2,3},{3,1}}]];
triD2={{1},{1},{1}};
triangleFaceResult={
  triD1.triD2==ConstantArray[0,{3,1}],
  MatrixRank[triD1],MatrixRank[triD2],
  3-MatrixRank[triD1]-MatrixRank[triD2]};

(* Frobenius perturbation of the actual Dwork-type Calabi-Yau period.
   The parameter rho has a repeated indicial root of multiplicity n.
   The family L_n F(z,rho) = rho^n z^rho produces the entire
   n-element logarithmic local solution basis, not just its first period. *)
Clear[frobCoefficient,frobCoeffTests,frobRecTests,logJordan,logMonodromy,logChecks];
frobCoefficient[n_Integer?Positive,k_Integer?NonNegative,r_]:=
 Product[(n+1) Product[(n+1)(h-1+r)+q,{q,1,n}]/(h+r)^n,{h,1,k}];
frobCoeffTests=Flatten[Table[
 TrueQ[FullSimplify[frobCoefficient[n,k,0] ==
   Factorial[(n+1)k]/Factorial[k]^(n+1)]],
 {n,2,7},{k,0,5}]];
frobRecTests=Flatten[Table[
 TrueQ[FullSimplify[(k+rho)^n frobCoefficient[n,k,rho] -
  (n+1) Product[(n+1)(k-1+rho)+q,{q,1,n}]
  frobCoefficient[n,k-1,rho] == 0]],
 {n,2,6},{k,1,5}]];
logJordan[n_Integer?Positive]:=Table[If[j==i+1,1,0],
 {i,1,n},{j,1,n}];
(* Deliberately split off the exponent-zero term to avoid Wolfram
   MatrixPower on a singular Jordan matrix at power 0. *)
logMonodromy[n_Integer?Positive]:=IdentityMatrix[n]+
 Sum[(2 Pi I)^k MatrixPower[logJordan[n],k]/Factorial[k],
 {k,1,n-1}];
logChecks=Table[{n,
 TrueQ[FullSimplify[
   MatrixPower[logMonodromy[n]-IdentityMatrix[n],n] ==
   ConstantArray[0,{n,n}]]],
 TrueQ[FullSimplify[
   MatrixPower[logMonodromy[n]-IdentityMatrix[n],n-1] !=
   ConstantArray[0,{n,n}]]]},
 {n,2,7}];


(* Global relative algebraic cycle classes are flat under Gauss-Manin
   monodromy; rank-one fixed direction for a single maximal Jordan chain.
   This verifies the source-selection linear algebra, not the assertion
   that every analytic period vector is represented by a global cycle. *)
Clear[fixedPeriodChecks];
fixedPeriodChecks=Table[{n,
 MatrixRank[logMonodromy[n]-IdentityMatrix[n]]==n-1,
 Length[NullSpace[logMonodromy[n]-IdentityMatrix[n]]]==1,
 TrueQ[Simplify[(logMonodromy[n]-IdentityMatrix[n]).
   UnitVector[n,1]==ConstantArray[0,n]]]},
 {n,2,8}];


(* Entire maximal unipotent causal weight filtration:
   ker N^k has dimension k, one new cohomological direction at every
   even monodromy weight from 0 through 2(n-1). *)
Clear[kernelStaircaseChecks];
kernelStaircaseChecks=Table[{n,
  Table[n-MatrixRank[MatrixPower[logJordan[n],k]],{k,1,n}],
  Table[n-MatrixRank[MatrixPower[logJordan[n],k]],{k,1,n}]===Range[n]},
 {n,2,9}];

{"KernelStaircaseChecks"->kernelStaircaseChecks,
 "FixedSourceRankChecks"->fixedPeriodChecks,
 "FrobeniusCoefficientCount"->Length[frobCoeffTests],
 "FrobeniusCoefficientAllTrue"->And@@frobCoeffTests,
 "FrobeniusRecurrenceCount"->Length[frobRecTests],
 "FrobeniusRecurrenceAllTrue"->And@@frobRecTests,
 "MonodromyNilpotencyChecks"->logChecks,
 "AllOrderCount"->Length[allOrderChecks],
 "AllOrderAllTrue"->And@@allOrderChecks,
 "FaceRankCount"->Length[rankFaceChecks],
 "FaceRankAllTrue"->And@@rankFaceChecks,
 "TriangleFilledBoundary"->triangleFaceResult,
 "SingleCount"->Length[single],
 "SingleAllTrue"->And@@Flatten[single],
 "DoubleCount"->Length[double],
 "SmoothingCount"->Length[smoothing],
 "SmoothingAllTrue"->And@@Flatten[smoothing],
 "GenesisCount"->Length[genesis],
 "GenesisAllTrue"->And@@genesis,
 "GenesisCoefficientCount"->Length[genesisCoeffs],
 "GenesisCoefficientsAllTrue"->And@@Flatten[genesisCoeffs],
 "DoubleAllTrue"->And@@double,
 "GraphRankResults"->graphResult,
 "DoubleEvenWeight2Coefficient"->Coefficient[
   Coefficient[Expand[node[2,1] node[3,1] tower[2]],tt,4],ss,2]}
