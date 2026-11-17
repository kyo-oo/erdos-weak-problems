(* Reproducible exact Wolfram source for:
   GST_full_N_original_wave_CRT_Hankel_one_matrix_algebra_2026_11_10.tex

   All operations use ORIGINAL GST carry/trit F, CM mirror/sign, microscopic
   Wave-I SURVIVE, and original mixed seed. No geometric Chow or Hodge
   realization of the information signal is assumed.

   Exact finite assertions: N=1 and N=2.
   Uniform theorem: algebraic CRT and resultant proof in the TeX file.
   Run in fresh Wolfram Language kernel.
*)
ClearAll[gstCells,gstIx,gstTwo,gstMid,gstFinal,gstSurvive,gstPos,
  gstU,gstJ,gstM,gstT,gstSeed,gstChi,gstKry,gstFold,
  gstUniform,gstCase,gstRuns,gstRes,gstAll];

gstCells=Flatten[Table[{c,d},{c,0,3},{d,0,2}],1];
gstIx[a_]:=First[FirstPosition[gstCells,a]];
gstTwo[z_]:=Boole[z==2];
gstMid[c_,d_]:=Mod[Quotient[c,2]+2d,3];
gstFinal[c_,d_]:=Mod[Mod[c,2]+2gstMid[c,d],3];
gstSurvive[c_,d_]:=
  gstTwo[d]*gstTwo[gstMid[c,d]]+
  gstTwo[gstMid[c,d]]*gstTwo[gstFinal[c,d]];
gstPos={0,1,3,4,5,9};
gstU=Table[
 Boole[j==gstIx[{
  Quotient[First[gstCells[[i]]]+4Last[gstCells[[i]]],3],
  Mod[First[gstCells[[i]]]+4Last[gstCells[[i]]],3]}]],
 {i,12},{j,12}];
gstJ=Table[
 If[MemberQ[gstPos,First[gstCells[[i]]]+4Last[gstCells[[i]]]],1,-1]*
  Boole[j==gstIx[{3-First[gstCells[[i]]],2-Last[gstCells[[i]]]}]],
 {i,12},{j,12}];
gstM=DiagonalMatrix[(gstSurvive@@#)&/@gstCells];
gstT=gstU+gstJ+gstM;
gstSeed=Boole[MemberQ[{{0,0},{0,1}},#]]&/@gstCells;
gstChi=CharacteristicPolynomial[gstT,x];
gstKry[t_,w_,r_Integer]:=Transpose[NestList[t.#&,w,r-1]];

gstFold[n_Integer?Positive]:=
 KroneckerProduct[IdentityMatrix[n],gstT]+
 KroneckerProduct[DiagonalMatrix[10Range[0,n-1]],IdentityMatrix[12]];
gstUniform[n_Integer?Positive]:=Flatten[ConstantArray[gstSeed,n]];
gstCase[n_Integer?Positive]:=Module[
 {r=12n,t=gstFold[n],v=gstUniform[n],k,ell,orbit,mom,h},
 k=gstKry[t,v,r];
 ell=LinearSolve[Transpose[k],UnitVector[r,r]];
 orbit=NestList[t.#&,v,2r-2];
 mom=ell.#&/@orbit;
 h=Table[mom[[i+j+1]],{i,0,r-1},{j,0,r-1}];
 <|"holes"->n,"waveDimension"->r,"KrylovRank"->MatrixRank[k],
 "KrylovDet"->Det[k],"HankelDet"->Det[h],
 "antiTriangular"->And@@Flatten[Table[
  If[i+j<r-1,h[[i+1,j+1]]==0,
   If[i+j==r-1,h[[i+1,j+1]]==1,True]],
  {i,0,r-1},{j,0,r-1}]],
 "allPassed"->(MatrixRank[k]==r&&Det[h]==1)
 |>
];
gstRuns=Table[gstCase[n],{n,1,2}];
gstRes=Resultant[gstChi,gstChi/.x->x-10,x];
gstAll=<|
 "OriginalU5"->(MatrixPower[gstU,5]==IdentityMatrix[12]),
 "OriginalJ2"->(gstJ.gstJ==-IdentityMatrix[12]),
 "OriginalUJcommute"->(gstU.gstJ==gstJ.gstU),
 "OriginalUAdjointU4"->(Transpose[gstU]==MatrixPower[gstU,4]),
 "OriginalJAdjointMinusJ"->(Transpose[gstJ]==-gstJ),
 "OriginalMSelfAdjoint"->(Transpose[gstM]==gstM),
 "AbsoluteRowBound4"->(Max[Total[Abs[gstT],{2}]]==4),
 "BaseCharacteristicPolynomial"->gstChi,
 "BaseKrylovDet"->Lookup[gstRuns[[1]],"KrylovDet"],
 "TwoHoleKrylovDet"->Lookup[gstRuns[[2]],"KrylovDet"],
 "TwoHoleShiftResultant"->gstRes,
 "ResultantIdentity"->(
  Lookup[gstRuns[[2]],"KrylovDet"]==
  Lookup[gstRuns[[1]],"KrylovDet"]^2*gstRes),
 "FullSourceWordMatrixUnitIdentity"->Module[
   {k=gstKry[gstT,gstSeed,12],p=Outer[Times,gstSeed,gstSeed],i=3,j=7,e},
   e=SparseArray[{{i+1,j+1}->1},{12,12}]//Normal;
   MatrixPower[gstT,i].p.MatrixPower[Transpose[gstT],j]==
    k.e.Transpose[k]],
 "RankOfAll144SourceWords"->MatrixRank[
   KroneckerProduct[gstKry[gstT,gstSeed,12],
     gstKry[gstT,gstSeed,12]]],
 "ExactRuns"->gstRuns
|>;
gstAll=Append[gstAll,"allPassed"->
 (And@@(Lookup[#,"allPassed"]&/@gstRuns) &&
 gstAll["OriginalU5"] && gstAll["OriginalJ2"] &&
 gstAll["OriginalUJcommute"] &&
 gstAll["OriginalUAdjointU4"] &&
 gstAll["OriginalJAdjointMinusJ"] &&
 gstAll["OriginalMSelfAdjoint"] &&
 gstAll["AbsoluteRowBound4"] &&
 gstAll["ResultantIdentity"] &&
 gstAll["FullSourceWordMatrixUnitIdentity"] &&
 gstAll["RankOfAll144SourceWords"]==144)];
Print[gstAll];
gstAll
