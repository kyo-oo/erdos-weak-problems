(* CORRECTION AUDIT: GST cardinality proposal requires CONNECTED native geometry.
   This executable is exact rational linear algebra ONLY, not a Chow
   correspondence constructor or a proof of universal Hodge algebraicity.
   It tests the mathematically decisive distinctions from three images:
   (1) disconnected tags vs connected source fold;
   (2) Hodge-valued 2-coordinate reconstruction vs scalar compression;
   (3) full cyclic orbit automatically supplies a rational nonzero-Hankel
       detector (no independent third obstruction).
   The uniform proof is in the accompanying repository correction record.
*)
ClearAll[one, runs, tMix, tSep, seed, dual, compress, result];
one[r_Integer?Positive] := Module[{p,t,v,k,ell,moment},
  p=Table[Boole[i==Mod[j,r]+1],{i,r},{j,r}];
  t=3 IdentityMatrix[r]+p;
  v=UnitVector[r,1];
  k=Transpose[Table[MatrixPower[t,j].v,{j,0,r-1}]];
  ell=LinearSolve[Transpose[k],UnitVector[r,r]];
  moment=Table[ell.MatrixPower[t,i+j].v,{i,0,r-1},{j,0,r-1}];
  <|"rank"->r,"krylovRank"->MatrixRank[k],"krylovDet"->Det[k],
    "hankelDet"->Det[moment],
    "expectedHankelDet"->(-1)^(r(r-1)/2),
    "passed"->(MatrixRank[k]==r &&
      Det[moment]==(-1)^(r(r-1)/2))|>
];
runs=Table[one[r],{r,1,7}];
tMix={{0,1},{1,0}};
tSep=IdentityMatrix[2];
seed={1,0};dual={1,0};
compress={{1,1}};
result=<|
 "momentCriterionFromFullRank"->runs,
 "allMomentCriteriaPass"->And@@(Lookup[#,"passed"]&/@runs),
 "unlinkedRank"->MatrixRank[Transpose[{seed,tSep.seed}]],
 "unlinkedMomentDet"->Det[
   Table[dual.MatrixPower[tSep,i+j].seed,{i,0,1},{j,0,1}]],
 "connectedRank"->MatrixRank[Transpose[{seed,tMix.seed}]],
 "connectedMomentDet"->Det[
   Table[dual.MatrixPower[tMix,i+j].seed,{i,0,1},{j,0,1}]],
 "scalarCompressionRank"->MatrixRank[compress],
 "scalarCompressionKernel"->(compress.{1,-1}=={0}),
 "allPassed"->(And@@(Lookup[#,"passed"]&/@runs) &&
   MatrixRank[Transpose[{seed,tSep.seed}]]==1 &&
   MatrixRank[Transpose[{seed,tMix.seed}]]==2 &&
   MatrixRank[compress]==1 && compress.{1,-1}=={0})
|>;
Print[result];result