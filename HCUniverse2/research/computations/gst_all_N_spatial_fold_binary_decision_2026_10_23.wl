(* GST all-N spatial fold dichotomy: exact geometry arithmetic.
   Input two marked elliptic moduli (i,i) vs (i,2i).
   Exterior wedge test independent from Hodge-polynomial test.
   Entire exact domain N = 2,...,40, no random sampling.
   Mathematical projective variety and rational Hodge-conjecture
   statements are proved in companion TeX, not inferred from tests.
*)
Clear[ss,tt,u,v,k,domega,eqPeriod,breakPeriod,hSurface,hPoly,rows];
domega=Factor[Det[{{1,0,-1,0},{0,1,0,-1},{1,tt,0,0},{0,0,1,ss}}]];
eqPeriod=domega/.{tt->I,ss->I};
breakPeriod=domega/.{tt->I,ss->2 I};
hSurface=Expand[(1+u)^2 (1+v)^2];
rows=Table[Module[{h,diag,misalignedSector,topCoefficient},
 h=Expand[hSurface Sum[(u v)^j,{j,0,dim-2}]];
 diag=Coefficient[Coefficient[h,u,dim-1],v,dim-1];
 misalignedSector=Coefficient[Coefficient[h,u,dim],v,dim-2];
 topCoefficient=Coefficient[Coefficient[h,u,dim],v,dim];
 {dim,diag,misalignedSector,topCoefficient,
  TrueQ[diag>=1 && misalignedSector==1 && topCoefficient==1 &&
    eqPeriod==0 && breakPeriod==I]}],{dim,2,40}];
result=<|
 "exactHolomorphicVolumeCoefficient"->domega,
 "equalMarkedModuliPeriod"->eqPeriod,
 "unequalMarkedModuliPeriod"->breakPeriod,
 "finiteNRange"->{2,40},
 "geometricDimensionsChecked"->Length[rows],
 "allPureHodgePolynomialsAndOffDiagonalChannelsPass"->And@@rows[[All,5]],
 "firstCases"->Take[rows,3],
 "lastCases"->Take[rows,-3],
 "failedCases"->Select[rows,Not[#[[5]]]&],
 "nonClaim"->"No computation establishes all-X Hodge algebraicity; this tests the proposed break=>counterexample rule"
|>;
Print[result];result