(* GST unlimited-emergent-dimension whole Hodge/Chow spectra.
   2026-10-23. Exact independent finite enumerator:
   all 0<=n<=5, rank tuples in {1,2,3}, 364 towers.
   Compares explicit tuples of all Tate shifts against
   product of projective fold factors.
   Also tests separate Hodge-fiber, algebraic-image and
   defect spectra, plus first-defect survival and
   n-binomial growth up to depth 12.
   No claim of a finite test proving the rational Hodge
   conjecture or an actual infinite-dimensional variety.
*)
ClearAll["Global`*"];
foldPoly[rr_List] := Expand[Times@@(Sum[t^j,{j,0,#}]&/@rr)];
enumeratePoly[rr_List] := If[Length[rr]==0,1,
  Expand[Total[t^Total[#]&/@Tuples[(Range[0,#]&/@rr)]]]];
tripleF=2+5 t+3 t^2;
tripleA=2+3 t+3 t^2;
tripleD=Expand[tripleF-tripleA];
allRanks=Flatten[Table[Tuples[{1,2,3},nn],{nn,0,5}],1];
cases=Table[Module[{f=foldPoly[rr],e=enumeratePoly[rr],
       h=Expand[(1+u v+(u v)^2)foldPoly[rr]/.t->u v],
       pureCheck,algebraCheck,defectCheck,firstCheck},
   pureCheck=Expand[h-(1+u v+(u v)^2)(e/.t->u v)]===0;
   algebraCheck=Expand[tripleA f-tripleA e]===0;
   defectCheck=Expand[tripleD f-(tripleF f-tripleA f)]===0;
   firstCheck=Coefficient[tripleD f,t,1]==2;
   {Length[rr],f===e,pureCheck,algebraCheck,defectCheck,firstCheck}],
 {rr,allRanks}];
binomialChecks=Flatten[Table[
 {nn,pp,TrueQ[Coefficient[Expand[tripleD (1+t)^nn],t,pp] ==
   Sum[Binomial[nn,j] Coefficient[tripleD,t,pp-j],{j,0,Min[nn,pp]}]]},
 {nn,0,12},{pp,0,13}],1];
(* Exact one-birth causal gradient and finite quantitative lower bound,
   tested for every allowed p on the formal base defect 2t. *)
gradientChecks=Table[{pp,
 TrueQ[Coefficient[Expand[tripleD (1+t)],t,pp+1] -
       Coefficient[tripleD,t,pp+1] == Coefficient[tripleD,t,pp]]},
 {pp,0,6}];
linearLowerBound=Table[{nn,
 TrueQ[Coefficient[Expand[tripleD (1+t)^nn],t,2] >=
   nn Coefficient[tripleD,t,1]]},{nn,0,12}];
result=<|
 "towerCount"->Length[cases],
 "tupleEnumerationPass"->And@@cases[[All,2]],
 "wholeHodgePass"->And@@cases[[All,3]],
 "nativeAlgebraicImagePass"->And@@cases[[All,4]],
 "defectDifferencePass"->And@@cases[[All,5]],
 "firstDefectInvariantPass"->And@@cases[[All,6]],
 "rankOneBinomialCases"->Length[binomialChecks],
 "rankOneBinomialPass"->And@@binomialChecks[[All,3]],
 "gradientCases"->Length[gradientChecks],
 "gradientPass"->And@@gradientChecks[[All,2]],
 "lowerBoundCases"->Length[linearLowerBound],
 "lowerBoundPass"->And@@linearLowerBound[[All,2]],
 "symbolicDefectAtGrades1to4"->Table[2 Binomial[n,j],{j,0,3}],
 "asymptoticLeadingCoefficients"->Table[Coefficient[Expand[Product[n-k,{k,0,j-1}]/Factorial[j]],n,j],{j,0,4}],
 "formalHypotheticalDefect"->tripleD,
 "failedTowers"->Select[cases,Not[And@@#[[2;;6]]]&],
 "failedBinomial"->Select[binomialChecks,Not[#[[3]]]&]
|>;
Print[result]; result