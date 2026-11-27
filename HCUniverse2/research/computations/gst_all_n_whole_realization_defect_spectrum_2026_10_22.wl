(* 2026-10-22 GST whole-realization all-N Hodge defect spectral test.
   EXACT rational arithmetic, no assumed Hodge conjecture.
   Test A: projective folds by polynomial multiplication vs independent
   enumeration of rank-index tuples for ranks {1,2,3,1,2,3}.
   Test B: binomial fold law for n=0..14 and all p=0..9.
   Test C: first-defect persistence, base D(t)=a t^2+b t^4.
   Test D: formal all-pure but Chow-defective rank-two model for n=0..12.
   All are finite assertions, not geometric Chow source certificates. *)
ClearAll["Global`*"];
rankList={1,2,3,1,2,3};
basePoly=Sum[z[p] t^p,{p,0,8}];
(* Independent enumeration, without expanding a product of fold polys. *)
directFold[n_Integer?NonNegative] :=
 Expand[Sum[basePoly t^Total[indices],
  {indices,Tuples[Range[0,#]& /@ Take[rankList,n]]}]];
factorFold[n_Integer?NonNegative] :=
 Expand[basePoly Times@@(Sum[t^i,{i,0,#}]& /@ Take[rankList,n])];
allDepth=Table[{n,
   TrueQ[Simplify[directFold[n]-factorFold[n]]==0]},
 {n,0,Length[rankList]}];
binomialCases=Flatten[Table[
 {n,p,
  TrueQ[Sum[Binomial[n,k] If[0<=p-k<=8,z[p-k],0],
       {k,0,Min[n,p]}]===
    Coefficient[Expand[basePoly (1+t)^n],t,p]]},
 {n,0,14},{p,0,9}],1];
firstDefect=Table[
 {n,TrueQ[Coefficient[Expand[(a t^2+b t^4)(1+t)^n],t,2]===a]},
 {n,0,14}];
formalPureModel=Table[{n,2+n,1+n,1,
 TrueQ[(2+n)-(1+n)==1]},{n,0,12}];
result=<|"depthCases"->Length[allDepth],
 "depthAllPass"->And@@allDepth[[All,2]],
 "binomialCases"->Length[binomialCases],
 "binomialAllPass"->And@@binomialCases[[All,3]],
 "firstDefectCases"->Length[firstDefect],
 "firstDefectAllPass"->And@@firstDefect[[All,2]],
 "formalPureModelCases"->Length[formalPureModel],
 "formalPureDefectPersists"->And@@formalPureModel[[All,5]],
 "failures"->Join[Select[allDepth,Not[#[[2]]]&],
 Select[binomialCases,Not[#[[3]]]&],
 Select[firstDefect,Not[#[[2]]]&]]|>;
Print[result];result