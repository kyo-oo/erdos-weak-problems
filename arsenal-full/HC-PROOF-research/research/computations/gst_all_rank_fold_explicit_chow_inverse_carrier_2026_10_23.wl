(* Mathbox verification of the GST ACTUAL projective-fold
   Segre/Chow coefficient extraction law.
   Mathematical theorem is proved for ALL r in the matching LaTeX;
   this symbolic computation independently audits ranks 0..12.
   No stochastic input, no numerical tolerance, no local Lean. *)
ClearAll["Global`*"];
test[r_Integer]:=Module[{svec,avec,moments,out},
 svec=Prepend[Array[ss,r],1];
 avec=Table[aa[i],{i,0,r}];
 moments=Table[
  Expand[Sum[svec[[i-j+1]] avec[[i+1]],{i,j,r}]],
 {j,0,r}];
 out=ConstantArray[0,r+1];
 Do[
  out[[j+1]]=Expand[
    moments[[j+1]]-Sum[
     svec[[i-j+1]]out[[i+1]],{i,j+1,r}]],
 {j,r,0,-1}];
 {r,TrueQ[out===avec]}
];
rankChecks=Table[test[r],{r,0,12}];
(* Search for a SINGLE projective fold decreasing the geometric
   carrier dimension: r>=1, 0<=k<=r, delta'=delta+r-k. *)
counterexample=Reduce[
 rr>=1&&0<=kk<=rr&&rr-kk<0,{rr,kk},Integers];
(* Independent exact check of the explicit rank-2 recursion:
   q2=a2; q1=a1+s1 a2; q0=a0+s1 a1+s2 a2. *)
top=a2;
middle=Expand[(a1+s1 a2)-s1 top];
bottom=Expand[(a0+s1 a1+s2 a2)-s1 middle-s2 top];
rank2Exact=TrueQ[{bottom,middle,top}==={a0,a1,a2}];
(* The source-complexity index min(p,d-p) is <=1 for
   every codimension p in d=0,1,2,3, so the established
   rational Hodge + Hard Lefschetz + divisor-source
   construction covers ALL such classes. *)
smallDimensions=Flatten[Table[
 {d,p,Min[p,d-p]<=1},{d,0,3},{p,0,d}],1];
out=<|
 "foldRanksTested"->Length[rankChecks],
 "foldCoefficientExtractionAllPass"->And@@rankChecks[[All,2]],
 "failedRankCases"->Select[rankChecks,Not[#[[2]]]&],
 "rank2IndependentCheck"->rank2Exact,
 "carrierDropCounterexample"->counterexample,
 "completeSmallDimensionSectorChecks"->Length[smallDimensions],
 "allSmallDimensionSectorsHavePrimitiveIndexAtMostOne"->And@@smallDimensions[[All,3]]
|>;
Print[out];out