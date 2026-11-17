(* GST compact causal Hopf-vs-projective fold, exact arithmetic.
   Date: 2026-10-22. Target: uniform polynomial consequences of
   geometric sphere Gysin sequence and Euler top-Chern threshold.
   These tests do NOT formalize or prove existence of the analytic
   Hopf quotient, nor do they construct a Hodge counterexample
   on a smooth projective variety. No floating point; deterministic.
   Tested d=0..8, rank r=2..7, occupancy k=0..r, 297 cases.
*)
ClearAll[t,h,z,dd,rr,kk,base,evenPart,oddPart,
  spherePoly,breakPoly,purePoly,testRows,result];
base[dd_Integer?NonNegative] := Sum[t^(2j),{j,0,dd}];
evenPart[dd_Integer?NonNegative,rr_Integer?Positive] :=
  Sum[If[j<rr,t^(2j),0],{j,0,dd}];
oddPart[dd_Integer?NonNegative,rr_Integer?Positive] :=
  t^(2rr-1) Sum[If[j+rr>dd,t^(2j),0],{j,0,dd}];
spherePoly[dd_,rr_] := Expand[evenPart[dd,rr]+oddPart[dd,rr]];
breakPoly[dd_,rr_,kk_] :=
  If[kk<rr, Expand[(1+t)(1+t^(2rr-1))base[dd]],
    Expand[(1+t)spherePoly[dd,rr]]];
purePoly[dd_,rr_] :=
  Expand[base[dd] Sum[t^(2j),{j,0,rr}]];

testRows=Flatten[Table[
 Module[{chern=Expand[(1+h z)^kk],top,bp,pp,degree,formula,tests},
 top=Coefficient[chern,z,rr];
 bp=breakPoly[dd,rr,kk];
 pp=purePoly[dd,rr];
 degree=2(dd+rr);
 formula=Expand[(1+t)(1+t^Max[2dd+1,2rr-1])*
      Sum[t^(2j),{j,0,Min[dd,rr-1]}]];
 tests={
   top === If[kk==rr,h^rr,0], (* top Chern threshold *)
   Coefficient[bp,t,1]===1,   (* odd b1 in Hopf branch *)
   Coefficient[pp,t,1]===0,   (* even b1: CPd input *)
   Expand[bp/.t->-1]===0,    (* Hopf Euler chi=0 *)
   Expand[t^degree(bp/.t->1/t)-bp]===0, (* PD Hopf *)
   Expand[t^degree(pp/.t->1/t)-pp]===0, (* PD projective *)
   Coefficient[bp,t,degree]===1,
   Coefficient[pp,t,degree]===1,
   If[kk<rr,Expand[bp-(1+t)(1+t^(2rr-1))base[dd]]===0,True],
   If[kk==rr,Expand[bp-formula]===0,True]
 };
 {dd,rr,kk,And@@tests}
 ],{dd,0,8},{rr,2,7},{kk,0,rr}],2];

result=<|
 "testedTriples"->Length[testRows],
 "allChecksPass"->And@@testRows[[All,4]],
 "failedTriples"->Select[testRows,Not[#[[4]]]&],
 "CP2_rank2_projective"->purePoly[2,2],
 "CP2_rank2_occupancy1"->breakPoly[2,2,1],
 "CP2_rank2_occupancy2"->breakPoly[2,2,2],
 "CP2_rank2_topChern"->Coefficient[Expand[(1+h z)^2],z,2]
|>;
Print[result];result
