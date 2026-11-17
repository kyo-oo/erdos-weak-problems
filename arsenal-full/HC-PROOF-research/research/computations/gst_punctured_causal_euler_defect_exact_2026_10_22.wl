(* GST punctured-bundle exact causal Euler defect checks, 22 October 2026.
   Projective-space grading: d=0..8, r=2..7, k=0..r, p=0..d.
   Rational algebra/Hodge defect models: all 81 parameter quadruples
   a,b,c,h in {-1,0,1}; maps send algebraic generator to algebraic
   generator. Exact arithmetic, no floating point.
   DOES NOT prove the geometric localization or a universal
   prescribed Hodge-to-Chow source; proof in associated LaTeX.
*)
ClearAll[bettiRank,eulerRank,gradedChecks,v0,v3,matrank,
 modelRows,hh,tt,cc,aa,bb,dd,rr,kk,pp];
bettiRank[dd_,pp_]:=If[0<=pp<=dd,1,0];
eulerRank[dd_,rr_,kk_,pp_]:=If[kk==rr&&rr<=pp<=dd,1,0];
gradedChecks=Flatten[Table[
 {dd,rr,kk,pp,bettiRank[dd,pp]-eulerRank[dd,rr,kk,pp],
 If[kk<rr||pp<rr,bettiRank[dd,pp],0]},
 {dd,0,8},{rr,2,7},{kk,0,rr},{pp,0,dd}],3];
v0={{1},{0}};v3={{1},{0},{0}};
matrank[xx_]:=MatrixRank[xx];
modelRows=Flatten[Table[
 Module[{tt={{aa,bb},{0,cc},{0,hh}},dimd0,dimd3,rankimage,dimopen},
 dimd0=2-matrank[v0];dimd3=3-matrank[v3];
 rankimage=matrank[Join[v3,tt,2]]-matrank[v3];
 dimopen=3-matrank[Join[v3,tt,2]];
 {aa,bb,cc,hh,dimd3==rankimage+dimopen&&dimd0==1&&
 rankimage==If[cc==0&&hh==0,0,1]&&rankimage<=dimd0}],
 {aa,-1,1},{bb,-1,1},{cc,-1,1},{hh,-1,1}],3];
result=<|"projectiveSpaceCases"->Length[gradedChecks],
"projectiveSpacePass"->And@@(#[[5]]==#[[6]]&/@gradedChecks),
"rationalDefectModels"->Length[modelRows],
"rationalModelsPass"->And@@modelRows[[All,5]],
"failedModelInputs"->Select[modelRows,Not[#[[5]]]&]|>;
Print[result];result