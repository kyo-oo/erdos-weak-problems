(* GST vertical Chow residue and graph-incidence exact audit.
   Exact symbolic arithmetic. r=1..8, k=0..r: 44 checks.
   Additional full symbolic genus identity and g=0..5.
   This does not prove universal Hodge-to-Chow surjectivity.
*)
coefRec[rr_Integer?Positive,nn_Integer?NonNegative] :=
 If[nn==0,1,Expand[Sum[(-1)^(jj+1) cc[jj] coefRec[rr,nn-jj],
 {jj,1,Min[rr,nn]}]]];
fiberPush[rr_Integer?Positive,mm_Integer] :=
 If[mm<rr,0,coefRec[rr,mm-rr]];
residueSelector[rr_Integer?Positive,kk_Integer?NonNegative] :=
 Expand[Sum[(-1)^jj If[jj==0,1,cc[jj]] fiberPush[rr,rr+kk-jj],
 {jj,0,rr}]];
selectorChecks = Flatten[Table[
 {rr,kk,residueSelector[rr,kk] === If[kk==0,1,0]},
 {rr,1,8},{kk,0,rr}],1];
gramCurve[gen_] := {{0,1,1},{1,0,1},{1,1,2-2gen}};
hv={1,1,0};deltaV={0,0,1};primitiveV=deltaV-hv;
pair[gen_,u_,v_]:=Expand[u.gramCurve[gen].v];
genusChecks=Table[{gen,pair[gen,primitiveV,primitiveV],
 pair[gen,primitiveV,hv],Det[gramCurve[gen]]},{gen,0,5}];
result=<|"selectorCases"->Length[selectorChecks],
"selectorPassed"->Count[selectorChecks,{_,_,True}],
"selectorFailed"->Cases[selectorChecks,{_,_,False}],
"universalGramDet"->Factor[Det[gramCurve[genus]]],
"universalPrimitiveSquare"->Factor[pair[genus,primitiveV,primitiveV]],
"universalPrimitiveHyperplanePair"->pair[genus,primitiveV,hv],
"genusChecks"->genusChecks,
"rank2"->Table[residueSelector[2,kk],{kk,0,2}],
"rank3"->Table[residueSelector[3,kk],{kk,0,3}]|>;
Print[result];result