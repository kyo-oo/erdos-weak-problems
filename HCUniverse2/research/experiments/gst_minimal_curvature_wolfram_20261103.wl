ClearAll["Global`*"];
count=0; failures={};
check[q_,tag_]:=(count++;If[!TrueQ[q],AppendTo[failures,tag]]);
zero={0,0,0,0};
mul[a_,b_]:={a[[1]] b[[1]],a[[1]] b[[2]]+a[[2]] b[[1]],a[[1]] b[[3]]+a[[3]] b[[1]],a[[1]] b[[4]]+a[[2]] b[[3]]+a[[3]] b[[2]]+a[[4]] b[[1]]};
rr[rows_]:=If[Length[rows]==0,0,MatrixRank[rows]];
mu[cs_]:=Module[{i,mi,base=IdentityMatrix[4]},i=Flatten[Table[mul[b,c],{b,base},{c,cs}],1];mi=Flatten[Table[mul[b,c],{b,Rest[base]},{c,cs}],1];rr[i]-rr[mi]];
ones=({0,#[[1]],#[[2]],0}& /@ Tuples[{-1,0,1},2]);
triples=Tuples[ones,3];hist=ConstantArray[0,3];
Do[k=mu[cs];check[k==MatrixRank[cs[[All,{2,3}]]],"same-degree-quotient"];hist[[k+1]]++,{cs,triples}];
Do[cs={a,b,{0,0,0,z}};expected=MatrixRank[{a[[{2,3}]],b[[{2,3}]]}]+If[a==zero&&b==zero&&z!=0,1,0];check[mu[cs]==expected,"mixed-degree-quotient"],{a,ones},{b,ones},{z,{-1,0,1}}];
check[hist=={1,104,624},"histogram"];
Do[b=Prepend[bc,0];check[mul[mul[b,b],b]==zero,"nilpotent-order"];Do[check[(x-mul[b,x]==zero)==(x==zero),"fixed-point"],{x,Tuples[{-1,0,1},4]}],{bc,Tuples[{-1,0,1},3]}];
check[mu[{{0,1,0,0},{0,0,1,0}}]==2,"syzygy-not-free-handle"];
cohom[dims_,ps_,curvs_]:=Module[{r=Length[ps],bb,states,degs,top,d,mask,exp,bit,target,sgn,idx,ranks,groups},
 bb=Tuples[Range[0,#]& /@ dims];states=Tuples[{bb,Range[0,2^(2r)-1]}];
 degs=Table[2 Total[s[[1]]]+Sum[If[BitAnd[s[[2]],2^i]!=0,2ps[[Floor[i/2]+1]]-1,0],{i,0,2r-1}],{s,states}];
 top=Max[degs];d=ConstantArray[0,{Length[states],Length[states]}];
 Do[exp=states[[j,1]];mask=states[[j,2]];
  Do[bit=2(i-1);If[BitAnd[mask,2^bit]!=0,
   target=exp+curvs[[i]];
   If[And@@Thread[target<=dims],
    idx=First@FirstPosition[states,{target,mask-2^bit}];
    sgn=(-1)^DigitCount[BitAnd[mask,2^bit-1],2,1];d[[idx,j]]+=sgn]],{i,1,r}],{j,Length[states]}];
 check[d.d==ConstantArray[0,Dimensions[d]],"whole-d-square"];
 groups=Table[Flatten@Position[degs,k],{k,0,top}];
 ranks=Table[If[Length[groups[[k+1]]]==0||Length[groups[[k+2]]]==0,0,MatrixRank[d[[groups[[k+2]],groups[[k+1]]]]]],{k,0,top-1}];
 Table[Length[groups[[k+1]]]-If[k<top,ranks[[k+1]],0]-If[k>0,ranks[[k]],0],{k,0,top}]];
clock=AbsoluteTiming[
 p3=cohom[{3},{1,2,3},{{1},{2},{3}}];
 p11=cohom[{1,1},{1,1,2},{{1,0},{0,1},{1,1}}];][[1]];
expected3=CoefficientList[Expand[(1+t)(1+t^7)(1+t^3)^2(1+t^5)^2],t];
expected11=CoefficientList[Expand[(1+t)^2(1+t^3)^4],t];
check[p3==expected3,"P3-full-factor"];
check[p11==expected11,"P1P1-full-factor"];
ExportString[<|"all_passed"->(failures=={}),"assertions"->count,"failures"->failures,"normal_form_cases"->972,"histogram"->hist,"nilpotent_fixed_point_cases"->2187,"P3_spectrum"->p3,"P1P1_spectrum"->p11,"cohomology_runtime_seconds"->clock,"kernel_version"->$Version|>,"RawJSON","Compact"->True]
