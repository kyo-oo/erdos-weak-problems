(* Exact ordered-word implementation, independent of the Python bit-mask code.
   Every polynomial is a list {xExponent,yExponent,orderedOddWord,coefficient}.
   Command: submit this complete file to Wolfram Language evaluator, 60 seconds.
   No floating arithmetic, random inputs, historical-priority or Chow claim. *)
ClearAll["Global`*"];
count=0;failures={};
ck[p_,label_]:=(count++;If[!TrueQ[p],AppendTo[failures,label]]);
norm[p_]:=Select[({#[[1,1]],#[[1,2]],#[[1,3]],Total[#[[All,4]]]}& /@ GatherBy[p,Take[#,3]&]),Last[#]!=0&];
plus[p_,q_]:=norm[Join[p,q]];
times[p_,q_]:=Module[{out={},a,b,w,sign},
 Do[a=i[[1]]+j[[1]];b=i[[2]]+j[[2]];
 If[a<=1&&b<=1&&Intersection[i[[3]],j[[3]]]=={},
 sign=(-1)^Total[Flatten[Table[Boole[c>d],{c,i[[3]]},{d,j[[3]]}]]];
 w=Sort[Join[i[[3]],j[[3]]]];AppendTo[out,{a,b,w,sign*i[[4]]*j[[4]]}]],{i,p},{j,q}];norm[out]];
g[i_]:={{0,0,{i},1}};
words=SortBy[Subsets[Range[0,5]],Total[2^#]&];
ss=Flatten[Table[{a,b,w},{a,0,1},{b,0,1},{w,words}],2];
ix[s_]:=1+64*(2*s[[1]]+s[[2]])+Total[2^s[[3]]];
vec[p_]:=Normal[SparseArray[(ix[Take[#,3]]->#[[4]])& /@ p,{256}]];
single[s_]:={Append[s,1]};
sub[s_,im_]:=Fold[times,{{s[[1]],s[[2]],{},1}},im[[1+s[[3]]]]];
diff[s_,im_]:=Module[{out={},w=s[[3]],p},
 Do[p={{s[[1]],s[[2]],{},(-1)^(j-1)}};
 Do[p=times[p,g[k]],{k,Take[w,j-1]}];p=times[p,im[[1+w[[j]]]]];
 Do[p=times[p,g[k]],{k,Drop[w,j]}];out=plus[out,p],{j,Length[w]}];out];
apply[p_,fn_]:=norm[Flatten[(Function[t,Map[ReplacePart[#,4->#[[4]]*t[[4]]]&,fn[Take[t,3]]]] /@ p),1]];
degree[s_]:=2*(s[[1]]+s[[2]])+Total[If[#<4,1,3]& /@ s[[3]]];
oldIm={{{1,0,{},1}},{},{},{},{{1,1,{},1}},{}};
dm=Transpose[vec[diff[#,oldIm]]& /@ ss];
base=Transpose[vec[single[#]]& /@ Select[ss,#[[3]]=={}&]];
rows={};tm=AbsoluteTiming[
Do[Module[{f=Table[g[i],{i,0,5}],h=Table[g[i],{i,0,5}],newIm,newD,fm,hm,em,kdim},
 f[[5]]={{0,0,{4},1},{0,1,{0},-1},{0,0,{0,1,2},lam}};
 h[[5]]={{0,0,{4},1},{0,1,{0},1},{0,0,{0,1,2},-lam}};
 newIm={{{1,0,{},1}},{},{},{},If[lam==0,{},{{1,0,{1,2},lam}}],{}};
 newD[s_]:=diff[s,newIm];
 fm=Transpose[vec[sub[#,f]]& /@ ss];hm=Transpose[vec[sub[#,h]]& /@ ss];
 em=Transpose[vec[newD[#]]& /@ ss];
 ck[fm.hm==IdentityMatrix[256],{"forward-inverse",lam}];
 ck[hm.fm==IdentityMatrix[256],{"inverse-forward",lam}];
 ck[dm.fm==fm.em,{"chain",lam}];ck[em.em==ConstantArray[0,{256,256}],{"square",lam}];
 Do[ck[And@@(degree[Take[#,3]]==degree[s]& /@ sub[s,f]),{"absolute-degree",lam,s}],{s,ss}];
 kdim=MatrixRank[em]+4-MatrixRank[Join[em,base,2]];
 ck[kdim==2,{"marked-kernel",lam}];
 ck[vec[apply[{{0,0,{4},1},{0,0,{0,1,2},-lam}},newD]]==ConstantArray[0,256],{"corrected-closed",lam}];
 ck[(newD[{0,0,{4}}]=={})==(lam==0),{"W-closed",lam}];
 AppendTo[rows,{lam,256,kdim,lam==0}]],{lam,{-2,-1,0,1,2}}];][[1]];
(* Complete degree-five secondary coset: only x*v,y*v are indeterminate.
   Use the same ordered words but only generators u=0,v=1, both degree 3. *)
smallStates=Flatten[Table[{a,b,w},{a,0,1},{b,0,1},{w,{{},{0},{1},{0,1}}}],2];
smallDegree[s_]:=2*(s[[1]]+s[[2]])+3*Length[s[[3]]];
smallD[s_]:=diff[s,{{{1,1,{},1}},{}}];
bounds=vec[smallD[#]]& /@ Select[smallStates,smallDegree[#]==4&];
ind={vec[{{1,0,{1},1}}],vec[{{0,1,{1},1}}]};m=vec[{{0,1,{0},-1}}];
ri=MatrixRank[Join[bounds,ind]];rj=MatrixRank[Append[Join[bounds,ind],m]];
ck[ri==2&&rj==3,"secondary-coset"];
ck[smallD[{0,1,{0}}]=={},"secondary-closed"];
ck[Length[Select[smallStates,smallDegree[#]==3&]]==2,"degree-three-domain"];
ExportString[<|"all_passed"->(failures=={}),"assertions"->count,"failures"->failures,
 "nonlinear_rows"->rows,"massey_ranks"->{ri,rj},"kernel_version"->$Version,
 "runtime_seconds"->tm|>,"RawJSON","Compact"->True]
