ClearAll["Global`*"];
count=0;failures={};assert[name_,v_]:=(count++;If[!TrueQ[v],AppendTo[failures,name]]);
(* Independent signed-list exterior implementation, not Python's bit masks. *)
boundary[indices_,m_,r_,kk_]:=Module[{terms={},a,pos,j,seq},
 Do[If[MemberQ[indices,2*m+2*a-1],
  pos=First@FirstPosition[indices,2*m+2*a-1];
  Do[seq=Join[Take[indices,pos-1],{2*j-1,2*j},Drop[indices,pos]];
   If[DuplicateFreeQ[seq]&&kk[[a,j]]!=0,
    AppendTo[terms,{Sort[seq],(-1)^pos*kk[[a,j]]*Signature[seq]}]],{j,m}]],{a,r}];terms];
spectrum[m_,r_,kk_]:=Module[{n=2*(m+r),bases,matrices,ranks,bs,rho,columns,targets,rules},
 bases=Table[Subsets[Range[n],{k}],{k,0,n}];
 matrices=Table[
  columns=bases[[k+1]];targets=bases[[k+2]];
  rules=Flatten[MapIndexed[Function[{col,position},
    ({First@FirstPosition[targets,First[#]],First[position]}->Last[#]& /@
       boundary[col,m,r,kk])],columns],1];
  SparseArray[rules,{Length[targets],Length[columns]}],{k,0,n-1}];
 Do[assert["boundary squared",AllTrue[Flatten[Normal[matrices[[k+1]].matrices[[k]]]],#===0&]],
   {k,1,Length[matrices]-1}];
 ranks=Append[MatrixRank /@ matrices,0];
 bs=Table[Binomial[n,k]-ranks[[k+1]]-If[k==0,0,ranks[[k]]],{k,0,n}];
 rho=If[m==0||r==0,0,MatrixRank[kk]];
 assert["duality",bs===Reverse[bs]];
 If[n>0,assert["whole opposedness",bs[[2]]-2*(m+r-rho)===rho]];
 {m,r,kk,bs,ranks,rho,m+r-rho}];
rows={spectrum[0,0,{}],spectrum[1,0,{}],spectrum[0,1,{{}}]};
Do[AppendTo[rows,spectrum[m,1,{Table[If[j<=t,1,0],{j,m}]}]],{m,0,4},{t,0,m}];
Do[AppendTo[rows,spectrum[item[[1]],Length[item[[2]]],item[[2]]]],
 {item,{{2,{{1,0},{0,1}}},{2,{{1,1},{2,2}}},{2,{{1,0},{-1,0}}},{3,{{1,0,1},{0,1,1}}}}}];
hist=Counts[MatrixRank[Partition[#,2]]& /@ Tuples[{-1,0,1},4]];
ExportString[<|"all_passed"->(failures==={}),"assertion_count"->count,"failures"->failures,
 "kernel_version"->$Version,"spectral_rows"->rows,
 "matrix_rank_histogram_2x2"->Table[Lookup[hist,k,0],{k,0,2}]|>,"RawJSON","Compact"->True]
