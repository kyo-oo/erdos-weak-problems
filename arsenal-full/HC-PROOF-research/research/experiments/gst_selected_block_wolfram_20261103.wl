ClearAll["Global`*"];
count=0; failures={};
assert[name_,value_]:=(count++;If[!TrueQ[value],AppendTo[failures,name]]);
bn[n_,k_]:=If[0<=k<=n,Binomial[n,k],0];
rows=Flatten[Table[Table[
  ks=Range[Max[0,s-m],Min[r,s]];
  cs=Table[bn[r-1,k-1]*bn[m,s-k]-bn[r,k]*bn[m-1,s-k-1],{k,ks}];
  assert["coefficient cancellation",Total[cs]===0];
  {r,m,s,cs},{s,0,r+m}],{r,1,4},{m,1,4}],2];
projector={{1+x,y},{z,1-x}}/2;
reduce[expression_]:=Last[PolynomialReduce[Expand[expression],{x^2+y*z-1},{y,z,x,e,t}]];
assert["projector",And@@(reduce[#]===0& /@ Flatten[projector.projector-projector])];
a=projector+e*DiagonalMatrix[{1,-1}];
chi=reduce[Det[t*IdentityMatrix[2]-a]];
assert["characteristic",Expand[chi-(t^2-t-e*x-e^2)]===0];
disc=Discriminant[chi,t];
assert["discriminant",Expand[disc-(1+4*e*x+4*e^2)]===0];
branches=Table[
 branch=-(1+4*eps^2)/(4*eps);lower=(1-2*eps)^2;
 assert["branch outside core",branch < -1];
 assert["branch smooth",1-branch^2!=0];
 assert["positive compact gap",lower>0];
 assert["branch root",(disc/.{e->eps,x->branch})===0];
 {ToString[eps,InputForm],ToString[branch,InputForm],ToString[lower,InputForm]},
 {eps,{1/10,1/4,1/3}}];
u={{0,1},{0,0}};v={{0,0},{1,0}};comm=u.v-v.u;
assert["nonzero obstruction",comm===DiagonalMatrix[{1,-1}]];
assert["traceless obstruction",Tr[comm]===0];
(* Newton's generating function independently computes the degree-p Chern term. *)
Do[
 homCharacter=Expand[(r+w*(-t)^p)*(m-w*t^p)];
 logChern=Sum[(-1)^(j-1)*(j-1)!*Coefficient[homCharacter,t,j]*zz^j,{j,1,p}];
 recovered=Coefficient[Normal[Series[Exp[logChern],{zz,0,p}]],zz,p];
 assert["polarized excess Newton coefficient",Expand[recovered-(-1)^(p-1)*(p-1)!*(m*(-1)^p-r)*w]===0],
 {p,1,6},{r,1,4},{m,1,4}];
ExportString[<|"all_passed"->(failures==={}),"assertion_count"->count,
 "failures"->failures,"kernel_version"->$Version,
 "coefficient_rows"->rows,"branch_rows"->branches,"commutator"->comm|>,"RawJSON","Compact"->True]
