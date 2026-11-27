(* Exact Wolfram validation of the intrinsic GST PGL projective fold
  Chern extraction. Mathematical proof is a splitting-principle identity
  with center-shifted Chern roots y_i=x_i-Mean[x].
  Full theorem is in
  research/derivations/GST_higher_causal_projective_descent_torsion_gerbe_2026-10-23.tex
  These exact rational cases are regression checks; they do not
  assert universal existence of projective flat descent.
*)
ClearAll["Global`*"];
rootData={1,2,4,8,16,32};
cases=Flatten[Table[
 Module[{rr=Take[rootData,r],yy,den,pol},
  yy=rr-Mean[rr];
  den=Table[
   Product[If[j==i,1,yy[[i]]-yy[[j]]],{j,1,r}],
   {i,1,r}];
  pol=Normal[Series[
   Product[1/(1-yy[[i]] t),{i,1,r}],
   {t,0,6}]];
  Table[{r,k,TrueQ[FullSimplify[
   Sum[yy[[i]]^(r-1+k)/den[[i]],{i,1,r}]==
         Coefficient[pol,t,k]]]},{k,0,6}]
 ],{r,2,6}],1];
logChecks=Flatten[Table[
 Module[{rr=Take[rootData,r],yy,pol},
  yy=rr-Mean[rr];
  pol=Normal[Series[
   Log[Product[1/(1-yy[[i]] t),{i,1,r}]],
   {t,0,5}]];
  Table[{r,p,TrueQ[FullSimplify[
    Coefficient[pol,t,p]==
        (Factorial[p-1]/Factorial[p]) Total[yy^p]]]},
    {p,1,5}]
 ],{r,2,6}],1];
twistChecks=Table[
 Module[{rr=Take[rootData,r],m=Mean[Take[rootData,r]],a=7/3},
  {r,TrueQ[
    Take[rootData,r]-m==
      (Take[rootData,r]+a)-Mean[Take[rootData,r]+a]
    ]}
 ],{r,2,6}];
result=<|
 "projectiveGysinResidueTests"->Length[cases],
 "allGysinResiduesPass"->And@@cases[[All,3]],
 "gysinFailures"->Select[cases,Not[#[[3]]]&],
 "intrinsicSegreLogTests"->Length[logChecks],
 "allIntrinsicLogPass"->And@@logChecks[[All,3]],
 "logFailures"->Select[logChecks,Not[#[[3]]]&],
 "lineTwistInvarianceTests"->Length[twistChecks],
 "allTwistInvariancePass"->And@@twistChecks[[All,2]],
 "twistFailures"->Select[twistChecks,Not[#[[2]]]&]
|>;
Print[result];result