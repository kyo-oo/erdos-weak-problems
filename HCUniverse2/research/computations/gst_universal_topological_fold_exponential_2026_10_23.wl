(* Exact full-grade GST spatial Chern-Segre fold audit.
   Input: arbitrary X,p,alpha realized through the rational
   topological K-theory purity ch(E)=rank+m alpha.
   Universal mathematical proof uses splitting principle and
   log(1/c(E,-t))=Sum[(k-1)! ch_k(E) t^k].
   Finite Wolfram checks verify coefficients only, not an all-X
   projective algebraization theorem.
*)
coeffTests=Flatten[Table[
 Module[{z=Unique["z"],a=Unique["a"],poly},
  poly=Normal[Series[Exp[Factorial[p-1] a z^p],{z,0,d}]];
  Table[With[{expected=If[Mod[k,p]==0,
       (Factorial[p-1] a)^(k/p)/Factorial[k/p],0]},
    {p,d,k,TrueQ[FullSimplify[Coefficient[poly,z,k]==expected]]}
  ],{k,0,d}]
 ],{p,1,8},{d,p,12}],2];
genericQuotient=1/((1-x t)(1-y t));
genericRationalExp=Sum[(x^k+y^k)*t^k/k,{k,1,8}];
rootLogCheck=TrueQ[FullSimplify[
  Normal[Series[Log[genericQuotient],{t,0,8}]]==
  genericRationalExp]];
(* Actual algebraic paired projective bundles over CP^2:
   E+=O(1)+O(-1), E-=O+O. CP^2 has h^3=0.
   Their ratio of Segre series is exp(h^2 t^2). *)
cp2FoldRatio=Normal[Series[1/(1-h^2 t^2),{t,0,4}]]/.h^4->0;
cp2PureExp=Normal[Series[Exp[h^2 t^2],{t,0,4}]]/.h^4->0;
cp2Check=TrueQ[FullSimplify[cp2FoldRatio==cp2PureExp]];
(* Independent geometric incidence-complement check:
   for an original projective X=P^d embedded in P^N,
   the closed incidence over X has fiber P^(N-1).
   Its open complement has E_c=P_d(w) (P_N(w)-P_(N-1)(w)).
   The formula must equal w^N P_d(w), with N>=d. *)
projectiveHodge[n_Integer]:=If[n<0,0,Sum[w^j,{j,0,n}]];
affineFoldHodgeChecks=Flatten[Table[
 {d,n,TrueQ[Expand[projectiveHodge[d]*
   (projectiveHodge[n]-projectiveHodge[n-1])-
   w^n projectiveHodge[d]]===0]},
 {d,0,8},{n,d,12}],1];
result=<|
 "testedChernSegreGradeCoefficients"->Length[coeffTests],
 "passedCoefficients"->Count[coeffTests,{_,_,_,True}],
 "failedCoefficients"->Select[coeffTests,Not[#[[4]]]&],
 "genericRootLogIdentity"->rootLogCheck,
 "algebraicCP2FoldProjectiveBundle"->cp2Check,
 "cp2FoldPolynomial"->cp2FoldRatio,
 "affineIncidenceFoldCases"->Length[affineFoldHodgeChecks],
 "affineIncidenceFoldAllPass"->And@@affineFoldHodgeChecks[[All,3]],
 "affineIncidenceFoldFailures"->Select[affineFoldHodgeChecks,Not[#[[3]]]&],
 "p3Series"->Normal[Series[Exp[2 a t^3],{t,0,9}]]
|>;
Print[result];result