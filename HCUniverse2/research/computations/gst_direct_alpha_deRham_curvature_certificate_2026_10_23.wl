(* Exact Mathbox certificate for the alpha-dependent GST algebraic
   de Rham projector equation. These tests certify the matrix
   equations and correct normalization in stated ranges, not
   unconditional existence for every Hodge alpha. *)
ClearAll["Global`*"];
(* True incidence rank-one P on J(P1):
   x=(1,u), ell=(1,v), denominator 1+u v.
   F_{u v}=Tr P (P_u P_v - P_v P_u). *)
pp={{1,v},{u,u v}}/(1+u v);
pu=D[pp,u];pv=D[pp,v];
omega=FullSimplify[Tr[pp.(pu.pv-pv.pu)]];
rankOne=<|
 "P2equalsP"->TrueQ[FullSimplify[pp.pp-pp]==ConstantArray[0,{2,2}]],
 "TraceOne"->TrueQ[FullSimplify[Tr[pp]]==1],
 "ExactOmegaDuDv"->omega,
 "ExpectedCurvature"->TrueQ[FullSimplify[omega+1/(1+u v)^2]==0]
|>;
(* Full rational degree-two Chern source in true Gr(2,5).
   Use h^2 and independent Schubert s2. *)
ch2S=h^2/2-s2;
ch2Line=h^2/2;
theta=2h^2/5-s2;
grassmann=<|
 "ch2S"->ch2S,
 "ch2Line"->ch2Line,
 "fiveTimesTargetSolved"->TrueQ[Expand[5 ch2S-ch2Line-5 theta]===0],
 "rationalSourceCoefficient"->{1,-1/5}
|>;
(* Every tangent Q to any idempotent is off-diagonal,
   and Q=[[Q,P],P]. Construct exact nontrivial integer tests. *)
testTangent[m_,r_]:=Module[{p,q,lin,g,comm},
 p=DiagonalMatrix[Join[ConstantArray[1,r],ConstantArray[0,m-r]]];
 q=Table[If[Xor[i<=r,j<=r],2i+3j,0],{i,m},{j,m}];
 lin=p.q+q.p-q;
 g=q.p-p.q;
 comm=g.p-p.g-q;
 {m,r,lin==ConstantArray[0,{m,m}],
      comm==ConstantArray[0,{m,m}]}
];
tangentTests=Flatten[Table[testTangent[m,r],{m,1,9},{r,0,m}],1];
(* Genuine Chow-graded Newton source, not assuming equal lower Chern:
   for EVERY rank r and codimension p<=r, compare the
   integer Newton polynomial in c_j with the power sum
   of independently symbolic Chern roots. *)
newtonTest[rr_,pp_]:=Module[{roots,cs,ns},
 roots=Array[cc,rr];
 cs=Table[Total[Times@@@Subsets[roots,{j}]],{j,1,pp}];
 ns=ConstantArray[0,pp];ns[[1]]=cs[[1]];
 Do[ns[[n]]=Expand[Sum[(-1)^(j-1)cs[[j]] ns[[n-j]],
                       {j,1,n-1}]+(-1)^(n-1)n cs[[n]]],
                 {n,2,pp}];
 {rr,pp,TrueQ[Expand[ns[[pp]]-Total[roots^pp]]===0]}
];
newtonTests=Flatten[Table[newtonTest[rr,pp],
                      {rr,1,7},{pp,1,rr}],1];
(* A sharp p=2 counterexample to replacing ch2-differences
   with c2-differences when LOWER ch are not equal:
   E+ roots {1,1}, E- roots {0,1}. *)
rootsPlus={1,1};rootsMinus={0,1};
ch2Diff=Total[rootsPlus^2]/2-Total[rootsMinus^2]/2;
c2Diff=Times@@rootsPlus-Times@@rootsMinus;
newtonP2Diff=((Total[rootsPlus])^2-2 Times@@rootsPlus -
    ((Total[rootsMinus])^2-2 Times@@rootsMinus))/2;
out=<|
 "rankOne"->rankOne,
 "allNewtonRankCodimPairs"->Length[newtonTests],
 "NewtonAllPass"->And@@newtonTests[[All,3]],
 "NewtonFailures"->Select[newtonTests,Not[#[[3]]]&],
 "ExampleCh2Difference"->ch2Diff,
 "ExampleC2Difference"->c2Diff,
 "NaiveTopChernDifferenceWrong"->TrueQ[ch2Diff!=c2Diff],
 "FullMinorPolynomialCorrect"->TrueQ[ch2Diff==newtonP2Diff],
 "Gr25"->grassmann,
 "allTangentPairs"->Length[tangentTests],
 "allTangentEquationsHold"->And@@Flatten[tangentTests[[All,3;;4]]],
 "tangentFailures"->Select[tangentTests,Not[And@@#[[3;;4]]]&]
|>;
Print[out];out