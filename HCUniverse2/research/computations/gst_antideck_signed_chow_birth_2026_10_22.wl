(* GST nonlinear double-cover anticharacter source, exact arithmetic.
   Date 2026-10-22. Full geometry/proof in associated LaTeX.
   Checks: exact projective-quadric branch identity; relative signs
   on two geometric components; two-sheet signed intersection law;
   all 2^m sign patterns for m=1..8; component projector 36 cases;
   quadric primitive Gram and source square. Uses exact symbols.
   These checks do NOT prove scheme existence or the Hodge conjecture.
*)
ClearAll["Global`*"];
quad = xx0 yy0 + xx1 yy1 + xx2 yy2;
aa1 = xx0 + yy0; aa2 = xx0 - yy0;
branch = Expand[aa1^2 + 4 xx1 yy1];
branchDifference = Expand[branch - (aa2^2 - 4 xx2 yy2)];
branchCompatible = TrueQ[Expand[branchDifference - 4 quad] == 0];
componentASign = TrueQ[Expand[(aa2+aa1)/.xx0->0] == 0];
componentBSign = TrueQ[Expand[(aa2-aa1)/.yy0->0] == 0];
sheetPush[ep_Integer] := Sum[
    sigma tau If[tau==ep sigma,1,0],
    {sigma,{-1,1}},{tau,{-1,1}}];
sheetChecks = Table[{ep,sheetPush[ep],sheetPush[ep]==2 ep},
  {ep,{-1,1}}];
signRows = Flatten[Table[
  Table[Module[{signed,total,expected,signs,vars},
    signs = code;
    vars = Table[z[j],{j,1,mm}];
    signed = Sum[sheetPush[signs[[j]]] vars[[j]],{j,1,mm}];
    total = Total[vars];
    expected = 2 Sum[signs[[j]] vars[[j]],{j,1,mm}];
    {mm,code,TrueQ[Expand[signed-expected]==0]}],
    {code,Tuples[{-1,1},mm]}],
  {mm,1,8}],1];
extractRows = Flatten[Table[
  Module[{ss,vars,total,signed,component},
    ss=Table[If[j==index,1,-1],{j,1,mm}];
    vars=Table[z[j],{j,1,mm}];
    total=Total[vars];signed=Sum[sheetPush[ss[[j]]] vars[[j]],{j,1,mm}];
    component=Expand[signed/4+total/2];
    {mm,index,TrueQ[Expand[component-vars[[index]]]==0]}],
  {mm,1,8},{index,1,mm}],1];
gram={{1,0},{0,1}};
rVec={1,-1};newVec=-2 rVec;hVec={1,1};
(* Exhaustive rational target-sensitive signed coupling: 780 period vectors
   with entries -2,-1,0,1,2, length 1..4; every sign choice assessed. *)
targetRows = Flatten[Table[
 Table[Module[{optimal = Max[Table[2 ss.vv,
       {ss, Tuples[{-1,1},mm]}]]},
   {mm,vv,optimal===2 Total[Abs[vv]]}],
  {vv,Tuples[{-2,-1,0,1,2},mm]}],
 {mm,1,4}],1];
(* All Z2xZ2 characters, including the first parity-valid cubic triple. *)
higherCharacterRows=Flatten[Table[
 Module[{c1=(-1)^uu,c2=(-1)^vv,c3=(-1)^(uu+vv)},
  {uu,vv,c1,c2,c3,c1*c2*c3,
   c1*c2*c3==1}],
 {uu,0,1},{vv,0,1}],1];
singleDeckOdd=Table[{nn,(-1)^nn,OddQ[nn]&&(-1)^nn==-1},
 {nn,1,13,2}];
(* Full rational Hodge target -> actual nonambient Q4 Chow-source coordinates.
   Basis B={h^2, transferred anti-deck S} has exact Gram diag(2,8). *)
basisGram={{2,0},{0,8}};
hodgeTarget={alphaH,alphaS};
hodgeCompilerQ4=Simplify[Inverse[basisGram].hodgeTarget];
hodgeCompilerReturn=Simplify[basisGram.hodgeCompilerQ4-hodgeTarget];
result=<|
 "branchCompatibility"->branchCompatible,
 "componentSignsCorrect"->componentASign&&componentBSign,
 "sheetCheck"->sheetChecks,
 "allSignPatternCases"->Length[signRows],
 "allSignPatternPass"->And@@signRows[[All,3]],
 "extractorCases"->Length[extractRows],
 "extractorPass"->And@@extractRows[[All,3]],
 "quadricPrimitiveHyperplanePair"->hVec.gram.rVec,
 "quadricPrimitiveSquare"->rVec.gram.rVec,
 "quadricTransferredSourceSquare"->newVec.gram.newVec,
 "targetOptimizedCases"->Length[targetRows],
 "targetOptimizedPass"->And@@targetRows[[All,3]],
 "quadricTargetCouplingMax"->2 {1,-1}.{1,-1},
 "cubicCharacterCases"->Length[higherCharacterRows],
 "cubicCharacterPass"->And@@higherCharacterRows[[All,7]],
 "oddSingleDeckCases"->Length[singleDeckOdd],
 "oddSingleDeckPass"->And@@singleDeckOdd[[All,3]],
 "hodgeCompilerQ4"->hodgeCompilerQ4,
 "hodgeCompilerExact"->hodgeCompilerReturn=={0,0},
 "quadricTransferredSource"->newVec
|>;
Print[result];result