(* GST emergent-dimensional causal fold, exact Wolfram arithmetic.
   Mathematical source:
   research/derivations/GST_emergent_dimension_causal_hodge_fold_2026_10_21.tex
   Tests: all-N triangular Chern--Segre reconstruction for N=0..9
   with fixed exact integer Chern coefficients; symbolic N=3;
   actual smooth abelian surface partial-conjugation Hodge-type change.
   Finite checks are NOT proof of all-N geometry or Hodge conjecture. *)
ClearAll[t,c1,c2,c3,m,mi,eta,omega1,omega2,partialConj,
  hodgeCoeff,result,passes,depth,chern,seg,tt,inv];
m={{1,c1,c1^2-c2,c1^3-2c1*c2+c3},
   {0,1,c1,c1^2-c2},{0,0,1,c1},{0,0,0,1}};
mi={{1,-c1,c2,-c3},{0,1,-c1,c2},
    {0,0,1,-c1},{0,0,0,1}};
passes=Table[
 chern=Prepend[Table[2 i+1,{i,1,depth}],1];
 seg=ConstantArray[0,depth+1];seg[[1]]=1;
 Do[seg[[k+1]]=Sum[(-1)^(j+1) chern[[j+1]]
      seg[[k-j+1]],{j,1,k}],{k,1,depth}];
 tt=Table[If[i>=j,seg[[i-j+1]],0],
          {j,0,depth},{i,0,depth}];
 inv=Table[If[i>=j,(-1)^(i-j)chern[[i-j+1]],0],
          {j,0,depth},{i,0,depth}];
 {depth,TrueQ[tt.inv==IdentityMatrix[depth+1]&&
              inv.tt==IdentityMatrix[depth+1]]},
 {depth,0,9}];
eta=SparseArray[{{1,4}->1,{4,1}->-1,
                 {3,2}->-1,{2,3}->1},{4,4}];
omega1={1,0,I,0};omega2={0,1,0,I};
partialConj=DiagonalMatrix[{1,1,-1,1}];
hodgeCoeff[a_]:=Expand[Sum[a[[i,j]]
 (omega1[[k]]omega2[[l]]-omega1[[l]]omega2[[k]])
 Signature[{i,j,k,l}],
 {i,1,4},{j,1,4},{k,1,4},{l,1,4}]/4];
result=<|
 "N3SymbolicLeftInverse"->TrueQ[Simplify[m.mi==IdentityMatrix[4]]],
 "N3SymbolicRightInverse"->TrueQ[Simplify[mi.m==IdentityMatrix[4]]],
 "N0Through9ExactReconstruction"->passes,
 "InitialAbelianSurfaceHodge02Coefficient"->hodgeCoeff[eta],
 "FoldedAbelianSurfaceHodge02Coefficient"->
                         hodgeCoeff[partialConj.eta.partialConj],
 "PartialFoldInvolution"->TrueQ[partialConj.partialConj==IdentityMatrix[4]]|>;
If[!TrueQ[result["N3SymbolicLeftInverse"]]||
   !TrueQ[result["N3SymbolicRightInverse"]]||
   !And@@(Last/@passes)||
   !TrueQ[result["InitialAbelianSurfaceHodge02Coefficient"]==0]||
   !TrueQ[result["FoldedAbelianSurfaceHodge02Coefficient"]==-2 I]||
   !TrueQ[result["PartialFoldInvolution"]],
   Print["FAIL"];Abort[]];
Print[result];
Print["PASS exact finite calculation; geometric proof separate"];
