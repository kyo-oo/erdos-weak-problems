(* Exact Mathematica source: all-X topological twist Chern polynomial and N-world carry.
   Proof of the universal identities is in the matching LaTeX.
   These finite checks are only independent tests, not Hodge/Chow proofs. *)
ClearAll[carryWeight, carryMoment, twistChern, absMoment, cc, hh, tt, pp, rr, j, q, result];
carryWeight[pp_Integer,j_Integer]:=(-1)^(j-1) Binomial[pp+1,j];
carryMoment[pp_Integer,q_Integer]:=Sum[carryWeight[pp,j] j^q,{j,1,pp+1}];
twistChern[rr_Integer,pp_Integer,t_]:=
 Sum[Binomial[rr-i,pp-i] t^(pp-i) hh^(pp-i) cc[i],{i,0,pp}];
absMoment[pp_Integer]:=Sum[Abs[carryWeight[pp,j]] j^pp,{j,1,pp+1}];
result=Table[
<|"p"->pp,
  "worldWeights"->Table[carryWeight[pp,j],{j,1,pp+1}],
  "moments"->Table[carryMoment[pp,q],{q,0,pp}],
  "momentIdentity"->TrueQ[Table[carryMoment[pp,q],{q,0,pp}]==Join[{1},ConstantArray[0,pp]]],
  "topChernChecks"->Table[
   TrueQ[Expand[Sum[carryWeight[pp,j] twistChern[rr,pp,j],{j,1,pp+1}]-cc[pp]]==0],
    {rr,pp,pp+4}],
  "uncorrelatedMassLeadingFactor"->absMoment[pp]|>,
 {pp,1,8}];
allPassed=And@@Flatten[Join[result[[All,"momentIdentity"]],Flatten[result[[All,"topChernChecks"]]]]];
Print[<|"allPassed"->allPassed,"numberRankTests"->40,
 "weights_p2"->result[[2,"worldWeights"]],
 "weights_p3"->result[[3,"worldWeights"]],
 "massFactors_p1_through_p8"->result[[All,"uncorrelatedMassLeadingFactor"]]|>];
If[!TrueQ[allPassed],Abort[]];
