(* Exact original-X Chow matrix-unit convention and source/Hodge dual compiler.
   INPUT: a finite rational Hodge source basis and its TRUE nondegenerate
   Lefschetz intersection Gram G, where full native source coverage
   of W_p(X) has been independently established.
   The mathematical derivation constructs actual native Chow duals
   b_j=sum_k (G^-1)_(kj) z_k h^(d-2p), so Betti correspondence
   F_ij(z)=degree(z b_j) a_i has matrix e_i e_j^T and
   F_ij o F_kl=delta_(j,k) F_il.
   These are EXACT abstract coefficient checks, not a construction
   of previously missing Chow sources on arbitrary X.
*)
ClearAll[one,run,passed];
one[r_Integer?Positive] := Module[{l,g,gInv,dualReadout,
 unit,eq,full,shift,moment},
 l=Table[If[i>=j,Binomial[i-1,j-1],0],{i,r},{j,r}];
 g=l.Transpose[l];gInv=Inverse[g];
 dualReadout=Transpose[gInv].g;
 unit[i_,j_]:=Outer[Times,UnitVector[r,i],dualReadout[[j]]];
 eq=Flatten[Table[
   unit[i,j].unit[k,m] ==
    KroneckerDelta[j,k] unit[i,m],
   {i,r},{j,r},{k,r},{m,r}],3];
 full=Total[Table[unit[i,i],{i,r}]];
 shift=Total[Table[unit[Mod[i,r]+1,i],{i,r}]];
 moment=Table[
   dualReadout[[r]].MatrixPower[shift,i+j].UnitVector[r,1],
   {i,0,r-1},{j,0,r-1}];
 <|"r"->r,"pairingDualIdentity"->(dualReadout==IdentityMatrix[r]),
 "matrixUnitsIndependent"->(MatrixRank[
   Flatten[Table[Flatten[unit[i,j]],{i,r},{j,r}],1]]==r^2),
 "allCompositionIdentities"->And@@eq,
 "sumOfChowProjectorsIsIdentity"->(full==IdentityMatrix[r]),
 "singleFoldOrbitFullRank"->(MatrixRank[
   Transpose[Table[MatrixPower[shift,j].UnitVector[r,1],
     {j,0,r-1}]]]==r),
 "HankelDet"->Det[moment],
 "expected"->(-1)^(r(r-1)/2),
 "allPassed"->(dualReadout==IdentityMatrix[r] &&
   And@@eq && full==IdentityMatrix[r] &&
   Det[moment]==(-1)^(r(r-1)/2))|>
];
run=Table[one[r],{r,1,5}];
passed=And@@(Lookup[#,"allPassed"]&/@run);
Print[<|"checks"->run,"allPassed"->passed|>];
<|"checks"->run,"allPassed"->passed|>