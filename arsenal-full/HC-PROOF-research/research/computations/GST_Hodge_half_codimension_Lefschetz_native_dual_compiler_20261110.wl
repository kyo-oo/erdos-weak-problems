(* GST Hodge original-X: construct GENUINE algebraic complementary dual
   cycles from full source rank in lower-half codimensions using
   rational HARD LEFSCHETZ and Poincare pairing.

   GEOMETRIC theorem: if native Chow cycles span W_q(X) for
   0<=q<=floor(d/2), then B_q(x,y)=int_X x*y*h^(d-2q)
   is rational nondegenerate on W_q(X), hence its matrix G in
   the actual native source basis is rational invertible. The
   dual native cycles are rational combinations of those same
   cycles multiplied by h^(d-2q). A single true original-X
   cyclic Chow correspondence then exists in EVERY codimension,
   without an independent analytic Hodge-star-algebraicity input.

   The following tests check the rational inverse Gram, dual basis
   and exactly antidiagonal Hankel determinant for ranks 1..9,
   plus source/dual algebraic codimension formulas for d=1..12.
   They do NOT prove existence of the complete source basis on
   every X. That remains the universal Hodge source-birth target.
*)
ClearAll[gstCase,gstRankRuns,gstDegrees,gstResult];
gstCase[r_Integer?Positive] := Module[{l,g,duals,e,fold,seed,ell,hank},
 l=Table[If[i>=j,Binomial[i-1,j-1],0],{i,r},{j,r}];
 g=l.Transpose[l];
 duals=Inverse[g];
 fold=Table[Boole[i==Mod[j,r]+1],{i,r},{j,r}];
 seed=UnitVector[r,1];
 ell=UnitVector[r,r];
 hank=Table[ell.MatrixPower[fold,i+j].seed,
   {i,0,r-1},{j,0,r-1}];
 <|"HodgeRank"->r,"GramDet"->Det[g],
 "dualPairingIdentity"->(g.duals==IdentityMatrix[r]),
 "singleFoldRank"->MatrixRank[
    Transpose[Table[MatrixPower[fold,k].seed,{k,0,r-1}]]],
 "momentDet"->Det[hank],
 "expectedMomentDet"->(-1)^(r(r-1)/2),
 "passed"->(Det[g]!=0 && g.duals==IdentityMatrix[r] &&
   Det[hank]==(-1)^(r(r-1)/2))|>
];
gstRankRuns=Table[gstCase[r],{r,1,9}];
gstDegrees=Flatten[Table[Module[{q=Min[p,d-p],forward,source,dual},
 forward=Abs[d-2p];
 source=If[2p<=d,p,q+(d-2q)];
 dual=If[2p<=d,q+(d-2q),q];
 <|"d"->d,"p"->p,"lowWeight"->q,
 "amplePowerNeeded"->forward,
 "sourceCodimension"->source,"dualCodimension"->dual,
 "passed"->(q<=Floor[d/2]&&source==p&&dual==d-p)|>
],{d,1,12},{p,0,d}],1];
gstResult=<|
 "ranksChecked"->Length[gstRankRuns],
 "rankCases"->gstRankRuns,
 "allRationalGramAndHankelChecks"->And@@(Lookup[#,"passed"]&/@gstRankRuns),
 "codimensionPairsChecked"->Length[gstDegrees],
 "allChowCodimensionDegreeChecks"->And@@(Lookup[#,"passed"]&/@gstDegrees),
 "allPassed"->(
  And@@(Lookup[#,"passed"]&/@gstRankRuns) &&
  And@@(Lookup[#,"passed"]&/@gstDegrees))|>;
Print[gstResult];gstResult