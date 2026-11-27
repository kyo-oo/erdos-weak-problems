(* Exact Mathbox audit of the alpha-dependent high positive-twist
   topological Chern identity. Claim in companion LaTeX is proved
   for ALL ranks/codimensions via the splitting principle.
   Finite test: independently expand Chern roots for 1<=p<=r<=7.
*)
ClearAll["Global`*"];
checkRootIdentity[rr_Integer,pp_Integer]:=
 Module[{xs=Array[x,rr],roots,lhs,rhs,cj},
  roots=Table[x[i]+q,{i,1,rr}];
  lhs=Expand[Total[Times@@@Subsets[roots,{pp}]]];
  cj[j_Integer]:=If[j==0,1,
            Total[Times@@@Subsets[xs,{j}]]];
  rhs=Expand[Sum[Binomial[rr-j,pp-j] q^(pp-j) cj[j],
                                                  {j,0,pp}]];
  TrueQ[Expand[lhs-rhs]===0]
 ];
rootTests=Flatten[Table[{r,p,checkRootIdentity[r,p]},
                          {r,1,7},{p,1,r}],1];
(* Exact separate sufficient rational lattice gap:
  if a/denA and b/m differ nontrivially their gap >=1/(Qm).
  Integer numerator test is independent of the Chern identity. *)
latticeTests=Flatten[Table[
 {denA,m,a,b,TrueQ[(Abs[b/m-a/denA] < 1/(denA m)) ==
                                       (b/m == a/denA)]},
 {denA,1,6},{m,1,6},{a,-3,3},{b,-3,3}],3];
(* For a mass O(k^p) and angular error O(k^-1/2),
   the product mass*(angle)^2 is O(k^(p-1)).
   Its exponent is nonnegative for every p>=1. *)
angleExponents=Table[{p,p-1},{p,1,8}];
(* Actual codimension-two Grassmannian Hodge-period SOURCE-TYPE test.
   For Gr(2,5), roots xx,yy of S-dual and
   integral(f) = coefficient xx^4 yy^3 of (xx-yy) f. *)
hg=xx+yy; sg=xx yy;
grInt[f_]:=Coefficient[Coefficient[Expand[(xx-yy) f],xx,4],yy,3];
thetaG=2 hg^2/5-sg;
grVals={grInt[hg^6],grInt[sg hg^4],
        grInt[sg^2 hg^2],grInt[thetaG hg^4],
        grInt[thetaG^2 hg^2]};
out=<|
 "ChernRootRankCodimPairs"->Length[rootTests],
 "ChernRootAllPass"->And@@rootTests[[All,3]],
 "ChernRootFailures"->Select[rootTests,Not[#[[3]]]&],
 "LatticeDenominatorTests"->Length[latticeTests],
 "LatticeGapAllPass"->And@@latticeTests[[All,5]],
 "LatticeFailures"->Select[latticeTests,Not[#[[5]]]&],
 "GrassmannianSchubertPairings"->grVals,
 "AllExactSchubertChecks"->TrueQ[grVals==={5,2,1,0,1/5}],
 "AngleDefectExponents"->angleExponents
|>;
Print[out];out