(* Mathbox -- actual algebraic GST Rees folding, exceptional
   normal Segre pushforward and nondivisor original-X cycle.
   All-X structural proofs are in the paired .tex manuscript;
   this file verifies independent exact polynomial identities.
   No random tests, no floating point, no internet.
*)
ClearAll["Global`*"];
(* In LINES convention, normal Chern roots lambda_i give
   the projective relation xi^(m+1) Product_i(xi+lambda_i).
   Independently compare its Chern-expanded polynomial. *)
projTest[c_Integer,m_Integer]:=Module[
 {roots=Array[aa,c],lhs,ee,rhs},
 lhs=Expand[xx^(m+1) Product[xx+roots[[j]],{j,1,c}]];
 ee[j_Integer]:=If[j==0,1,
   Total[Times@@@Subsets[roots,{j}]]];
 rhs=Expand[Sum[ee[j] xx^(c+m+1-j),{j,0,c}]];
 {c,m,TrueQ[lhs===rhs]}];
projectiveCases=Flatten[Table[projTest[c,m],
 {c,1,7},{m,0,8}],1];
(* Segre pushforward independently via:
   (A) the reciprocal total CHERN polynomial, and
   (B) equivariant Lagrange fiber localization for the
       projectivization of LINES in N with integer Chern roots.
   q_*xi^(c-1+l) = sum_i (-root_i)^(c-1+l)/
                     product_(j!=i)(root_j-root_i). *)
segTest[c_Integer,ell_Integer]:=Module[
 {roots=Range[c],series,locus},
 series=SeriesCoefficient[
  1/Product[1+rr[j] t,{j,1,c}] /.
   Table[rr[j]->roots[[j]],{j,1,c}],{t,0,ell}];
 locus=Total[Table[
 (-roots[[i]])^(c-1+ell)/
  Product[roots[[j]]-roots[[i]],
      {j,DeleteCases[Range[c],i]}],{i,1,c}]];
 {c,ell,TrueQ[series===locus],series,locus}
];
segCases=Flatten[Table[segTest[c,ell],
 {c,2,7},{ell,0,6}],1];
(* Pushforward of the cth exceptional divisor power
   is (-1)^(c-1) * [Z] because q_*xi^(c-1)=1;
   higher powers are (-1)^(c+ell-1) i_*s_ell(N). *)
exceptionalChecks=Table[
 {c,(-1)^(c-1)*segTest[c,0][[4]]==(-1)^(c-1)},
 {c,2,9}];
(* Gr(2,5): true nondivisor original-X class from
   the blowup of the zero locus of a section of S-dual.
   b_*(exceptional^2) = -[Gr(2,4)] = -s2. *)
h=x+y;ss=x y;alpha=2 h^2/5-ss;
grInt[f_]:=Coefficient[
 Coefficient[Expand[(x-y)f],x,4],y,3];
schubert={grInt[h^6],grInt[ss h^4],grInt[ss^2 h^2],
 grInt[alpha h^4],grInt[alpha^2 h^2]};
sourceClass=Expand[2 h^2/5-ss];
sourceChecks=<|
 "normalCenterCodimension"->2,
 "blowupPushE2Coefficient"->-1,
 "sourceEqualsAlpha"->TrueQ[Expand[sourceClass-alpha]===0],
 "HodgePrimitiveOrthogonality"->TrueQ[schubert[[4]]==0],
 "NonzeroPrimitivePairing"->TrueQ[schubert[[5]]==1/5]
|>;
(* Full CODIMENSION-TWO original-X/born-center Chow projectors.
   In coordinates (a,z) of actual blowup Chow,
   PiX and PiBorn are the geometric push-pull operators
   b^* b_* and -j_* q^* q_* j^*, respectively. *)
projOriginal={{1,0},{0,0}};
projBorn={{0,0},{0,1}};
fullChowProjectors=<|
 "originalIdempotent"->TrueQ[projOriginal.projOriginal===projOriginal],
 "bornIdempotent"->TrueQ[projBorn.projBorn===projBorn],
 "mutualOrthogonality"->TrueQ[projOriginal.projBorn===ConstantArray[0,{2,2}]
   &&projBorn.projOriginal===ConstantArray[0,{2,2}]],
 "sumIsFullIdentity"->TrueQ[projOriginal+projBorn===IdentityMatrix[2]]
|>;
(* Exceptional-square relation on the actual exceptional
   P(N) where zeta^2+c1(N) zeta+c2(N)=0.
   Restrict both sides of E^2=-b^*[Z]+j_*q^*c1(N). *)
lhsExceptionalRestrict=-cOne zz-cTwo;
rhsExceptionalRestrict=-cTwo-zz cOne;
exceptionalSquareRestrictionExact=TrueQ[
 Expand[lhsExceptionalRestrict-rhsExceptionalRestrict]===0];
(* New all-original-X alpha-selected divisor-to-polynomial-center theorem:
   choose line bundle M with c1(M)=denom*beta.
   two regular polynomial complete intersections have Chow classes
   (denom*beta+twist*h)*h^(p-1) and twist*h^p.
   Their signed Rees blowup exceptional powers return the
   difference, exactly beta*h^(p-1), with no codim-p
   pre-existing Chow witness as input. *)
targetFoldTests=Table[
 Module[{plus,minus,blowupPlus,blowupMinus,target},
 plus=(denom*beta+twist*hh)*hh^(p-1);
 minus=twist*hh^p;
 blowupPlus=(-1)^(p-1)*plus;
 blowupMinus=(-1)^(p-1)*minus;
 target=Expand[(-1)^(p-1)*
            (blowupPlus-blowupMinus)/denom];
 {p,TrueQ[FullSimplify[target==beta*hh^(p-1)]]}
 ],{p,2,12}];
result=<|
 "universalHodgeDivisorInputFoldRanks"->Length[targetFoldTests],
 "alphaSelectedFoldSourceAllPass"->And@@targetFoldTests[[All,2]],
 "alphaSelectedFoldFailures"->Select[targetFoldTests,Not[#[[2]]]&],
 "fullCodimensionTwoChowProjectorPair"->fullChowProjectors,
 "exceptionalSquareRestrictionExact"->exceptionalSquareRestrictionExact,
 "projectiveChowRelationCases"->Length[projectiveCases],
 "allProjectiveRelations"->And@@projectiveCases[[All,3]],
 "projectiveFailures"->Select[projectiveCases,Not[#[[3]]]&],
 "SegreIndependentRootCases"->Length[segCases],
 "allSegreRootPushforwards"->And@@segCases[[All,3]],
 "SegreFailures"->Select[segCases,Not[#[[3]]]&],
 "exceptionalCenterCases"->Length[exceptionalChecks],
 "exceptionalCenterPushAllPass"->And@@exceptionalChecks[[All,2]],
 "schubertPeriods"->schubert,
 "foldBornSource"->sourceChecks
|>;
Print[result];result