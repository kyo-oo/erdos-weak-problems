(* Mathbox GST fold proof-test. Exact actual geometries:
   E_i x E_i versus E_i x E_(Sqrt[2] i), and arbitrary
   external X x (P^1)^n for n>=0, p<=n+1.
   No numerical approximation; no claim of arbitrary-X HC proof. *)
indices=Subsets[Range[4],{2}];
hol1={1,tt,0,0};hol2={0,0,1,ss};
wedge=Table[Det[Join[IdentityMatrix[4][[ij]],{hol1,hol2}]],{ij,indices}];
atSame=ComplexExpand[wedge/.{tt->I,ss->I}];
atDifferent=ComplexExpand[wedge/.{tt->I,ss->I Sqrt[2]}];
matSame={{0,1,0,0,-1,0},{0,0,1,1,0,0}};
matDifferent={{0,1,0,0,0,0},{0,0,0,0,1,0},
              {0,0,1,0,0,0},{0,0,0,1,0,0}};
factorDiv1={0,0,0,0,0,1};
factorDiv2={1,0,0,0,0,0};
diagonalDiv={1,0,-1,1,0,1};
cmgraphDiv={1,1,0,0,1,1};
allActualDivisors={factorDiv1,factorDiv2,diagonalDiv,cmgraphDiv};
sameHodge=6-MatrixRank[matSame];
diffHodge=6-MatrixRank[matDifferent];
(* Independently enumerate the four cohomological Hodge bidegrees
   of each elliptic factor and the two of each projective factor. *)
ellipticBasisPolynomial=Total[Flatten[Table[u^a v^b,{a,0,1},{b,0,1}]]];
projectiveBasisPolynomial=Total[Table[(u v)^k,{k,0,1}]];
noBreakWhole=Table[
 TrueQ[Expand[ellipticBasisPolynomial^2 projectiveBasisPolynomial^n] ===
   Expand[(1+u)^2 (1+v)^2 (1+u v)^n]],{n,0,16}];
sameMarked=Simplify[atSame.diagonalDiv];
diffMarked=Simplify[atDifferent.diagonalDiv];
allNMarked=Flatten[Table[
 {n,p,
  TrueQ[sameMarked==0],
  TrueQ[diffMarked!=0],
  TrueQ[Length[Range[p-1]]<=n]},
 {n,0,16},{p,1,n+1}],1];
out=<|
 "wedgeCoefficientVector"->wedge,
 "equalCMRationalKernelRank"->sameHodge,
 "differentNonisogenousRationalKernelRank"->diffHodge,
 "actualAlignedDivisorsIndependent"->(MatrixRank[allActualDivisors]==4),
 "allActualAlignedDivisorsHodge"->And@@(matSame.#=={0,0}&/@allActualDivisors),
 "actualGenericDivisorsSpan"->(MatrixRank[{factorDiv1,factorDiv2}]==diffHodge),
 "sameMarkedWedge"->sameMarked,
 "differentMarkedWedge"->diffMarked,
 "allEmergentDimensionsSameHodgePolynomial"->And@@noBreakWhole,
 "allNMarkedTests"->Length[allNMarked],
 "allNMarkedBifurcationPass"->And@@Flatten[allNMarked[[All,3;;5]]],
 "allNMarkedFailures"->Select[allNMarked,Not[And@@#[[3;;5]]]&]
|>;
Print[out];out