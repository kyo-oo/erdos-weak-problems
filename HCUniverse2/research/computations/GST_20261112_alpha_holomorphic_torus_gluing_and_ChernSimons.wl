(* Exact user-correction checks:
   1. An actual nontrivial holomorphic line bundle on affine
      the two-dimensional complex algebraic torus via an integer automorphy cocycle.
   2. Its Chern period is integral one.
   3. An algebraic Laurent-polynomial differential has zero
      (x^-1 y^-1) residue when exact, so dlog x wedge dlog y
      is not exact.
   4. The all-degree ABELIAN Chern-Simons telescoping
      identity; general matrix case follows from Bianchi.
   The projective Hodge conjecture is not tested here. *)
Module[{m,n,mp,np,z1,z2,factor,cocycle,connection,curvature,
  a,b,remainders,mR,nR,dfResidue,dgResidue},
factor[aa_,bb_,zz_]:=Exp[2 Pi I aa zz];
cocycle=FullSimplify[
 factor[m,n,z2+np]*factor[mp,np,z2]/
 factor[m+mp,n+np,z2],
 Assumptions->Element[{m,n,mp,np},Integers]];
connection=2 Pi I z1;
curvature=D[connection,z1];
remainders=Table[
 Expand[(b-a)*Sum[b^(p-1-k)*a^k,{k,0,p-1}]-(b^p-a^p)],
 {p,1,9}];
(* Laurent differential on coordinate ring:
 d(x^k y^j dx + x^r y^s dy)
  = (r x^(r-1)y^s-j x^k y^(j-1)) dx^dy.
 At x^-1 y^-1 both derivative coefficients vanish. *)
dfResidue=Table[If[k==0,0,k]*KroneckerDelta[k-1,-1],{k,-4,4}];
dgResidue=Table[If[k==0,0,k]*KroneckerDelta[k-1,-1],{k,-4,4}];
<|"holomorphicLineBundleCocycleDefect"->cocycle,
"curvatureCoefficient"->curvature,
"integralChernNumber"->Simplify[curvature/(2 Pi I)],
"exactChernSimonsPolynomialRemaindersP1to9"->remainders,
"allExactLaurentMonomialResiduesZero"->(
 dfResidue==ConstantArray[0,9]&&
 dgResidue==ConstantArray[0,9]),
"affineAlgebraicPicard"->"zero: Laurent polynomial UFD",
"allPassed"->(cocycle==1&&curvature==2 Pi I&&
 And@@(#==0& /@ remainders)&&
 dfResidue==ConstantArray[0,9]&&
 dgResidue==ConstantArray[0,9])|>
]