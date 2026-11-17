(* GST non-split singular original-X middle-source birth arithmetic.
   Geometric theorem: for every X^(2p), smooth codimension-p center Z,
   normal bundle N, ample h|_Z and sufficiently large m, a general
   hypersurface containing Z has n_pm = int_Z c_p(N^dual \[CircleTimes] L^m)
   ordinary double points, with exact exceptional Chow return.
   These are deterministic exact symbolic checks, not a proof of
   existence of an arbitrary prescribed rational Hodge algebraic center.
*)
ClearAll[deg,mi,hh,dd,aa,bb,cc,ee,qi,qj,qk,roots,
         signedRootCheck,hessianCheck,gram,prim,diagonal,
         rankChecks,exactResult,coeffs,normalRootPoly,normalSymPoly];
normalRootPoly[deg_Integer?Positive] :=
  Expand[Product[mi hh-roots[j],{j,1,deg}]];
normalSymPoly[deg_Integer?Positive] :=
  Expand[Sum[(-1)^j mi^(deg-j) hh^(deg-j)
           SymmetricPolynomial[j,Table[roots[i],{i,1,deg}]],
           {j,0,deg}]];
signedRootCheck=Table[
  {deg,normalRootPoly[deg]===normalSymPoly[deg]},
  {deg,2,7}];

(* For a transverse normal jet, Hessian has 0,A^T;A,Q.
   Verify uniform determinant sign in rational integer examples;
   algebraically determinant is (-1)^p det(A)^2 for any Q. *)
hessianCheck=Table[
 Module[{matA,matQ,hes,sign},
  matA=Table[If[i==j,i+1,Mod[i+2j,3]-1],{i,1,deg},{j,1,deg}];
  matQ=Table[i+j,{i,1,deg},{j,1,deg}];
  hes=ArrayFlatten[{{ConstantArray[0,{deg,deg}],Transpose[matA]},
                     {matA,matQ}}];
  {deg,Det[hes]===(-1)^deg Det[matA]^2,
   Det[matA],Det[hes]}],
 {deg,2,8}];

(* K3 x K3: basis A,B,U=h1h2, diagonal.
   d>0 is half polarizing self-intersection. *)
gram={{0,1,0,1},{1,0,0,1},{0,0,4dd^2,2dd},{1,1,2dd,24}};
prim={0,0,-1/dd,1};
diagonal={0,0,0,1};
rankChecks=Flatten[Table[{dd,mi,24+8dd mi^2>0,
                   (mi-1)^2>=0},{dd,1,12},{mi,1,20}],1];

(* Thom-Porteous source: for rank n bundle V, c_p(V(tH)) is the
   displayed binomial Chern formula. Check independent elementary-
   symmetric definition before using the primitive-pairing identity. *)
twistChernChecks=Flatten[Table[
 Module[{lhs,rhs,vars},
  vars=Table[roots[i],{i,1,rank}];
  lhs=Expand[SymmetricPolynomial[degree,vars+ConstantArray[ti hh,rank]]];
  rhs=Expand[Sum[Binomial[rank-j,degree-j](ti hh)^(degree-j)
                       SymmetricPolynomial[j,vars],{j,0,degree}]];
  {rank,degree,lhs===rhs}],
 {rank,2,8},{degree,2,Min[rank,5]}],1];
primitiveH2=FullSimplify[prim.gram.{2dd,2dd,2,0},dd>0];
primitiveTangentSource=FullSimplify[
 prim.gram.(24{1,1,0,0}+6ti^2{2dd,2dd,2,0}),dd>0];

exactResult=<|
 "allArityRootChecks"->signedRootCheck,
 "allArityRootPassed"->And@@signedRootCheck[[All,2]],
 "HessianBlockChecks"->hessianCheck,
 "HessianPassed"->And@@hessianCheck[[All,2]],
 "twistChernCases"->Length[twistChernChecks],
 "twistChernPass"->And@@twistChernChecks[[All,3]],
 "K3PrimitiveHyperplaneSquare"->primitiveH2,
 "K3PrimitiveTangentSource"->primitiveTangentSource,
 "K3PrimitiveSquare"->FullSimplify[prim.gram.prim,dd>0],
 "K3PrimitiveDiagonalPeriod"->FullSimplify[prim.gram.diagonal,dd>0],
 "K3DiagonalSquare"->diagonal.gram.diagonal,
 "K3NodalPolynomial"->24+8dd mi^2,
 "PlaneInP4NodalPolynomial"->Expand[(mi-1)^2],
 "CubicContainingPlaneNodes"->(3-1)^2,
 "K3d1m5Nodes"->24+8(1)(5)^2,
 "sampleCount"->Length[rankChecks],
 "samplePass"->And@@(#[[3]]&&#[[4]]&/@rankChecks)
|>;
Print[exactResult];exactResult