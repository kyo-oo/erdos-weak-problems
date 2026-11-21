(* GST IMAGE 3 — arbitrary-N zero-local-SURVIVE companion source compiler.
   The full proof is algebraic (see accompanying derivation).
   These exact tests are its small h=2,3 implementation audit.

   ORIGINAL owner's GST matrices:
       U (fivefold x4/base3 shuffle),
       J (rational CM signed complement, J^2=-I), and
       M (ORIGINAL SURVIVE source, not an invented diagonal).
   Seed v=e_(0,0)+e_(0,1).

   Choose distinct nonzero rational eigenvalues lambda_i summing 0.
   C=companion(Product(t-lambda_i)) => diagonal(C)=0 exactly.
   Choose rational polynomial f(C) by Lagrange interpolation with
   f(lambda_i)=10(i-1) (Wave II spectral address).
   Define full F=I_h ⊗ (U+J)+C ⊗ M + f(C)⊗I_12.
   Initial source is ONLY first world e_1⊗v.
   Check all actual original finite GST indices exactly, rationally.

   The general h>=2 theorem follows from zero-trace companion
   cyclicity, old proven all-rational single-cell Krylov determinant,
   eigenvalue separation and polynomial CRT, not extrapolating tests.
*)
ClearAll[cells,idx,sh,mir,sgn,src,u,j,m,v,id12,
  run,rows,result];
cells=Flatten[Table[{a,b},{a,0,3},{b,0,2}],1];
idx[q_]:=First[FirstPosition[cells,q]];
sh[{a_,b_}]:={Quotient[a+4b,3],Mod[a+4b,3]};
mir[{a_,b_}]:={3-a,2-b};
sgn[{a_,b_}]:=If[MemberQ[{0,1,3,4,5,9},a+4b],1,-1];
src[{a_,b_}]:=Module[{mid=Mod[Quotient[a,2]+2b,3],out},
 out=Mod[Mod[a,2]+2mid,3];
 Boole[b==2]Boole[mid==2]+Boole[mid==2]Boole[out==2]];
u=Table[Boole[k==idx[sh[cells[[i]]]]],{i,12},{k,12}];
j=Table[sgn[cells[[i]]]*Boole[k==idx[mir[cells[[i]]]]],{i,12},{k,12}];
m=DiagonalMatrix[src/@cells];
v=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cells;
id12=IdentityMatrix[12];

run[lambda_List]:=Module[{h=Length[lambda],p,co,C,B,T,root,n,K,r,ell,moms},
 p=Expand[Times@@(x-#&/@lambda)];co=CoefficientList[p,x];
 C=ConstantArray[0,{h,h}];
 Do[C[[i+1,i]]=1,{i,1,h-1}];
 Do[C[[i,h]]=-co[[i]],{i,1,h}];
 B=Sum[10(i-1)*Fold[Dot,IdentityMatrix[h],
  Table[(C-lambda[[jj]]IdentityMatrix[h])/
    (lambda[[i]]-lambda[[jj]]),
    {jj,Complement[Range[h],{i}]}]],{i,1,h}];
 T=KroneckerProduct[IdentityMatrix[h],u+j]+
   KroneckerProduct[C,m]+KroneckerProduct[B,id12];
 root=Join[v,ConstantArray[0,12(h-1)]];
 n=12h;
 K=Transpose[NestList[T.#&,root,n-1]];
 r=MatrixRank[K];
 ell=LinearSolve[Transpose[K],UnitVector[n,n]];
 moms=Table[ell.MatrixPower[T,k].root,{k,0,n-1}];
 <|"h"->h,"lambda"->lambda,
  "allStrengthsNonzero"->FreeQ[lambda,0],
  "noForbiddenMinusOne"->FreeQ[lambda,-1],
  "strengthSumZero"->(Total[lambda]==0),
  "noLocalSurviveSource"->(Diagonal[C]==ConstantArray[0,h]),
  "trueCompanionCharacteristic"->(
    Expand[(-1)^h CharacteristicPolynomial[C,x]-p]===0),
  "trueWaveIIAddressCharacteristic"->(
    Expand[(-1)^h CharacteristicPolynomial[B,x]-
      Product[x-10(i-1),{i,1,h}]]===0),
  "addressCommutesWithSource"->(C.B==B.C),
  "rootReachesAllHoles"->(
    MatrixRank[Transpose[NestList[C.#&,UnitVector[h,1],h-1]]]==h),
  "originalSourceMatrixMaxAbs"->Max[Abs[lambda]],
  "cyclicOrbitRank"->r,"requiredRank"->n,
  "dualOrbitMomentFirstN"->moms,
  "dualHankelAntidiagonal"->(
    moms==Join[ConstantArray[0,n-1],{1}]),
  "allPassed"->(Total[lambda]==0&&
    FreeQ[lambda,0]&&FreeQ[lambda,-1]&&
    Diagonal[C]==ConstantArray[0,h]&&
    Expand[(-1)^h CharacteristicPolynomial[C,x]-p]===0&&
    C.B==B.C&&r==n&&
    moms==Join[ConstantArray[0,n-1],{1}])|>];
rows={run[{1/2,-1/2}],run[{1/2,1/3,-5/6}]};
result=<|"cases"->rows,"allPassed"->And@@(Lookup[#,"allPassed"]&/@rows)|>;
Print[result];result
