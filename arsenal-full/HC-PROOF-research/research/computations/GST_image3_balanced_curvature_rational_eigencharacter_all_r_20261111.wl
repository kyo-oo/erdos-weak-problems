(* ORIGINAL GST Image 3 rank-adaptive balanced native F — exact rational
   source character proof and N-hole Vandermonde evidence.

   U: original carry/trit radix shuffle (U^5=I)
   J: original signed CM mirror (J^2=-I)
   M: original Wave-I SURVIVE current
   C=J.M-M.J (the true native CM source curvature)
   B=U+J+M+C (balanced native F, no invented signal basis)

   The original U-fixed null/max information cells form
     {{1,3},{1,3}},
   producing two rational eigencharacters 0 and 4, detected by
     ell0(u)=u(null)-u(max), ell4(u)=u(null)+3u(max).
   BOTH detectors see the original mixed seed with value 1.
   The r-channel eigenvalue quotient uses shifts 20i and original
   N-hole channels, i=0,...,r-1, and its Krylov determinant is a
   Vandermonde. This constructs a rank-r SYMBOLIC GST quotient
   for every finite positive r, not a universal geometric Hodge map.
*)
ClearAll[cells,idx,sh,mir,sgn,surv,U,J,M,C,seed,B,ell0,ell4,
  fixed,chars,kry,shifted,ret,r,quad,detFormula,result];
cells=Flatten[Table[{i,k},{i,0,3},{k,0,2}],1];
idx[z_]:=First[FirstPosition[cells,z]];
sh[{i_,k_}]:={Quotient[i+4k,3],Mod[i+4k,3]};
mir[{i_,k_}]:={3-i,2-k};
sgn[{i_,k_}]:=If[MemberQ[{0,1,3,4,5,9},i+4k],1,-1];
surv[{i_,k_}]:=Module[{p=Mod[Quotient[i,2]+2k,3],q},
 q=Mod[Mod[i,2]+2p,3];
 Boole[k==2]Boole[p==2]+Boole[p==2]Boole[q==2]];
U=Table[Boole[z==idx[sh[cells[[i]]]]],{i,12},{z,12}];
J=Table[sgn[cells[[i]]]*Boole[z==idx[mir[cells[[i]]]]],{i,12},{z,12}];
M=DiagonalMatrix[surv/@cells];
C=J.M-M.J;
seed=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cells;
B=U+J+M+C;
ell0=UnitVector[12,idx[{0,0}]]-UnitVector[12,idx[{3,2}]];
ell4=UnitVector[12,idx[{0,0}]]+3UnitVector[12,idx[{3,2}]];
fixed=B[[{idx[{0,0}],idx[{3,2}]},{idx[{0,0}],idx[{3,2}]}]];
kry[t_,vv_,n_]:=Transpose[NestList[t.#&,vv,n-1]];
ret={};
Do[
 shifted=20 Range[0,r-1];
 quad=Table[If[k==0,1,shifted[[i]]^k],{k,0,r-1},{i,1,r}];
 detFormula=Times@@Flatten[Table[shifted[[j]]-shifted[[i]],{i,1,r-1},{j,i+1,r}]];
 AppendTo[ret,<|"rank"->r,"quotientKrylovRank"->MatrixRank[quad],
 "quotientDet"->Det[quad],"exactVandermondeProduct"->detFormula,
 "passed"->(MatrixRank[quad]==r&&Det[quad]==detFormula)|>],
 {r,1,6}];
result=<|"originalJ2"->(J.J==-IdentityMatrix[12]),
 "originalU5"->(MatrixPower[U,5]==IdentityMatrix[12]),
 "balancedFixedPair"->fixed,
 "rationalEigenvalues"->Eigenvalues[fixed],
 "zeroCharacter"->(ell0.B==ConstantArray[0,12]),
 "fourCharacter"->(ell4.B==4ell4),
 "zeroCharacterOnOriginalSeed"->ell0.seed,
 "fourCharacterOnOriginalSeed"->ell4.seed,
 "full12NativeRank"->MatrixRank[kry[B,seed,12]],
 "full12NativeDet"->Det[kry[B,seed,12]],
 "maxAbsoluteRowSum"->Max[Total[Abs[B],{2}]],
 "quotientRanks1through6"->ret|>;
result=Append[result,"allPassed"->(
 result["originalJ2"]&&result["originalU5"]&&
 result["balancedFixedPair"]=={{1,3},{1,3}}&&
 result["zeroCharacter"]&&result["fourCharacter"]&&
 result["zeroCharacterOnOriginalSeed"]==1&&
 result["fourCharacterOnOriginalSeed"]==1&&
 result["full12NativeRank"]==12&&
 result["full12NativeDet"]==-445265540949&&
 And@@(Lookup[#,"passed"]&/@ret))];
Print[result];result