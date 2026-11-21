(* GST Image 3 ORIGINAL CM all-N companion curvature certificate.
   Exact original Wave-I 12-cell U,J,M and zero-local-source
   companion transport C_h. The all-h theorem is proved algebraically:
       [I_h ⊗ J, I_h ⊗ (U+J)+C_h⊗M+f(C_h)⊗I]
           = C_h ⊗ [J,M], and rank = h*6.
   This file checks h=2,3 exactly in rational arithmetic and
   does not assert geometric original-X Hodge algebraicity.
*)
ClearAll[cells,ix,sh,mir,sgn,src,u,j,m,id12,curv,
  verify,rows,result];
cells=Flatten[Table[{a,b},{a,0,3},{b,0,2}],1];
ix[q_]:=First[FirstPosition[cells,q]];
sh[{a_,b_}]:={Quotient[a+4b,3],Mod[a+4b,3]};
mir[{a_,b_}]:={3-a,2-b};
sgn[{a_,b_}]:=If[MemberQ[{0,1,3,4,5,9},a+4b],1,-1];
src[{a_,b_}]:=Module[{mid=Mod[Quotient[a,2]+2b,3],out},
 out=Mod[Mod[a,2]+2mid,3];
 Boole[b==2]Boole[mid==2]+Boole[mid==2]Boole[out==2]];
u=Table[Boole[k==ix[sh[cells[[i]]]]],{i,12},{k,12}];
j=Table[sgn[cells[[i]]]*Boole[k==ix[mir[cells[[i]]]]],{i,12},{k,12}];
m=DiagonalMatrix[src/@cells];
id12=IdentityMatrix[12];
curv=j.m-m.j;
verify[lambda_List]:=Module[{h=Length[lambda],poly,coeff,
 c,b,fold,allCM,actual,target},
 poly=Expand[Times@@(x-#&/@lambda)];
 coeff=CoefficientList[poly,x];
 c=ConstantArray[0,{h,h}];
 Do[c[[i+1,i]]=1,{i,1,h-1}];
 Do[c[[i,h]]=-coeff[[i]],{i,1,h}];
 b=Sum[10(i-1)*Fold[Dot,IdentityMatrix[h],
  Table[(c-lambda[[jj]]IdentityMatrix[h])/
    (lambda[[i]]-lambda[[jj]]),
    {jj,Complement[Range[h],{i}]}]],{i,1,h}];
 fold=KroneckerProduct[IdentityMatrix[h],u+j]+
   KroneckerProduct[c,m]+KroneckerProduct[b,id12];
 allCM=KroneckerProduct[IdentityMatrix[h],j];
 actual=allCM.fold-fold.allCM;
 target=KroneckerProduct[c,curv];
 <|"h"->h,
  "localSurviveDiagonalZero"->(
    Diagonal[c]==ConstantArray[0,h]),
  "sourceCouplingInvertible"->(Det[c]!=0),
  "exactCMCommutatorIdentity"->(actual==target),
  "singleWorldCMRank"->MatrixRank[curv],
  "globalCMRank"->MatrixRank[actual],
  "globalCMRankRequired"->6 h,
  "allPassed"->(actual==target&&
    MatrixRank[curv]==6&&MatrixRank[actual]==6 h&&
    Det[c]!=0&&Diagonal[c]==ConstantArray[0,h])|>];
rows={verify[{1/2,-1/2}],verify[{1/2,1/3,-5/6}]};
result=<|"cases"->rows,
 "allPassed"->And@@(Lookup[#,"allPassed"]&/@rows)|>;
Print[result];result
