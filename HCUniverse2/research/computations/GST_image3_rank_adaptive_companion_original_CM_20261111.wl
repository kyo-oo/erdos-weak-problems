(* GST Image 3 — rank-adaptive ORIGINAL U/J/M native all-N source.
   For each desired rank r=1,2:
   h=2r source worlds with lambda paired +/- (a+1/a)/2,
   a=i+2, zero source trace and hence zero C diagonal,
   address step L=20(r+5), B=f(C) rational Lagrange.
   Exact original twelve-cell fixed-pair quadratic factor is
      q_lambda(x)=x^2-(2+2lambda)x+(2+2lambda)
   and splits into rational linear factors for all chosen lambda.
   Verify no local M, full 12h Krylov det mod1009, all companion
   eigenmode address claims and existence of r rational linear
   factors. No original-X algebraic Hodge classes are claimed.
*)
ClearAll[cells,ix,sh,mir,sgn,src,u,j,m,v,id12,case,rows,result];
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
v=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cells;
id12=IdentityMatrix[12];

case[r_Integer?Positive]:=Module[{h=2r,aa,lam,L,poly,co,c,b,
 T,root,K,det,cp,quad,mu,sel,rEval,pi},
 aa=Range[3,r+2];
 lam=Flatten[({(# + 1/#)/2,-(# + 1/#)/2}&/@aa)];
 L=20(r+5);poly=Expand[Times@@(x-#&/@lam)];
 co=CoefficientList[poly,x];
 c=ConstantArray[0,{h,h}];
 Do[c[[i+1,i]]=1,{i,1,h-1}];
 Do[c[[i,h]]=-co[[i]],{i,1,h}];
 b=Sum[L(i-1)*Fold[Dot,IdentityMatrix[h],
   Table[(c-lam[[kk]]IdentityMatrix[h])/(lam[[i]]-lam[[kk]]),
    {kk,Complement[Range[h],{i}]}]],{i,1,h}];
 T=KroneckerProduct[IdentityMatrix[h],u+j]+
    KroneckerProduct[c,m]+KroneckerProduct[b,id12];
 root=Join[v,ConstantArray[0,12(h-1)]];
 K=Transpose[NestList[Mod[T.#,1009]&,root,12h-1]];
 det=Det[K,Modulus->1009];
 cp=Table[CharacteristicPolynomial[u+j+lam[[i]]m,x],
    {i,1,h}];
 quad=Table[x^2-(2+2lam[[i]])x+(2+2lam[[i]]),
    {i,1,h}];
 mu=Table[L(2i-2)+1+aa[[i]],{i,1,r}];
 rEval=Table[mu[[i]]^(k-1),{i,1,r},{k,1,r}];
 <|"r"->r,"h"->h,"sourceStrengths"->lam,
 "strengthSumZero"->(Total[lam]==0),
 "strengthsDistinct"->DuplicateFreeQ[lam],
 "allLocalMcoefficientsZero"->(Diagonal[c]==ConstantArray[0,h]),
 "companionCharacteristicExact"->(
   Expand[(-1)^h CharacteristicPolynomial[c,x]-poly]===0),
 "waveIIAddressCharacteristicExact"->(
   Expand[(-1)^h CharacteristicPolynomial[b,x]-
      Product[x-L(i-1),{i,1,h}]]===0),
 "rationalFixedSpectralFactorExact"->And@@Table[
   PolynomialRemainder[cp[[i]],quad[[i]],x]===0,{i,1,h}],
 "quadraticSplitsIntoTwoRationalLinearFactors"->And@@Table[
   Length[Select[FactorList[quad[[i]]],
     Exponent[First[#],x]==1&]]==2,{i,1,h}],
 "nativeFullRankDetMod1009"->det,
 "rootFullNativeCyclic"->(det!=0),
 "chosenRationalQuotientEigenvalues"->mu,
 "chosenQuotientVandermondeDet"->Det[rEval],
 "rankAdaptiveQuotientCyclic"->(Det[rEval]!=0),
 "allPassed"->(Total[lam]==0&&DuplicateFreeQ[lam]&&
   Diagonal[c]==ConstantArray[0,h]&&det!=0&&
   Expand[(-1)^h CharacteristicPolynomial[c,x]-poly]===0&&
   And@@Table[PolynomialRemainder[cp[[i]],quad[[i]],x]===0,
     {i,1,h}]&&Det[rEval]!=0)|>];
rows={case[1],case[2]};
result=<|"tests"->rows,
 "allPassed"->And@@(Lookup[#,"allPassed"]&/@rows)|>;
Print[result];result
