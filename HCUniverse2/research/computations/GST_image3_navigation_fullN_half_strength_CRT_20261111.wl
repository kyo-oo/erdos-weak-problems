(* GST Image-3 ORIGINAL all-N Wave II CRT finite certificate.
   Uses the OWNER's true twelve-state U,J,Survive M and original
   mixed seed in 2 independently addressed holes (0,10).
   Checks exact 24x24 determinant = baseDet^2 Resultant(chi(x),chi(x-10))
   at rational strengths 1/2 and 1.
   The all-positive-N statement is a separate general CRT proof in
   research/derivations/GST_image3_native_navigation_CM_Ncohomology_pureHodge_F_2026_11_11.md
*)
ClearAll[cc,ix,sh,mir,sgn,src,u,j,m,v,kry,run,runs,result];
cc=Flatten[Table[{c,d},{c,0,3},{d,0,2}],1];
ix[a_]:=First[FirstPosition[cc,a]];
sh[{c_,d_}]:={Quotient[c+4d,3],Mod[c+4d,3]};
mir[{c_,d_}]:={3-c,2-d};
sgn[{c_,d_}]:=If[MemberQ[{0,1,3,4,5,9},c+4d],1,-1];
src[{c_,d_}]:=Module[{mid=Mod[Quotient[c,2]+2d,3],fin},
 fin=Mod[Mod[c,2]+2mid,3];
 Boole[d==2]Boole[mid==2]+Boole[mid==2]Boole[fin==2]];
u=Table[Boole[k==ix[sh[cc[[i]]]]],{i,12},{k,12}];
j=Table[sgn[cc[[i]]]*Boole[k==ix[mir[cc[[i]]]]],{i,12},{k,12}];
m=DiagonalMatrix[src/@cc];
v=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cc;
kry[t_,vv_,r_Integer?Positive]:=Transpose[NestList[t.#&,vv,r-1]];
run[lambda_]:=Module[{t=u+j+lambda m,two,v2,k12,k24,chi,res},
 two=KroneckerProduct[IdentityMatrix[2],t]+
 KroneckerProduct[DiagonalMatrix[{0,10}],IdentityMatrix[12]];
 v2=Join[v,v];
 k12=kry[t,v,12];k24=kry[two,v2,24];
 chi=CharacteristicPolynomial[t,x];
 res=Resultant[chi,chi/.x->x-10,x];
 <|"strength"->lambda,"baseRank"->MatrixRank[k12],
 "twoHoleRank"->MatrixRank[k24],
 "twoHoleDetNonzero"->(Det[k24]!=0),
 "exactResultantIdentity"->(Det[k24]==Det[k12]^2 res),
 "exactRowSumBound"->Max[Total[Abs[t],{2}]],
 "allPassed"->(MatrixRank[k12]==12&&MatrixRank[k24]==24&&
  Det[k24]!=0&&Det[k24]==Det[k12]^2 res &&
  Max[Total[Abs[t],{2}]]<=4)|>];
runs={run[1/2],run[1]};
result=<|"cases"->runs,"allPassed"->And@@(Lookup[#,"allPassed"]&/@runs)|>;
Print[result];result