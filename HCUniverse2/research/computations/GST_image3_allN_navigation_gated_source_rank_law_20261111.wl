(* ORIGINAL GST Image 3 — exact all-N N-cohomology navigation rank law.
   True U/J/SURVIVE 12x12 operators. Each independently addressed
   original Wave-II hole has a binary NAVIGATION CHARGE q_i in {0,1}
   and a 10*channel_i address shift, making disjoint spectra.
   Exact theorem: rank of uniform seed Krylov orbit is
     sum_i (10+2 q_i) = 12 h - 2*(number of inactive holes).
   Full cyclicity iff ALL original navigation charges are active.
   Finite h=1 and h=2 checks exhaust ALL binary patterns;
   h=3 representative mixed pattern. All-h proof in derivation is
   by block cyclic subspace and pairwise coprime minimal polynomials.
*)
ClearAll[cc,ix,sh,mir,sign,src,u,j,m,seed,case,cases,result,
 nativeKrylov];
cc=Flatten[Table[{c,d},{c,0,3},{d,0,2}],1];
ix[a_]:=First[FirstPosition[cc,a]];
sh[{c_,d_}]:={Quotient[c+4d,3],Mod[c+4d,3]};
mir[{c_,d_}]:={3-c,2-d};
sign[{c_,d_}]:=If[MemberQ[{0,1,3,4,5,9},c+4d],1,-1];
src[{c_,d_}]:=Module[{a=Mod[Quotient[c,2]+2d,3],b},
 b=Mod[Mod[c,2]+2a,3];
 Boole[d==2]Boole[a==2]+Boole[a==2]Boole[b==2]];
u=Table[Boole[k==ix[sh[cc[[i]]]]],{i,12},{k,12}];
j=Table[sign[cc[[i]]]*Boole[k==ix[mir[cc[[i]]]]],{i,12},{k,12}];
m=DiagonalMatrix[src/@cc];
seed=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cc;
nativeKrylov[t_,v_,r_Integer?Positive]:=Transpose[NestList[t.#&,v,r-1]];
case[bits_List]:=Module[{h=Length[bits],t,v,kk,r,expect},
 t=ArrayFlatten[Table[
  If[i==k,u+j+bits[[i]] m+10 (i-1)IdentityMatrix[12],
    ConstantArray[0,{12,12}]],{i,h},{k,h}]];
 v=Flatten[ConstantArray[seed,h]];
 r=12 h;
 kk=nativeKrylov[t,v,r];
 expect=12h-2Count[bits,0];
 <|"navigation"->bits,"waveDimension"->r,
 "exactKrylovRank"->MatrixRank[kk],"predictedRank"->expect,
 "fullCyclic"->(MatrixRank[kk]==r),
 "allPassed"->(MatrixRank[kk]==expect)|>
];
cases=Join[Table[case[{a}],{a,0,1}],
 Table[case[{a,b}],{a,0,1},{b,0,1}]//Flatten,
 {case[{1,0,1}]}];
result=<|"baseOffRank"->MatrixRank[nativeKrylov[u+j,seed,12]],
 "baseOnRank"->MatrixRank[nativeKrylov[u+j+m,seed,12]],
 "NshapeCases"->cases,
 "allVerified"->And@@(Lookup[#,"allPassed"]&/@cases)|>;
Print[result];result