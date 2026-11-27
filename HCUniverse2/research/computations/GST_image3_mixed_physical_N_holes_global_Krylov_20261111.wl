(* Original GST physical-navigation MIXED N-hole Krylov source experiment.
   Physical Navigation gates g_i ∈{0,1}; original direct SURVIVE a_i ∈Q.
   Source F_(a,g)=U+J+aM+g[J,M], original mixed seed v.
   Sample sets exercise active+inactive and heterogeneous direct strengths.
   They verify full 12h rank for h=2, with a single globally shifted fold.
   Universal proof uses exact single-hole cyclicity + spectral norm + CRT;
   it is documented separately. NO canonical Hodge cycle lift is claimed. *)

ClearAll[GSTMixedKrylov,GSTMixedFold,GSTMixedRun];
GSTMixedKrylov[T_,v_,n_]:=Transpose[NestList[T.#&,v,n-1]];

Module[{cells,idx,sh,mir,sgn,surv,U,J,M,C,seed,check,tests,rows},
 cells=Flatten[Table[{i,k},{i,0,3},{k,0,2}],1];
 idx[z_]:=First[FirstPosition[cells,z]];
 sh[{i_,k_}]:={Quotient[i+4*k,3],Mod[i+4*k,3]};
 mir[{i_,k_}]:={3-i,2-k};
 sgn[{i_,k_}]:=If[MemberQ[{0,1,3,4,5,9},i+4*k],1,-1];
 surv[{i_,k_}]:=Module[{p=Mod[Quotient[i,2]+2*k,3],q},
   q=Mod[Mod[i,2]+2*p,3];
   Boole[k==2]Boole[p==2]+Boole[p==2]Boole[q==2]];
 U=Table[Boole[z==idx[sh[cells[[i]]]]],{i,12},{z,12}];
 J=Table[sgn[cells[[i]]]*Boole[z==idx[mir[cells[[i]]]]],{i,12},{z,12}];
 M=DiagonalMatrix[surv/@cells]; C=J.M-M.J;
 seed=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cells;
 GSTMixedFold[a_,g_]:=U+J+a*M+g*C;
 check[st_]:=Module[{h=Length[st],l,s,t,v,r,norms},
   l=Max[0,Sequence@@Abs[st[[All,1]]]];
   s=9+4*l;
   t=ArrayFlatten[Table[
     If[i==j,GSTMixedFold@@st[[i]]+
       (i-1)*s*IdentityMatrix[12],
       ConstantArray[0,{12,12}]],
     {i,h},{j,h}]];
   v=Flatten[ConstantArray[seed,h]];
   r=MatrixRank[GSTMixedKrylov[t,v,12*h]];
   norms=Max[Total[Abs[#],{2}]]& /@
      (GSTMixedFold@@#& /@ st);
   <|"states"->st,"holeCount"->h,
     "spacing"->s,"originalBlockNorms"->norms,
     "uniformNormUpperBound"->4+2*l,
     "allPhysicalGates"->AllTrue[st,MemberQ[{0,1},Last[#]]&],
     "allSingleHoleCyclic"->AllTrue[st,
       (Last[#]==1 || !MemberQ[{0,-1},First[#]])&],
     "singleGlobalKrylovRank"->r,
     "rankExpected"->12*h,
     "passed"->TrueQ[r==12*h] &&
       AllTrue[norms,#<=4+2*l&] &&
       TrueQ[s>2*(4+2*l)]|>];
 tests={{{1,0},{1,1}},{{2,0},{-3,1}},{{0,1},{-1,1}}};
 rows=check/@tests;
 <|"examples"->rows,"allPassed"->And@@Lookup[rows,"passed"]|>
]
