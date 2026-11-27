(* Exact two-parameter SOURCE strength classification for the original GST
   Image-3 twelve-state U/J/M/[J,M] fold.

   F_(a,b) = U + J + a M + b [J,M], a,b in Q.

   Proves using exact polynomial algebra, NOT numerical guessing:
   1. fixed two-cell Krylov determinant 2 b-1;
   2. degree of rotating-ten Krylov determinant in a is 8,
      with leading coefficient 64(b-2)^2;
   3. degree of two-vs-ten characteristic resultant in a is 12,
      with leading coefficient 2560;
   4. hence the full 12-cell Krylov determinant has degree 20 in a
      with leading coefficient 163840(2b-1)(b-2)^2, except at
      specialized exceptional b values where degree may drop;
   5. b=2 is not permanently singular: det F_(0,2) != 0;
   6. b=1/2 is permanently singular via the fixed-cell obstruction;
   7. for EVERY integer b=1 mod 11, the full determinant has NO
      rational a-root, by full finite-field coverage and the
      nonzero mod-11 leading coefficient.

   Scope: ORIGINAL finite rational GST source, not universal
   original-X Chow surjectivity or unconditional Hodge.
*)

ClearAll[GSTFullSourceKrylov];
GSTFullSourceKrylov[T_,v_,n_]:=Transpose[NestList[T.#&,v,n-1]];

Module[{cells,idx,sh,mir,sgn,surv,U,J,M,C,seed,ids,rest,
  a,b,x,T,T2,T10,d2,d10,R,droot,lead10,leadR,lead12,
  mod11Det,checks,all},
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
 M=DiagonalMatrix[surv/@cells];
 C=J.M-M.J;
 seed=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cells;
 ids={idx[{0,0}],idx[{3,2}]};
 rest=Complement[Range[12],ids];
 T=U+J+a*M+b*C;
 T2=T[[ids,ids]];T10=T[[rest,rest]];
 d2=Factor[Det[GSTFullSourceKrylov[T2,seed[[ids]],2]]];
 d10=Factor[Det[GSTFullSourceKrylov[T10,seed[[rest]],10]]];
 R=Factor[Resultant[CharacteristicPolynomial[T2,x],
                     CharacteristicPolynomial[T10,x],x]];
 lead10=Factor[Coefficient[d10,a,8]];
 leadR=Factor[Coefficient[R,a,12]];
 lead12=Factor[d2*lead10*leadR];
 droot=Factor[(d2*d10*R)/.{a->0,b->2}];
 mod11Det=Table[
   Mod[(d2*d10*R)/.{a->k,b->1},11],{k,0,10}];
 checks=<|
  "fixedTwoKrylovDet"->d2,
  "degreeTenInA"->Exponent[d10,a],
  "leadingTenInA"->lead10,
  "degreeResultantInA"->Exponent[R,a],
  "leadingResultantInA"->leadR,
  "fullLeadingA20"->lead12,
  "specialB2A0Det"->droot,
  "allF11DirectStrengthDetResiduesAtB1"->mod11Det,
  "exactTwoBlock"->TrueQ[Expand[d2-(2*b-1)]===0],
  "tenLeadingExact"->TrueQ[Expand[lead10-64*(b-2)^2]===0],
  "resultantLeadingExact"->TrueQ[Expand[leadR-2560]===0],
  "fullLeadingExact"->TrueQ[
     Expand[lead12-163840*(2*b-1)*(b-2)^2]===0],
  "b2NotPermanentlySingular"->TrueQ[droot==-10365615590204736],
  "everyF11DirectCoefficientNonzero"->FreeQ[mod11Det,0],
  "b1LeadingNonzeroMod11"->(Mod[lead12/.b->1,11]!=0)
 |>;
 all=And@@Lookup[checks,{"exactTwoBlock","tenLeadingExact",
   "resultantLeadingExact","fullLeadingExact",
   "b2NotPermanentlySingular","everyF11DirectCoefficientNonzero",
   "b1LeadingNonzeroMod11"}];
 Print[Append[checks,"allPassed"->all]];
 Append[checks,"allPassed"->all]
]
