(* Exact strength-uniform CM half-curvature resonance corank-one certificate.

   F_(a,1/2)=U+J+a M+(1/2)[J,M] on the author's ORIGINAL
   12-cell rational GST wave with original mixed seed.

   The maximum-information coordinate vanishes on the entire orbit,
   so the cyclic rank is <=11. The restriction to its 11-cell kernel
   is block diagonal: a 1-dimensional source eigenvalue 1 plus
   the 10-cell rotating original world.

   The 11x11 Krylov determinant FACTORS EXACTLY:
     (P8(a) Q2(a))/512,
   where P8 is a degree-8 polynomial of INTEGER coefficients and
   Q2(a)=69-72a+20a^2 is strictly positive for all real a because
     5 Q2 = (10a-18)^2 + 21.
   P8 has no root modulo 13 and a leading coefficient nonzero
   modulo 13, so has no rational root by the rational-root theorem.

   Hence for EVERY rational a, actual source cyclic rank is EXACTLY 11,
   not just at most 11 and not a numerical-only assertion.

   This is a native source theorem, not canonical Chow/Hodge algebraicity.
*)

ClearAll[GSTHalfCurvatureKrylov,GSTHalfCurvatureP8,GSTHalfCurvatureQ2];
GSTHalfCurvatureKrylov[T_,v_,n_]:=Transpose[NestList[T.#&,v,n-1]];
GSTHalfCurvatureP8[a_]:=11583665+66174720*a-44920944*a^2-
  19478232*a^3-1670652*a^4-2895936*a^5+
  666144*a^6-82944*a^7+36864*a^8;
GSTHalfCurvatureQ2[a_]:=69-72*a+20*a^2;

Module[{cells,idx,sh,mir,sgn,surv,U,J,M,C,seed,ids,rest,keep,
  a,F,T10,T11,d10,e1,d11,rP8,rQ2,cert},
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
 M=DiagonalMatrix[surv/@cells];C=J.M-M.J;
 seed=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cells;
 ids={idx[{0,0}],idx[{3,2}]};
 rest=Complement[Range[12],ids];
 keep=Complement[Range[12],{idx[{3,2}]}];
 F=U+J+a*M+(1/2)*C;
 T10=F[[rest,rest]];
 T11=F[[keep,keep]];
 d10=Factor[Det[GSTHalfCurvatureKrylov[T10,seed[[rest]],10]]];
 e1=Factor[Det[T10-IdentityMatrix[10]]];
 d11=Factor[Det[GSTHalfCurvatureKrylov[T11,seed[[keep]],11]]];
 rP8=Table[Mod[GSTHalfCurvatureP8[k],13],{k,0,12}];
 rQ2=Table[Mod[GSTHalfCurvatureQ2[k],13],{k,0,12}];
 cert=<|
   "degreeKrylovKernel"->Exponent[d11,a],
   "D10EqualsP8over256"->TrueQ[
      Expand[256*d10-GSTHalfCurvatureP8[a]]===0],
   "detDminusIEqualsQ2over2"->TrueQ[
      Expand[2*e1-GSTHalfCurvatureQ2[a]]===0],
   "11x11ExactFactorization"->TrueQ[
      Expand[512*d11-GSTHalfCurvatureP8[a]*GSTHalfCurvatureQ2[a]]===0],
   "11x11BlockSylvesterIdentity"->TrueQ[
      Expand[d11-d10*e1]===0],
   "Q2PositiveSquareIdentity"->TrueQ[
      Expand[5*GSTHalfCurvatureQ2[a]-((10*a-18)^2+21)]===0],
   "P8Mod13AllResidues"->rP8,
   "Q2Mod13AllResidues"->rQ2,
   "P8NoMod13Root"->FreeQ[rP8,0],
   "Q2NoMod13Root"->FreeQ[rQ2,0],
   "P8LeadingNonzeroMod13"->(Mod[36864,13]!=0),
   "Q2LeadingNonzeroMod13"->(Mod[20,13]!=0),
   "det11AtZero"->(d11/.a->0)
 |>;
 cert=Append[cert,"allPassed"->(
   Lookup[cert,"D10EqualsP8over256"]&&
   Lookup[cert,"detDminusIEqualsQ2over2"]&&
   Lookup[cert,"11x11ExactFactorization"]&&
   Lookup[cert,"11x11BlockSylvesterIdentity"]&&
   Lookup[cert,"Q2PositiveSquareIdentity"]&&
   Lookup[cert,"P8NoMod13Root"]&&
   Lookup[cert,"Q2NoMod13Root"]&&
   Lookup[cert,"P8LeadingNonzeroMod13"]&&
   Lookup[cert,"Q2LeadingNonzeroMod13"]&&
   Lookup[cert,"det11AtZero"]==799272885/512)];
 Print[cert];cert
]
