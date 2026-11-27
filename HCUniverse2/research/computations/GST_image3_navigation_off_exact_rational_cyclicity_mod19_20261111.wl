(* Exact ORIGINAL GST navigation-off source classification:
   F_(a,0)=U+J+aM on the author's real 4x3 Wave-I cell space.
   Two original fixed cells and ten rotating cells are invariant.
   Full Krylov determinant = -4 a^2 (a+1) Q8(a) Q9(a).
   No rational root of Q8 or Q9 by a COMPLETE F19 root check,
   and their leading coefficients are units modulo 19.
   Therefore full native cyclic rank 12 iff a ≠ 0 and a ≠ -1.
   This is native GST algebra, NOT all-varieties Hodge algebraicity. *)

ClearAll[GSTOffQ8,GSTOffQ9,GSTOffKrylov];
GSTOffQ8[a_]:=411701+899200*a-342272*a^2-123812*a^3-
  14492*a^4-25296*a^5+4672*a^6-832*a^7+256*a^8;
GSTOffQ9[a_]:=12176+45312*a+72685*a^2+59539*a^3+
  15088*a^4-15320*a^5-13120*a^6-1376*a^7+
  1984*a^8+640*a^9;
GSTOffKrylov[T_,v_,n_]:=Transpose[NestList[T.#&,v,n-1]];

Module[{cells,idx,sh,mir,sgn,surv,U,J,M,F,seed,a,x,ids,rest,
   fixed,ten,d2,d10,rs,global,r8,r9,leads,cert},
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
  F=U+J+a*M;
  seed=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cells;
  ids={idx[{0,0}],idx[{3,2}]};
  rest=Complement[Range[12],ids];
  fixed=F[[ids,ids]];
  ten=F[[rest,rest]];
  d2=Factor[Det[GSTOffKrylov[fixed,seed[[ids]],2]]];
  d10=Factor[Det[GSTOffKrylov[ten,seed[[rest]],10]]];
  rs=Factor[Resultant[CharacteristicPolynomial[fixed,x],
                      CharacteristicPolynomial[ten,x],x]];
  global=Factor[Det[GSTOffKrylov[F,seed,12]]];
  r8=Table[Mod[GSTOffQ8[k],19],{k,0,18}];
  r9=Table[Mod[GSTOffQ9[k],19],{k,0,18}];
  leads={Mod[256,19],Mod[640,19]};
  cert=<|
    "fixed2Det"->d2,
    "ten10Polynomial"->d10,
    "spectralResultant"->rs,
    "global12Polynomial"->global,
    "tenMatchesQ8"->TrueQ[Expand[d10-GSTOffQ8[a]]===0],
    "resultantMatches"->TrueQ[
      Expand[rs-4*a^2*(1+a)*GSTOffQ9[a]]===0],
    "fullFactorizationMatches"->TrueQ[
      Expand[global+4*a^2*(1+a)*GSTOffQ8[a]*GSTOffQ9[a]]===0],
    "all19Q8Residues"->r8,
    "all19Q9Residues"->r9,
    "leadingMod19"->leads,
    "noMod19Roots"->(FreeQ[r8,0]&&FreeQ[r9,0]),
    "leadingUnits"->AllTrue[leads,#!=0&],
    "rankAtA0"->MatrixRank[GSTOffKrylov[F/.a->0,seed,12]],
    "rankAtAMinus1"->MatrixRank[GSTOffKrylov[F/.a->-1,seed,12]],
    "rankAtA1"->MatrixRank[GSTOffKrylov[F/.a->1,seed,12]],
    "allPassed"->(
      d2===-1 &&
      TrueQ[Expand[d10-GSTOffQ8[a]]===0] &&
      TrueQ[Expand[rs-4*a^2*(1+a)*GSTOffQ9[a]]===0] &&
      TrueQ[Expand[global+4*a^2*(1+a)*GSTOffQ8[a]*GSTOffQ9[a]]===0] &&
      FreeQ[r8,0]&&FreeQ[r9,0]&&AllTrue[leads,#!=0&] &&
      MatrixRank[GSTOffKrylov[F/.a->0,seed,12]]==10 &&
      MatrixRank[GSTOffKrylov[F/.a->-1,seed,12]]==11 &&
      MatrixRank[GSTOffKrylov[F/.a->1,seed,12]]==12)|>;
  Print[cert];cert
]
