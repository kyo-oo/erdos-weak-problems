(* Exact structural factorization of the author's original Image-3 CM/Survive fold.
   F_(a,b)=U+J+a M+b[J,M], on 4 x 3 original carry/trit cells.
   Separates TWO FIXED CELLS from TEN ROTATING CELLS, then identifies:
   det Krylov_12 = det Krylov_2 * det Krylov_10 *
                    Resultant(characteristic2, characteristic10).
   Finite symbolic checks at a=0 and discriminating exact rational samples.
   This is native GST information geometry; it is not an all-X Chow theorem. *)

ClearAll[cmImage3Krylov,b10Polynomial,p16Polynomial];
cmImage3Krylov[T_,v_,n_] := Transpose[NestList[T.#&,v,n-1]];
b10Polynomial[t_] := 411701-2185728*t^2+293888*t^3+3073344*t^4-
  960384*t^5-1658656*t^6+835776*t^7+244932*t^8-
  222264*t^9+36900*t^10;
p16Polynomial[t_] := 255140-1606056*t^2+3096493*t^4-
  2099096*t^6+1818992*t^8-3016960*t^10+
  2444032*t^12-1234944*t^14+331776*t^16;

Module[{cells,idx,sh,mir,sgn,surv,U,J,M,C,seed,t,tw,ids,small,
 v2,v10,tw2,tw10,d2,d10,rs,global,checks,samples,one,result,allChecks,x,b},
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
 ids={idx[{0,0}],idx[{3,2}]};
 small=Complement[Range[12],ids];
 v2=seed[[ids]];v10=seed[[small]];

 (* Polynomial in b at direct source strength a=0 *)
 t=U+J+b*C;
 tw2=t[[ids,ids]]; tw10=t[[small,small]];
 d2=Factor[Det[cmImage3Krylov[tw2,v2,2]]];
 d10=Factor[Det[cmImage3Krylov[tw10,v10,10]]];
 rs=Factor[Resultant[CharacteristicPolynomial[tw2,x],
                      CharacteristicPolynomial[tw10,x],x]];
 global=Factor[Det[cmImage3Krylov[t,seed,12]]];
 checks=<|
   "source2CellDet"->d2,
   "source10CellDet"->d10,
   "spectralResultant"->rs,
   "global12CellDet"->global,
   "source2CellDetExact"->TrueQ[d2===2*b-1],
   "source10IsExistingP10"->TrueQ[Expand[d10-b10Polynomial[b]]===0],
   "resultantIsB4TimesExistingP16"->
     TrueQ[Expand[rs-b^4*p16Polynomial[b]]===0],
   "globalExactFactorization"->
     TrueQ[Expand[global-d2*d10*rs]===0],
   "zeroCrossBlock"->AllTrue[Flatten[t[[ids,small]]],#==0&] &&
     AllTrue[Flatten[t[[small,ids]]],#==0&]|>;

 (* Independent rational specializations in the full two-parameter family. *)
 one[{aa_,bb_}]:=Module[{F,A,D,dA,dD,rD,gD,off},
   F=U+J+aa*M+bb*C;
   A=F[[ids,ids]];D=F[[small,small]];
   off=Join[Flatten[F[[ids,small]]],Flatten[F[[small,ids]]]];
   dA=Det[cmImage3Krylov[A,v2,2]];
   dD=Det[cmImage3Krylov[D,v10,10]];
   rD=Resultant[CharacteristicPolynomial[A,x],
                CharacteristicPolynomial[D,x],x];
   gD=Det[cmImage3Krylov[F,seed,12]];
   <|"parameters"->{aa,bb},"blockInvariant"->AllTrue[off,#==0&],
     "d2"->dA,"d10"->dD,"resultant"->rD,
     "factorIdentity"->TrueQ[gD==dA*dD*rD],
     "globalCyclic"->(gD!=0)|>];
 samples=one/@{{0,1},{1,1},{2,1/3},{-2,5/4},{1,1/2},{0,0}};
 allChecks=Join[
  Lookup[checks,{"source2CellDetExact","source10IsExistingP10",
    "resultantIsB4TimesExistingP16","globalExactFactorization",
    "zeroCrossBlock"}],
  Lookup[samples,"blockInvariant"],
  Lookup[samples,"factorIdentity"]];
 result=<|"symbolicOneParameter"->checks,
   "twoParameterExactSamples"->samples,
   "allPassed"->And@@allChecks|>;
 Print[result];result
]
