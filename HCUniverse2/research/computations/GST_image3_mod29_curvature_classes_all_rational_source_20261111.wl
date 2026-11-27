(* Exact independent mod-29 certificates for the original Image-3
   two-parameter native U/J/M/[J,M] source. The U/J/M operators
   are reconstructed from their author-original 4x3 cell laws.

   For EVERY integer b with b mod 29 in {9,14,21,27}, the full
   rational 12-state source is cyclic for EVERY rational a.

   Proof contract: 29 rational-reduction residues exhaust F29;
   the degree-20 rational-a leading coefficient must remain a unit
   mod29. Rational-root theorem then rules out all Q-roots for
   each fixed integer b in the congruence class. No Hodge claim. *)

Module[{cells,idx,sh,mir,sgn,surv,U,J,M,C,seed,ids,rest,
 a,b,x,F,F2,F10,kry,d2,d10,res,poly,good,rows,lead,checks},
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
F=U+J+a*M+b*C;
F2=F[[ids,ids]];F10=F[[rest,rest]];
kry[T_,v_,n_]:=Transpose[NestList[T.#&,v,n-1]];
d2=Factor[Det[kry[F2,seed[[ids]],2]]];
d10=Factor[Det[kry[F10,seed[[rest]],10]]];
res=Factor[Resultant[CharacteristicPolynomial[F2,x],
                     CharacteristicPolynomial[F10,x],x]];
poly=Factor[d2*d10*res];
good={9,14,21,27};
rows=Table[Module[{p29,ld},
   p29=Table[Mod[poly/.{a->k,b->v},29],{k,0,28}];
   ld=Mod[163840*(2*v-1)*(v-2)^2,29];
   <|"bMod29"->v,"allDetResidues"->p29,
     "leadingA20Mod29"->ld,
     "all29Nonzero"->FreeQ[p29,0],
     "leadingNonzero"->(ld!=0)|>],{v,good}];
checks=<|"curvatureClasses"->good,
  "fullClassRecords"->rows,
  "twoCellExact"->TrueQ[Expand[d2-(2*b-1)]===0],
  "a20LeadingExact"->TrueQ[
      Expand[Coefficient[poly,a,20]-
        163840*(2*b-1)*(b-2)^2]===0],
  "allPassed"->(TrueQ[Expand[d2-(2*b-1)]===0]&&
    TrueQ[Expand[Coefficient[poly,a,20]-
      163840*(2*b-1)*(b-2)^2]===0]&&
    And@@Lookup[rows,"all29Nonzero"]&&
    And@@Lookup[rows,"leadingNonzero"])|>;
Print[checks];checks
]
