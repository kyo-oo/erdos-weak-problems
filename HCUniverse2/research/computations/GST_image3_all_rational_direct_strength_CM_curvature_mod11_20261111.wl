(* Exact original GST all-rational DIRECT-SURVIVE strength theorem
   at CM curvature strength b=1.
   F_a=U+J+a M + [J,M].
   Structural 2+10 decomposition:
     det Krylov_12 = det Krylov_2 * det Krylov_10 * spectral resultant
                  = P8(a) P12(a).
   Complete mod-11 root exclusion and leading coefficient tests prove
   this determinant !=0 for EVERY rational a. NO Chow/Hodge claim. *)

ClearAll[GSTDirectP8,GSTDirectP12];
GSTDirectP8[a_]:=-130491-27750*a-25120*a^2-31800*a^3+
  7068*a^4-3304*a^5+1520*a^6-80*a^7+64*a^8;
GSTDirectP12[a_]:=-10623+474348*a+710952*a^2+
  141208*a^3+696720*a^4-249912*a^5+418988*a^6-
  196384*a^7+166048*a^8-59264*a^9+33664*a^10-
  6912*a^11+2560*a^12;

Module[{cells,idx,sh,mir,sgn,surv,u,j,m,c,seed,f,ids,small,
a,x,fix,ten,kry,d2,d10,res,dglobal,r8,r12,leading,cert},
cells=Flatten[Table[{i,k},{i,0,3},{k,0,2}],1];
idx[z_]:=First[FirstPosition[cells,z]];
sh[{i_,k_}]:={Quotient[i+4*k,3],Mod[i+4*k,3]};
mir[{i_,k_}]:={3-i,2-k};
sgn[{i_,k_}]:=If[MemberQ[{0,1,3,4,5,9},i+4*k],1,-1];
surv[{i_,k_}]:=Module[{p=Mod[Quotient[i,2]+2*k,3],q},
 q=Mod[Mod[i,2]+2*p,3];
 Boole[k==2]Boole[p==2]+Boole[p==2]Boole[q==2]];
u=Table[Boole[z==idx[sh[cells[[i]]]]],{i,12},{z,12}];
j=Table[sgn[cells[[i]]]*Boole[z==idx[mir[cells[[i]]]]],{i,12},{z,12}];
m=DiagonalMatrix[surv/@cells];c=j.m-m.j;
seed=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cells;
f=u+j+a*m+c; ids={idx[{0,0}],idx[{3,2}]};
small=Complement[Range[12],ids];
fix=f[[ids,ids]];ten=f[[small,small]];
kry[t_,v_,n_]:=Transpose[NestList[t.#&,v,n-1]];
d2=Factor[Det[kry[fix,seed[[ids]],2]]];
d10=Factor[Det[kry[ten,seed[[small]],10]]];
res=Factor[Resultant[CharacteristicPolynomial[fix,x],
                      CharacteristicPolynomial[ten,x],x]];
dglobal=Factor[Det[kry[f,seed,12]]];
r8=Table[Mod[GSTDirectP8[k],11],{k,0,10}];
r12=Table[Mod[GSTDirectP12[k],11],{k,0,10}];
leading={Mod[64,11],Mod[2560,11]};
cert=<|
 "fixed2ControllabilityDet"->d2,
 "rotating10DetDegree"->Exponent[d10,a],
 "spectralResultantDegree"->Exponent[res,a],
 "full12DetDegree"->Exponent[dglobal,a],
 "P8FullF11Residues"->r8,
 "P12FullF11Residues"->r12,
 "leadingCoefficientsMod11"->leading,
 "direct10EqualsP8"->TrueQ[Expand[d10-GSTDirectP8[a]]===0],
 "resultantEqualsP12"->TrueQ[Expand[res-GSTDirectP12[a]]===0],
 "full12EqualsProduct"->TrueQ[Expand[dglobal-GSTDirectP8[a]*GSTDirectP12[a]]===0],
 "F11NoRoots"->(FreeQ[r8,0]&&FreeQ[r12,0]),
 "validRationalRootReduction"->AllTrue[leading,#!=0&],
 "balancedA1Det"->(GSTDirectP8[1]*GSTDirectP12[1]),
 "allPassed"->(d2===1&&Exponent[d10,a]===8&&Exponent[res,a]===12&&
  TrueQ[Expand[d10-GSTDirectP8[a]]===0]&&
  TrueQ[Expand[res-GSTDirectP12[a]]===0]&&
  TrueQ[Expand[dglobal-GSTDirectP8[a]*GSTDirectP12[a]]===0]&&
  FreeQ[r8,0]&&FreeQ[r12,0]&&AllTrue[leading,#!=0&]&&
  GSTDirectP8[1]*GSTDirectP12[1]==-445265540949)|>;
Print[cert];cert
]
