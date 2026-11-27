(* Exact GST multi-holonomy finite audit. Rational, stateless, no randomness.
   Mathematical proof: research/derivations/GST_all_graph_causal_holonomy_hodge_birth_2026-10-22.tex *)
ClearAll[cShift,cDel,cRank,cMat,cI,cB,cPm,cRp,cSp,t,s,u,v,A,P,cyc,fold,smooth,pos,cases,polys];
cShift[n_]:=Table[Boole[j==Mod[i,n]+1],{i,n},{j,n}];
cDel[m_,powers_]:=Join@@Map[(MatrixPower[m,#]-IdentityMatrix[Length[m]])&,powers];
cRank[n_,g_]:=Module[{cob,rank},cob=cDel[cShift[n],Join[{1,n-1},Table[Mod[j,n],{j,0,g-3}]]];rank=MatrixRank[cob];{n,g,n-rank,g n-rank,g n-rank==(g-1)n+n-rank}];
cases=Flatten[Table[cRank[n,g],{n,2,7},{g,2,5}],1];
cMat={{0,0,1,0},{0,0,0,1},{1,0,0,0},{0,1,0,0}};
cI=IdentityMatrix[4];cB=Join[cMat-cI,-cMat-cI];cPm=(cI+cMat)/2;cSp=(cI-cMat)/2;
cRp=Join[cPm,-cSp,2];cSp=Join[cPm,-cSp];
t=Unique["t"];s=Unique["s"];u=Unique["u"];v=Unique["v"];A=t^2 s^2 u v;P=1+t s(u+v)+A;
cyc[n_]:=Expand[Sum[With[{gg=GCD[n,j],ll=n/GCD[n,j]},(P/.{t->(-1)^(ll-1)t^ll,s->s^ll,u->u^ll,v->v^ll})^gg],{j,0,n-1}]/n];
fold[n_,g_]:=Expand[(1+t)cyc[n]+(A+(g-1)t)P^n];
smooth[n_,g_]:=Expand[(1+A)cyc[n]+t s(u+v)((g-1)P^n+cyc[n])];
pos[poly_]:=And@@Map[(IntegerQ[#]&&#>=0)&,Last/@CoefficientRules[poly,{t,s,u,v}]];
polys=Flatten[Table[{n,g,pos[fold[n,g]],pos[smooth[n,g]]},{n,2,4},{g,1,4}],1];
<|"rankChecked"->Length[cases],"rankPassed"->Count[cases,z_/;z[[5]]===True],
"polyChecked"->Length[polys],"polyPassed"->Count[polys,z_/;z[[3]]===True&&z[[4]]===True],
"distinctFixed"->4-MatrixRank[cB],"distinctCoker"->8-MatrixRank[cB],
"returnKillsBoundary"->(cRp.cB==ConstantArray[0,{4,4}]),
"returnSectionId"->(cRp.cSp==cI),
"Y_H2_W1"->Expand[Coefficient[Coefficient[fold[2,2],t,2],s,1]],
"S_H2_W2"->Expand[Coefficient[Coefficient[smooth[2,2],t,2],s,2]]|>