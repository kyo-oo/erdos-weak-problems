ClearAll["Global`*"];
checks=0; failures={};
ck[p_,tag_]:=(checks++;If[!TrueQ[p],AppendTo[failures,tag]]);
vecs=Tuples[Range[-2,2],2]; frows=Tuples[Range[-1,1],2]; arows=Tuples[Range[0,5],2];
(* Independent order detector: enumerate every possible annihilator, not GCD. *)
isTors[f_,a_,x_]:=AnyTrue[Range[6],Function[n,n (f.x)==0 && Mod[n (a.x),6]==0]];
isExact[f_,a_,x_]:=f.x==0 && Mod[a.x,6]==0;
rows=Table[Module[{rc=0,ec=0},
 Do[Do[
  tr=isTors[f,a,x];rc+=Boole[tr];ec+=Boole[isExact[f,a,x]];
  ck[tr==(f.x==0),"torsion iff free zero"];
  ck[!tr || isExact[f,a,6 x],"six kills finite part"];
  Do[ck[isTors[f,a,k x]==tr,"saturation"],{k,{2,3,4}}],
 {x,vecs}],{a,arows}];{f,rc,ec}],{f,frows}];
basis={{1,-1,0},{0,0,1}};exactBasis={{1,-1,1},{0,0,6}};
cc=0;sc=0;zc=0;
Do[cc++;sat=x[[1]]+x[[2]]==0;
 ex=sat && Mod[x[[1]]+2 x[[2]]+x[[3]],6]==0;
 If[sat,sc++;ab={x[[1]],x[[3]]};
  ck[ab.basis==x,"saturated coordinate reconstruction"];
  ck[ex==(Mod[ab[[2]]-ab[[1]],6]==0),"exact lattice congruence"];
  If[ex,zc++;ck[{ab[[1]],(ab[[2]]-ab[[1]])/6}.exactBasis==x,"kernel reconstruction"]]],
 {x,Tuples[Range[-3,3],3]}];
ck[Abs[Det[{{1,1},{0,6}}]]==6,"index six"];
lam={{2,1},{1,2}};
adj={{lam[[2,2]],-lam[[1,2]]},{-lam[[2,1]],lam[[1,1]]}};
ck[adj.lam==3 IdentityMatrix[2],"isogeny inverse up to degree"];
kernels=Table[Module[{xs=Select[Tuples[Range[0,d-1],2],Mod[lam.#,d]=={0,0}&]},
 Do[ck[Mod[3 x,d]=={0,0},"isogeny kernel torsion"],{x,xs}];{d,Length[xs]}],{d,2,12}];
degrees=Flatten[Table[d=n^(2 r);ck[(1/d)*d==1,"normalized source degree"];{r,n,d},{r,0,4},{n,1,6}],1];
ExportString[<|"all_passed"->(failures=={}),"assertions"->checks,"failures"->failures,
 "kernel_version"->$Version,"relation_rows"->rows,"basis_index"->6,
 "lattice_vector_counts"->{cc,sc,zc},"isogeny_kernel_counts"->kernels,
 "cover_degrees"->degrees|>,"RawJSON","Compact"->True]
