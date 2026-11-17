Module[{fixtures, tables={}, failures={}, assertions=0, ok, rk, name, caps, no, p, terms, ce, d, s, dim, base, full, nb, nn, odd, index, mulI, mulS, sum, sign, ij, e, v, a, c, i, j, k, q, uidx, vidx, dal, dd, degrees, bd, mats, dr, cyc, boundaries, span, oldrank, rr, reps, allreps, ad, lr, src, dst, lm, b, betti, grams, gr, top, pairing, gram, get, loss, flat, pred, rtotal, tor, jet},
ok[test_, label_]:=(assertions++;If[!TrueQ[test],AppendTo[failures,label]]);
rk[m_]:=If[Length[m]==0 || Length[First[m]]==0,0,MatrixRank[m]];
fixtures={
{"P1-flat",{1},0,1,{{{0},0,0}}},
{"P1-point",{1},0,1,{{{1},0,1}}},
{"P2-h",{2},0,1,{{{1},0,1}}},
{"P2-point",{2},0,2,{{{2},0,1}}},
{"P2xP2-square",{2,2},0,2,{{{2,0},0,1}}},
{"P2xP2-mixed",{2,2},0,2,{{{1,1},0,1}}},
{"P2xP2-rational",{2,2},0,2,{{{2,0},0,1/2},{{1,1},0,-2/3}}},
{"E-flat",{},2,1,{{{},0,0}}},
{"E-point",{},2,1,{{{},3,1}}},
{"P1xE-mixed",{1},2,1,{{{1},0,1},{{0},3,1}}},
{"P1xE-top",{1},2,2,{{{1},3,1}}},
{"ExE-symplectic",{},4,1,{{{},3,1},{{},12,1}}},
{"ExE-top",{},4,2,{{{},15,1}}}};
Do[
{name,caps,no,p,terms}=fixture;ce=Length[caps];d=2Total[caps]+no;s=2p-1;dim=d+2s;
base=Tuples[Join[Table[Range[0,c],{c,caps}],ConstantArray[{0,1},no]]];
full=Tuples[Join[Table[Range[0,c],{c,caps}],ConstantArray[{0,1},no+2]]];
nb=Length[base];nn=Length[full];odd=Range[ce+1,ce+no+2];uidx=ce+no+1;vidx=uidx+1;
index=AssociationThread[(ToString[#,InputForm]& /@ full),Range[nn]];
mulI=ConstantArray[0,{nn,nn}];mulS=mulI;
Do[sum=full[[i]]+full[[j]];
If[And@@Thread[sum<=Join[caps,ConstantArray[1,no+2]]],
sign=(-1)^Total[Flatten[Table[If[a>c,full[[i,a]]full[[j,c]],0],{a,odd},{c,odd}]]];
mulI[[i,j]]=index[ToString[sum,InputForm]];mulS[[i,j]]=sign],{i,nn},{j,nn}];
degrees=(2Total[Take[#,ce]]+Total[Take[#, {ce+1,ce+no}]]+s Total[Take[#,-2]]& /@ full);
(* Empty odd-base slice requires its separate zero convention. *)
If[no==0,degrees=(2Total[Take[#,ce]]+s Total[Take[#,-2]]& /@ full)];
bd=Table[Flatten[Position[degrees,k]],{k,0,dim+1}];
dd=ConstantArray[0,{nn,nn}];
Do[If[full[[j,uidx]]==1,
e=full[[j]];e[[uidx]]=0;i=index[ToString[e,InputForm]];
Do[dal=Join[term[[1]],Table[Mod[Quotient[term[[2]],2^a],2],{a,0,no-1}],{0,0}];
a=index[ToString[dal,InputForm]];ij=mulI[[i,a]];
If[ij!=0,dd[[ij,j]]+=term[[3]]mulS[[i,a]](-1)^Total[If[no==0,{},Take[e,{ce+1,ce+no}]]]],{term,terms}]],{j,nn}];
ok[dd.dd==ConstantArray[0,{nn,nn}],name<>" d2"];
ok[And@@Flatten[Table[dd[[i,j]]==0 || degrees[[i]]==degrees[[j]]+1,{i,nn},{j,nn}]],name<>" degree"];
mats=Table[dd[[bd[[k+2]],bd[[k+1]]]],{k,0,dim}];
dr=rk /@ mats;allreps={};
Do[src=bd[[k+1]];dst=bd[[k+2]];
cyc=If[Length[src]==0,{},If[Length[dst]==0,IdentityMatrix[Length[src]],NullSpace[mats[[k+1]]]]];
boundaries=If[k==0,{},Transpose[dd[[src,bd[[k]]]]]];
span=boundaries;oldrank=rk[span];reps={};
Do[rr=rk[Append[span,v]];If[rr>oldrank,AppendTo[span,v];AppendTo[reps,v];oldrank=rr],{v,cyc}];
AppendTo[allreps,reps],{k,0,dim}];
ad=Table[Count[(2Total[Take[#,ce]]+Total[Drop[#,ce]]& /@ base),j],{j,0,d}];
lr={};
Do[src=Select[Range[nb],2Total[Take[base[[#]],ce]]+Total[Drop[base[[#]],ce]]==j&];
dst=Select[Range[nb],2Total[Take[base[[#]],ce]]+Total[Drop[base[[#]],ce]]==j+2p&];
lm=ConstantArray[0,{Length[dst],Length[src]}];
Do[i=index[ToString[Join[base[[src[[a]]]],{0,0}],InputForm]];
Do[dal=Join[term[[1]],Table[Mod[Quotient[term[[2]],2^q],2],{q,0,no-1}],{0,0}];
c=index[ToString[dal,InputForm]];ij=mulI[[i,c]];
If[ij!=0,k=FirstPosition[base,Take[full[[ij]],ce+no]];
If[MemberQ[dst,First[k]],b=First[FirstPosition[dst,First[k]]];lm[[b,a]]+=term[[3]]mulS[[i,c]]]],{term,terms}],{a,Length[src]}];
AppendTo[lr,rk[lm]],{j,0,d}];
get[row_,a_]:=If[0<=a<Length[row],row[[a+1]],0];
top=index[ToString[Join[caps,ConstantArray[1,no+2]],InputForm]];
pairing=Table[If[mulI[[i,j]]==top,mulS[[i,j]],0],{i,nn},{j,nn}];
betti={};grams={};loss={};
Do[b=Length[bd[[k+1]]]-dr[[k+1]]-If[k==0,0,dr[[k]]];
pred=get[ad,k]+2get[ad,k-s]+get[ad,k-2s]-get[lr,k-2p]-get[lr,k-s]-get[lr,k-s-2p]-get[lr,k-2s];
ok[b==pred && b==Length[allreps[[k+1]]],name<>" Betti "<>ToString[k]];AppendTo[betti,b];
flat=get[ad,k]+2get[ad,k-s]+get[ad,k-2s];
ok[flat-b==Total[Flatten[Table[get[lr,k-s-a-c],{a,{0,1}},{c,{0,s}}]]],name<>" loss "<>ToString[k]];AppendTo[loss,flat-b];
gr=If[b==0,0,rk[allreps[[k+1]].pairing[[bd[[k+1]],bd[[dim-k+1]]]].Transpose[allreps[[dim-k+1]]]]];
ok[gr==b && b==Length[allreps[[dim-k+1]]],name<>" pairing "<>ToString[k]];AppendTo[grams,gr],{k,0,dim}];
rtotal=Total[lr];tor=2rtotal;
ok[Total[betti]==4(nb-rtotal),name<>" total"];
ok[betti==Reverse[betti],name<>" PD"];
ok[And@@Table[get[lr,j]==get[lr,d-2p-j],{j,0,d}],name<>" adjoint ranks"];
ok[Total[loss]==4rtotal,name<>" loss total"];
ok[If[rtotal==0,Total[loss]==0,Total[Take[loss,s]]==0 && loss[[s+1]]==1],name<>" first loss"];
ok[Total[betti]+2tor==4nb,name<>" tensor Tor"];
jet=ArrayFlatten[{{ConstantArray[0,{nn,nn}],ConstantArray[0,{nn,nn}]},{dd,ConstantArray[0,{nn,nn}]}}];
ok[rk[jet]==2rtotal,name<>" jet obstruction rank"];
ok[jet.jet==ConstantArray[0,{2nn,2nn}],name<>" jet d2"];
AppendTo[tables,<|"name"->name,"p"->p,"formal_dimension"->dim,"base_betti"->ad,"cup_ranks"->lr,"betti"->betti,"pairing_ranks"->grams,"total_betti"->Total[betti],"torsion_count"->tor,"tensor_special"->Total[betti]+tor,"tor_special"->tor|>],
{fixture,fixtures}];
ExportString[<|"all_passed"->(failures=={}),"assertions"->assertions,"failures"->failures,"kernel_version"->$Version,"tables"->tables|>,"RawJSON","Compact"->True]
]
