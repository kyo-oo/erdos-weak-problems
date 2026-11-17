(* Exact ORIGINAL GST U+J+SURVIVE Wave-I to original-X ample Chow-line quotient check.
   User's original GST nativeWaveReadout_T is already proved in Lean.
   Independent exact Wolfram matrix check at 12 cells and 3 N-hole addresses.
   Finite n=0..8 tests supplement, do not replace, the all-N Lean identity.
*)
ClearAll[cc,idx,shuffle,mirror,sign,tw,mid,surv,uu,jj,mm,tt,rr,seed,
 holeAddresses,totalFold,fullSeed,rows,oneHoleTests,result];
cc=Flatten[Table[{c,d},{c,0,3},{d,0,2}],1];
idx[a_]:=First[FirstPosition[cc,a]];
shuffle[{c_,d_}]:={Quotient[c+4d,3],Mod[c+4d,3]};
mirror[{c_,d_}]:={3-c,2-d};
sign[{c_,d_}]:=If[MemberQ[{0,1,3,4,5,9},c+4d],1,-1];
tw[z_]:=Boole[z==2];
mid[c_,d_]:=Mod[Quotient[c,2]+2d,3];
surv[c_,d_]:=Module[{m=mid[c,d],fn},
  fn=Mod[Mod[c,2]+2m,3];tw[d]tw[m]+tw[m]tw[fn]];
uu=Table[Boole[j==idx[shuffle[cc[[i]]]]],{i,12},{j,12}];
jj=Table[sign[cc[[i]]]*Boole[j==idx[mirror[cc[[i]]]]],{i,12},{j,12}];
mm=DiagonalMatrix[(surv@@#)&/@cc];
tt=uu+jj+mm;
rr=UnitVector[12,idx[{0,0}]]-UnitVector[12,idx[{3,2}]];
seed=Boole[MemberQ[{{0,0},{0,1}},#]]&/@cc;
holeAddresses={0,3,9};
totalFold=KroneckerProduct[IdentityMatrix[3],tt]+
 KroneckerProduct[DiagonalMatrix[10holeAddresses],IdentityMatrix[12]];
fullSeed=Flatten[ConstantArray[seed,3]];
rows=Table[Flatten[KroneckerProduct[UnitVector[3,i],rr]],{i,3}];
oneHoleTests=Table[
 <|"hole"->i,"lambda"->2+10holeAddresses[[i]],
 "leftEigen"->(rows[[i]].totalFold==(2+10holeAddresses[[i]])rows[[i]]),
 "initialSeed"->(rows[[i]].fullSeed==1),
 "orbit0to8"->And@@Table[
   rows[[i]].MatrixPower[totalFold,n].fullSeed==
    (2+10holeAddresses[[i]])^n,{n,0,8}]|>,{i,3}];
result=<|"originalU5"->(MatrixPower[uu,5]==IdentityMatrix[12]),
 "originalJSquaredMinusI"->(jj.jj==-IdentityMatrix[12]),
 "baseLeftEigen2"->(rr.tt==2rr),
 "sourceReadout1"->(rr.seed==1),
 "fullWaveDimensions"->Dimensions[totalFold],
 "holeTests"->oneHoleTests,
 "allPassed"->And@@Flatten[{
  MatrixPower[uu,5]==IdentityMatrix[12],
  jj.jj==-IdentityMatrix[12],
  rr.tt==2rr,rr.seed==1,
  (Lookup[#,"leftEigen"]&&Lookup[#,"initialSeed"]&&Lookup[#,"orbit0to8"]&/@oneHoleTests)}]|>;
Print[result];result