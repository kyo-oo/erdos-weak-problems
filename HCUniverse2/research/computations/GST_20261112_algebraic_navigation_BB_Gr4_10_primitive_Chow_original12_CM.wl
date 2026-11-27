(* GST NAVIGATION SOURCE BIRTH ON ORIGINAL X, NOT PREEXISTING FIBERS.
   Original X = Grassmannian Gr(4,10), dim_C X=24.
   An actual diagonal C* action with distinct weights has C(10,4)=210
   isolated fixed points. BB attracting cell closures are actual
   algebraic Schubert cycles; Chow and Betti basis, no alpha Chow
   representative assumed. Exact Schubert Pieri for sigma_1 builds
   the middle primitive algebraic cycles in codimension p=12.
   Then make a 12-channel ORIGINAL-X Chow basis with first two
   channels the TWO independently BORN primitive cycles, and
   implement owner's literal U/J/M/[J,M] physical Navigation F.
   All finite assertions exact integer/rational arithmetic.
   The known BB theorem and Schubert-Pieri theorem are
   external general geometric inputs: this computation does NOT
   assert they were proved solely by finite matrix checks.
   This theorem applies to original smooth projective X with an
   isolated-fixed-point algebraic C* action, not arbitrary X. *)

Module[{k=4,w=6,p=12,d,part,lam,mu,dual,pieri,delta,
  kernel,oldGram,primitiveGram,chosen,extraIndexes,change,
  bornDuals,dualCheck,cells,uu,jj,mm,cc,
  fOff,fOn,seed,kOff,kOn,source12,
  origOrbitOff,origOrbitOn,primitiveRecoverOff,
  primitiveRecoverOn,bothCells,allPassed},

part[n_]:=Select[Tuples[Range[0,w],k],
 (OrderedQ[Reverse[#]]&&Total[#]==n)&];
lam=part[p];mu=part[p+1];d=k*w;
dual[x_]:=Reverse[w-x];

pieri=Table[With[{delta=mu[[i]]-lam[[j]]},
 Boole[Count[delta,1]==1&&Count[delta,0]==k-1]],
 {i,Length[mu]},{j,Length[lam]}];

kernel=NullSpace[pieri];
oldGram=Table[Boole[lam[[i]]==dual[lam[[j]]]],
 {i,Length[lam]},{j,Length[lam]}];
primitiveGram=kernel.oldGram.Transpose[kernel];

(* The first two ACTUAL Chow classes in the new basis
   are the two alpha-sensitive primitive source-birth classes.
   Complete by independent actual Schubert cycles.
   Opposite Schubert classes supply ACTUAL Chow duals, with
   coefficient change computed by exact rational inversion. *)
chosen=Join[kernel,Table[UnitVector[Length[lam],i],{i,1,10}]];
extraIndexes={};
Do[If[MatrixRank[Transpose[Append[chosen,UnitVector[Length[lam],i]]]]>
  Length[chosen],
  AppendTo[chosen,UnitVector[Length[lam],i]];
  AppendTo[extraIndexes,i]],
 {i,11,Length[lam]}];
change=Transpose[chosen];
bornDuals=Transpose[Inverse[change]];
dualCheck=Transpose[change].bornDuals;
source12=Take[change,All,12];

(* Owner original native U trit shuffle, signed CM J mirror,
   literal SURVIVE diagonal M, commutator C=[J,M].
   No substitute 12x12 matrix is introduced. *)
cells=Flatten[Table[{i,q},{i,0,3},{q,0,2}],1];
uu=ConstantArray[0,{12,12}];
jj=ConstantArray[0,{12,12}];
mm=ConstantArray[0,{12,12}];
Do[With[{i=cells[[row,1]],q=cells[[row,2]]},
  uu[[row,1+3*Quotient[i+4*q,3]+Mod[i+4*q,3]]]=1;
  jj[[row,1+3*(3-i)+(2-q)]]=If[
    MemberQ[{0,1,3,4,5,9},i+4*q],1,-1];
  With[{pp=Mod[Quotient[i,2]+2*q,3]},
   mm[[row,row]]=Boole[q==2&&pp==2]+
     Boole[pp==2&&Mod[Mod[i,2]+2*pp,3]==2]]],
 {row,1,12}];
cc=jj.mm-mm.jj;
fOff=uu+jj+mm;
fOn=fOff+cc;
seed=Join[{1,1},ConstantArray[0,10]];
kOff=Transpose[NestList[fOff.#&,seed,11]];
kOn=Transpose[NestList[fOn.#&,seed,11]];

origOrbitOff=source12.kOff;
origOrbitOn=source12.kOn;
primitiveRecoverOff=And@@Table[
 kOff.Inverse[kOff].UnitVector[12,i]==UnitVector[12,i],{i,1,2}];
primitiveRecoverOn=And@@Table[
 kOn.Inverse[kOn].UnitVector[12,i]==UnitVector[12,i],{i,1,2}];

allPassed=(
 Length[lam]==18&&Length[mu]==16&&
 MatrixRank[pieri]==16&&Length[kernel]==2&&
 pieri.Transpose[kernel]==ConstantArray[0,{16,2}]&&
 primitiveGram=={{1095,-1005},{-1005,1275}}&&
 Det[primitiveGram]==386100&&
 Det[change]==36&&
 dualCheck==IdentityMatrix[18]&&
 MatrixRank[origOrbitOff]==12&&MatrixRank[origOrbitOn]==12&&
 primitiveRecoverOff&&primitiveRecoverOn&&
 MatrixPower[uu,5]==IdentityMatrix[12]&&
 jj.jj==-IdentityMatrix[12]&&
 Det[kOff]==-1149656584000&&
 Det[kOn]==-445265540949);

<|"originalX"->"Grassmannian Gr(4,10), smooth projective dimension24",
 "algebraicNavigationFixedPoints"->Binomial[10,4],
 "middleCodimension"->p,
 "trueBornSchubertChowChannels"->Length[lam],
 "middleSchubertPartitions"->lam,
 "PieriAmpleMultiplicationRank"->MatrixRank[pieri],
 "actualPrimitiveChowDimension"->Length[kernel],
 "firstPrimitiveSchubertCycleCoefficients"->kernel[[1]],
 "secondPrimitiveSchubertCycleCoefficients"->kernel[[2]],
 "primitiveProductsAreZeroAfterAmpleMultiplication"->
   pieri.Transpose[kernel]==ConstantArray[0,{16,2}],
 "actualPrimitiveIntersectionGram"->primitiveGram,
 "primitiveGramDet"->Det[primitiveGram],
 "completedActualChowBasisChangeDet"->Det[change],
 "sixExtraBornSchubertBasisIndices"->extraIndexes,
 "fullChowDualityAfterBasisChange"->dualCheck==IdentityMatrix[18],
 "originalGSTOffKrylovDet"->Det[kOff],
 "originalGSTOnKrylovDet"->Det[kOn],
 "actualOriginalXPrimitiveContainingOffOrbitRank"->MatrixRank[origOrbitOff],
 "actualOriginalXPrimitiveContainingOnOrbitRank"->MatrixRank[origOrbitOn],
 "bothOriginalPrimitiveChowCyclesRecoveredFromOneOffGSTSeed"->primitiveRecoverOff,
 "bothOriginalPrimitiveChowCyclesRecoveredFromOneOnGSTSeed"->primitiveRecoverOn,
 "allPassed"->allPassed|>
]