(* Exact ORIGINAL GST U/J/M/[J,M] 12-native-cell + TWO world memory
   corrections. The seven nonzero birth couplings B,C are
   NAVIGATION-INDEPENDENT, not fitted case-by-case. All symbolic
   arithmetic uses integer/rational exact matrices; no Chow
   source on arbitrary X is assumed.
   Original source definitions copied from owner's 4-by-3 module.
   Target proof: det(G_{a,b})=a+b(b-1)^2 for every rational a,b,
   with physical direct SURVIVE a=1 and b=0/1 exactly det=1.
   Both physical states are 14x14 cyclic for original mixed seed
   extended by ZERO auxiliary-world input. *)

GSTOrigXCells = Flatten[Table[{i,k},{i,0,3},{k,0,2}],1];
GSTOrigXIdx[z_] := First[FirstPosition[GSTOrigXCells,z]];
GSTOrigXShuffle[{i_,k_}] := {Quotient[i+4*k,3],Mod[i+4*k,3]};
GSTOrigXMirror[{i_,k_}] := {3-i,2-k};
GSTOrigXSign[{i_,k_}] := If[MemberQ[{0,1,3,4,5,9},i+4*k],1,-1];
GSTOrigXSurvive[{i_,k_}] := Module[{p=Mod[Quotient[i,2]+2*k,3],q},
  q=Mod[Mod[i,2]+2*p,3];
  Boole[k==2]Boole[p==2] + Boole[p==2]Boole[q==2]];
GSTOrigXU = Table[
  Boole[z==GSTOrigXIdx[GSTOrigXShuffle[GSTOrigXCells[[i]]]]],
  {i,12},{z,12}];
GSTOrigXJ = Table[
  GSTOrigXSign[GSTOrigXCells[[i]]]*
   Boole[z==GSTOrigXIdx[GSTOrigXMirror[GSTOrigXCells[[i]]]]],
  {i,12},{z,12}];
GSTOrigXM = DiagonalMatrix[GSTOrigXSurvive/@GSTOrigXCells];
GSTOrigXC = GSTOrigXJ.GSTOrigXM-GSTOrigXM.GSTOrigXJ;
GSTOrigXSeed = Boole[MemberQ[{{0,0},{0,1}},#]]&/@GSTOrigXCells;
GSTOrigXKrylov[t_,v_,n_] := Transpose[NestList[t.#&,v,n-1]];

Module[{birthB,birthC,makeG,a,b,g,detSymbolic,physical,sourceSeed,
  modRanks,smith,check},
birthB=ConstantArray[0,{12,2}];
birthB[[{4,5,6,10},1]]=ConstantArray[-1,4];
birthB[[12,2]]=1;
birthC=ConstantArray[0,{2,12}];
birthC[[1,11]]=1;birthC[[2,12]]=1;
makeG[aa_,bb_]:=ArrayFlatten[
 {{GSTOrigXU+GSTOrigXJ+aa GSTOrigXM+bb GSTOrigXC,birthB},
  {birthC,ConstantArray[0,{2,2}]}}];
g=makeG[a,b];
detSymbolic=Factor[Det[g]];
sourceSeed=Join[GSTOrigXSeed,{0,0}];
physical=Table[
 Module[{F,G,prime,red,smithD},
 F=GSTOrigXU+GSTOrigXJ+GSTOrigXM+bb GSTOrigXC;
 G=makeG[1,bb];
 prime=If[bb==0,2,3];
 red=RowReduce[Mod[F,prime],Modulus->prime];
 smithD=Diagonal[SmithDecomposition[F][[2]]];
 <|"charge"->bb,
   "sourceOriginalCore"->G[[1;;12,1;;12]]==F,
   "SmithDiagonal"->smithD,
   "originalCoreRankModBadPrime"->Length[
      Select[red,#!=ConstantArray[0,12]&]],
   "newWorldChannels"->2,
   "trueIntegralDet"->Det[G],
   "integralEntries"->And@@(IntegerQ/@Flatten[G]),
   "inverseIntegral"->And@@(IntegerQ/@Flatten[Inverse[G]]),
   "14StepOriginalZeroAuxSeedDet"->Det[
      GSTOrigXKrylov[G,sourceSeed,14]],
   "powersAllInvertibleTestN1to6"->And@@Table[
     MatrixPower[G,k].MatrixPower[G,-k]==IdentityMatrix[14],
     {k,1,6}]|>],{bb,{0,1}}];
<|"universalBirthB"->birthB,
 "universalBirthC"->birthC,
 "symbolicDet"->detSymbolic,
 "expectedSymbolicDet"->a+b-2b^2+b^3,
 "allAandBCoefficientsProved"->Together[
     detSymbolic-(a+b-2b^2+b^3)]===0,
 "physicalNavigationStates"->physical,
 "allPassed"->(
  Together[detSymbolic-(a+b-2b^2+b^3)]===0 &&
  Lookup[physical,"trueIntegralDet"]=={1,1} &&
  Lookup[physical,"originalCoreRankModBadPrime"]=={10,10} &&
  Lookup[physical,"14StepOriginalZeroAuxSeedDet"]==
    {-823658646480,14979092529} &&
  And@@Lookup[physical,"inverseIntegral"] &&
  And@@Lookup[physical,"powersAllInvertibleTestN1to6"])|>
]
