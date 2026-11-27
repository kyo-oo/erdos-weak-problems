(* Exact GST polarized-commutant source-birth audit
  Assumption boundary: these are Q-linear operator matrices, not realized
  original-X Chow correspondences or canonical Betti representations.
  Program target: GSS source-birth theorem, all original X.
  Reproduction: execute verbatim in a fresh Wolfram Language kernel.
*)
ClearAll[commData,gstCases,gstPositive,gstGram,gstQAdjoint,
  gstT4,gstSp,gstSplit,gstT2,gstE12,gstE21,gstPA,gstTBlock,gstAll];
commData[ops_List]:=Module[{nn=Length[First[ops]],variables,unknown,eq,coef,ns},
 variables=Flatten[Array[tt,{nn,nn}]];
 unknown=Partition[variables,nn];
 eq=Flatten[Table[unknown.op-op.unknown,{op,ops}]];
 coef=Table[Coefficient[q,v],{q,eq},{v,variables}];
 ns=NullSpace[coef];
 <|"dimension"->Length[ns],"basis"->(Partition[#,nn]&/@ns)|>
];
gstCases=Table[
 Module[{t=DiagonalMatrix[Table[2+10(i-1),{i,n}]],
 s=Table[Boole[Abs[i-j]==1],{i,n},{j,n}]},
 <|"n"->n,"commutantDimension"->commData[{t,s}]["dimension"],
   "tSymmetric"->(t==Transpose[t]),
   "sSymmetric"->(s==Transpose[s])|>],
 {n,1,7}];
gstT2=DiagonalMatrix[{1,0}];
gstE12={{0,1},{0,0}};
gstE21=Transpose[gstE12];
gstT4=DiagonalMatrix[{2,12,22,32}];
gstSp={{0,1,0,0},{1,0,1,0},{0,1,0,1},{0,0,1,0}};
gstSplit={{0,1,0,0},{1,0,0,0},{0,0,0,1},{0,0,1,0}};
gstGram=DiagonalMatrix[{2,3,5,7}];
gstPA=DiagonalMatrix[{1,1,0,0}];
gstTBlock=ArrayFlatten[{
 {{{1,2},{3,4}},ConstantArray[0,{2,2}]},
 {ConstantArray[0,{2,2}],{{5,6},{7,8}}}
}];
gstQAdjoint=Inverse[gstGram].Transpose[gstTBlock].gstGram;
gstPositive=<|
 "Qpositive"->(And@@(Positive /@ Diagonal[gstGram])),
 "rationalOrthogonalProjectorIdempotent"->(gstPA.gstPA==gstPA),
 "rationalOrthogonalProjectorSelfAdjoint"->(Transpose[gstPA].gstGram==gstGram.gstPA),
 "subspaceAndOrthogonalComplementInvariant"->(
   gstPA.gstTBlock==gstTBlock.gstPA &&
   gstPA.gstQAdjoint==gstQAdjoint.gstPA),
 "nonScalarProjector"->(gstPA!=IdentityMatrix[4]&&gstPA!=ConstantArray[0,{4,4}])|>;
gstAll=<|
 "allNCommutantsScalar"->And@@(Lookup[#,"commutantDimension"]==1&/@gstCases),
 "allNSelfAdjoint"->And@@(Lookup[#,"sSymmetric"]&&Lookup[#,"tSymmetric"]&/@gstCases),
 "nCases"->gstCases,
 "nonAdjointCounterexampleScalarCommutant"->(commData[{gstT2,gstE12}]["dimension"]==1),
 "nonAdjointCounterexamplePreservesProperLine"->(gstE12.{1,0}=={0,0}),
 "adjointRestoresNoProperInvariantLine"->(gstE21.{1,0}=={0,1}),
 "connectedFourCommutantDim"->commData[{gstT4,gstSp}]["dimension"],
 "disconnectedFourCommutantDim"->commData[{gstT4,gstSplit}]["dimension"],
 "positiveProjectionChecks"->gstPositive,
 "allPassed"->(
 And@@(Lookup[#,"commutantDimension"]==1&/@gstCases) &&
 And@@Values[gstPositive]&&
 commData[{gstT2,gstE12}]["dimension"]==1 &&
 commData[{gstT4,gstSp}]["dimension"]==1 &&
 commData[{gstT4,gstSplit}]["dimension"]==2)
|>;
Print[gstAll];
gstAll
