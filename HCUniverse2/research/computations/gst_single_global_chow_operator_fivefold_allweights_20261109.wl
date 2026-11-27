(* GST SINGLE GLOBAL algebraic correspondence on X=(P^1_C)^5,
   all Hodge weights p=0,..,5. Exact integer/rational Wolfram.
   Source geometric formula:
      Gamma = sum_{p=0}^5 sum_{|I|=|J|=p} M_p[J,I] *
                  pr1^*(D_(I complement)) . pr2^*(D_J).
   The true Chow intersection pairing
      integral_X D_I D_(J complement) = KroneckerDelta[I,J]
   turns each term into a matrix unit of H^(2p). The global
   operator has no off-degree action and odd cohomology is zero.
*)
Module[{c,z4,i4,s8,j8,i2,j2,z82,z28,t10,p5,
        blocks,seeds,krylov,global,index,subsets,pairings},
 c=CompanionMatrix[{1,1,1,1}];
 z4=ConstantArray[0,{4,4}];
 i4=IdentityMatrix[4];
 s8=ArrayFlatten[{{c,z4},{z4,c}}];
 j8=ArrayFlatten[{{z4,-i4},{i4,z4}}];
 j2={{0,-1},{1,0}};
 i2=IdentityMatrix[2];
 z82=ConstantArray[0,{8,2}];
 z28=ConstantArray[0,{2,8}];
 t10=ArrayFlatten[{{s8+j8,z82},{z28,i2+j2}}];

 p5=ConstantArray[0,{5,5}];
 Do[p5[[Mod[k,5]+1,k]]=1,{k,1,5}];
 blocks={IdentityMatrix[1],p5,t10,t10,p5,IdentityMatrix[1]};
 seeds={UnitVector[1,1],UnitVector[5,1],
        UnitVector[10,1]+UnitVector[10,9],
        UnitVector[10,1]+UnitVector[10,9],
        UnitVector[5,1],UnitVector[1,1]};
 krylov=Table[Transpose[
     Table[Nest[blocks[[p]].#&,seeds[[p]],k],
       {k,0,Length[seeds[[p]]]-1}]],{p,1,6}];

 global=ArrayFlatten[Table[
    If[p==q,blocks[[p]],
      ConstantArray[0,{Length[blocks[[p]]],Length[blocks[[q]]]}]],
    {p,1,6},{q,1,6}]];

 index=Range[5];
 subsets=Table[Subsets[index,{p}],{p,0,5}];
 pairings=Table[
    Table[Boole[Intersection[subsets[[p+1,i]],
                   Complement[index,subsets[[p+1,j]]]]=={}],
      {i,1,Length[subsets[[p+1]]]},{j,1,Length[subsets[[p+1]]]}],
    {p,0,5}];

 <|
  "X"->"(P^1_C)^5",
  "HodgeWeights"->Range[0,5],
  "ActualChowHodgeRanks"->(Length/@subsets),
  "AllSixGeometricComplementPairingsIdentity"->And@@Table[
      pairings[[p]]==IdentityMatrix[Length[subsets[[p]]]],{p,1,6}],
  "OneSeedKrylovDetPerWeight"->(Det/@krylov),
  "OneSeedKrylovRankPerWeight"->(MatrixRank/@krylov),
  "OneOrbitSpansEveryWeight"->And@@Table[
      MatrixRank[krylov[[p]]]==Length[subsets[[p]]],{p,1,6}],
  "GlobalCorrespondenceDimension"->Dimensions[global],
  "GlobalCorrespondenceDet"->Det[global],
  "GlobalCorrespondenceBettiRank"->MatrixRank[global],
  "GlobalCorrespondenceInvertibleOnRationalBetti"->
      (Det[global]!=0)
 |>
]
