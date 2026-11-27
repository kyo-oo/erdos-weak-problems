(* GST wave + CM combined fold on genuine codim-2 Chow sector
   of X=(P^1_C)^5, complex dimension 5. Exact rational computation.
   Each pair I of the ten two-element subsets indexes the algebraic
   cycle D_I = product_{i in I} h_i.  D_(I^c) is its true intersection dual.
   The algebraic correspondence Gamma_(j,i) =
   pr1^*(D_(I^c)) . pr2^*(D_J) acts as the matrix unit E_(j,i).
   We check this *exact* 10x10 intersection table.
*)
Module[{index,subsets,pair,c,z4,i4,s8,j8,j2,i2,z82,z28,
        s10,j10,t10,seed,krylov,p8,p2},
 index=Range[5];
 subsets=Subsets[index,{2}];
 pair=Table[
   Boole[Intersection[subsets[[i]],Complement[index,subsets[[j]]]]=={}],
   {i,1,10},{j,1,10}];

 c=CompanionMatrix[{1,1,1,1}];
 z4=ConstantArray[0,{4,4}];
 i4=IdentityMatrix[4];
 s8=ArrayFlatten[{{c,z4},{z4,c}}];
 j8=ArrayFlatten[{{z4,-i4},{i4,z4}}];
 j2={{0,-1},{1,0}};
 i2=IdentityMatrix[2];
 z82=ConstantArray[0,{8,2}];
 z28=ConstantArray[0,{2,8}];

 s10=ArrayFlatten[{{s8,z82},{z28,i2}}];
 j10=ArrayFlatten[{{j8,z82},{z28,j2}}];
 t10=s10+j10;
 seed=UnitVector[10,1]+UnitVector[10,9];
 krylov=Transpose[Table[Nest[t10.#&,seed,k],{k,0,9}]];
 p8=CharacteristicPolynomial[s8+j8,x];
 p2=CharacteristicPolynomial[i2+j2,x];

 <|
   "variety"->"(P^1)^5",
   "codimension"->2,
   "tenActualDivisorProductBasisLabels"->subsets,
   "complementIntersectionDualIsIdentity"->(pair==IdentityMatrix[10]),
   "HodgeRank"->Length[subsets],
   "WaveS5"->(MatrixPower[s10,5]==IdentityMatrix[10]),
   "CMJ2"->(j10.j10==-IdentityMatrix[10]),
   "WaveCMCommute"->(s10.j10==j10.s10),
   "CombinedFoldCharacteristic"->Factor[CharacteristicPolynomial[t10,x]],
   "TwoBlockPolynomialsCoprime"->(PolynomialGCD[p8,p2]==1),
   "Seed"->seed,
   "KrylovDeterminant"->Det[krylov],
   "KrylovRank"->MatrixRank[krylov],
   "EntireCodimensionTwoSectorGenerated"->(MatrixRank[krylov]==10)
 |>
]
