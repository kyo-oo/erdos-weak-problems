(* GST seven-axis wave + CM combined single-fold Krylov experiment
   2026-11-09, original Q-arithmetic at finite Hodge-sector model scale.
   Exact rational arithmetic; Wolfram Language, stateless execution.
   This experiment tests a REPRESENTATION, not a Chow correspondence.
*)
Module[{c,zero,i,s,j,t,seed,krylov,poly,proj,f,states,perm,p,ambient,seed9,krylov9},
c=CompanionMatrix[{1,1,1,1}];
zero=ConstantArray[0,{4,4}];
i=IdentityMatrix[4];
s=ArrayFlatten[{{c,zero},{zero,c}}];
j=ArrayFlatten[{{zero,-i},{i,zero}}];
t=s+j;
seed=UnitVector[8,1];
krylov=Transpose[Table[Nest[t.#&,seed,r],{r,0,7}]];
poly=CharacteristicPolynomial[t,x];

f[{carry_,digit_}]:={Quotient[carry+4*digit,3],
                       Mod[carry+4*digit,3]};
states=Flatten[Table[{carry,digit},
                     {carry,0,3},{digit,0,2}],1];
perm=Flatten[Position[states,#]&/@(f/@states)];
p=PermutationMatrix[perm];
proj=Total[Table[MatrixPower[p,r],{r,0,4}]]/5;

ambient=ArrayFlatten[{{t,ConstantArray[0,{8,1}]},
                       {ConstantArray[0,{1,8}],{{0}}}}];
seed9=Append[seed,0];
krylov9=Transpose[Table[Nest[ambient.#&,seed9,r],{r,0,8}]];
<|
  "permutationOrderFive"->(MatrixPower[p,5]==IdentityMatrix[12]),
  "permutationCharacteristic"->Factor[CharacteristicPolynomial[p,x]],
  "fiveWaveFixedRank"->MatrixRank[proj],
  "fiveWaveMovingRank"->MatrixRank[IdentityMatrix[12]-proj],
  "CMStructureJ2"->(j.j==-IdentityMatrix[8]),
  "waveS5"->(MatrixPower[s,5]==IdentityMatrix[8]),
  "waveCMCommute"->(s.j==j.s),
  "singleFoldPolynomial"->poly,
  "singleFoldIrreducibleQ"->IrreduciblePolynomialQ[poly],
  "singleFoldSeedOrbitDeterminant"->Det[krylov],
  "singleFoldSeedOrbitRank"->MatrixRank[krylov],
  "extendedNineDimensionalOrbitRank"->MatrixRank[krylov9],
  "extendedNineDimensionalMissingRow"->krylov9[[-1]],
  "adjoinNinthIndependentVector"->MatrixRank[
     Transpose[Append[Transpose[krylov9],UnitVector[9,9]]]]
|>
]
