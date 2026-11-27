(* GST WAVE I + CM + N-COHOMOLOGY CYCLICITY
   Exact, rational, reproducible computations. No floating point.
   This is NOT a test on arbitrary varieties.
*)
Module[
  {cells, Fold, Mirror, code, phase, midway, source,
   U, J, M, T, seed, K, P, ranks, nshapes, resShift, cycleMass},
  cells=Flatten[Table[{c,d},{c,0,3},{d,0,2}],1];
  Fold[{c_,d_}]:={Quotient[c+4*d,3],Mod[c+4*d,3]};
  Mirror[{c_,d_}]:={3-c,2-d};
  code[{c_,d_}]:=c+4*d;
  phase[s_]:=If[MemberQ[{0,1,3,4,5,9},code[s]],1,-1];
  midway[c_,d_]:=Mod[Quotient[c,2]+2*d,3];
  source[{c_,d_}]:=Module[{mid=midway[c,d]},
    Boole[d==2&&mid==2]+
    Boole[mid==2&&Mod[Mod[c,2]+2*mid,3]==2]];

  U=Table[Boole[cells[[j]]===Fold[cells[[i]]]],
           {i,1,12},{j,1,12}];
  J=Table[phase[cells[[i]]]*
          Boole[cells[[j]]===Mirror[cells[[i]]]],
           {i,1,12},{j,1,12}];
  M=DiagonalMatrix[source/@cells];
  T=U+J+M;
  seed=UnitVector[12,1]+UnitVector[12,2];
  K=Transpose[NestList[T.#&,seed,11]];
  P=CharacteristicPolynomial[T,x];

  ranks=Table[
    Module[{blocks,blockFold,uniformSeed,orbit},
      blocks=Table[T+10*k IdentityMatrix[12],{k,0,n-1}];
      blockFold=BlockDiagonalMatrix[blocks];
      uniformSeed=Flatten[Table[seed,{n}]];
      orbit=Transpose[
        NestList[blockFold.#&,uniformSeed,12*n-1]];
      {n,MatrixRank[orbit],12*n}],
    {n,1,3}];

  cycleMass={
    Total[source/@NestList[Fold,{0,1},4]],
    Total[source/@NestList[Fold,{0,2},4]]};

  <|
    "all12mirrorInvolutive"->AllTrue[cells,Mirror[Mirror[#]]===#&],
    "all12mirrorCommutesFold"->AllTrue[cells,Mirror[Fold[#]]===Fold[Mirror[#]]&],
    "all12period5"->AllTrue[cells,Nest[Fold,#,5]===#&],
    "J2MinusIdentity"->(J.J===-IdentityMatrix[12]),
    "UJCommutation"->(U.J===J.U),
    "waveCurrentSourceTable"->Table[{cells[[i]],source[cells[[i]]]},{i,1,12}],
    "pairedFiveCycleMass"->cycleMass,
    "waveSourceCMCurvatureRank"->MatrixRank[J.M-M.J],
    "foldOnlyCMOrbitRank"->MatrixRank[
       Transpose[Flatten[
         Table[{MatrixPower[U,k].seed,J.MatrixPower[U,k].seed},
           {k,0,4}],1]]],
    "unifiedTInfinityNorm"->Max[Total/@Abs[T]],
    "singleFoldKrylovRank"->MatrixRank[K],
    "singleFoldKrylovDet"->Det[K],
    "singleFoldCharPolynomial"->Factor[P],
    "nHoleSampleRanks"->ranks,
    "shift10GCD1"->(PolynomialGCD[P,P/.x->x-10]===1),
    "spectralSeparationBound"->10>2 Max[Total/@Abs[T]]
  |>
]