(* Exact GST Wave I/CM single-fold => primitive Chow sector on a
   sixfold X=E1×...×E6. The variables in the degree-two divisor
   subring are d_i, d_i^2=0; the integral of d_1...d_6 is one.
   L = cup (sum d_i), L^3 sends codim2->codim5,
   L^4 sends codim1->codim5.
   P_prim = identity - L (L^4)^{-1} L^3 on codim2.
   No floating point. Domain: divisor-product algebraic classes,
   not all rational Hodge classes of arbitrary sixfolds. *)
Module[{m=6,singles,pairs,fives,lmat,amat,bmat,proj,picked,oneHoleT,
  states,fold,mirror,sign,mid,mass,umat,jmat,mmat,seed,kry,
  primitiveWaveOrbit,projRanks},
  singles=Subsets[Range[m],{1}];
  pairs=Subsets[Range[m],{2}];
  fives=Subsets[Range[m],{m-1}];
  lmat=Table[If[SubsetQ[pairs[[i]],singles[[j]]],1,0],
    {i,Length[pairs]},{j,Length[singles]}];
  amat=Table[If[SubsetQ[fives[[i]],pairs[[j]]],6,0],
    {i,Length[fives]},{j,Length[pairs]}];
  bmat=Table[If[SubsetQ[fives[[i]],singles[[j]]],24,0],
    {i,Length[fives]},{j,Length[singles]}];
  proj=IdentityMatrix[Length[pairs]]-lmat.Inverse[bmat].amat;
  picked=Transpose[Take[IdentityMatrix[Length[pairs]],12]];
  states=Flatten[Table[{c,d},{c,0,3},{d,0,2}],1];
  fold[{c_,d_}]:={Quotient[c+4*d,3],Mod[c+4*d,3]};
  mirror[{c_,d_}]:={3-c,2-d};
  sign[{c_,d_}]:=If[MemberQ[{0,1,3,4,5,9},c+4d],1,-1];
  mid[c_,d_]:=Mod[Quotient[c,2]+2d,3];
  mass[{c_,d_}]:=Boole[d==2&&mid[c,d]==2]+
    Boole[mid[c,d]==2&&Mod[Mod[c,2]+2mid[c,d],3]==2];
  umat=Table[Boole[states[[j]]==fold[states[[i]]]],{i,12},{j,12}];
  jmat=Table[sign[states[[i]]]*
    Boole[states[[j]]==mirror[states[[i]]]],{i,12},{j,12}];
  mmat=DiagonalMatrix[mass/@states];
  oneHoleT=umat+jmat+mmat;
  seed=UnitVector[12,1]+UnitVector[12,2];
  kry=Transpose[NestList[oneHoleT.#&,seed,11]];
  primitiveWaveOrbit=proj.picked.kry;
  projRanks=Table[MatrixRank[Take[Transpose[primitiveWaveOrbit],k]],
    {k,1,12}];
  <|
    "complexDimension"->m,
    "allCodimensionTwoDivisorProducts"->Length[pairs],
    "hardLefschetzCoefficientMatrixDet"->Det[bmat],
    "primitiveProjectorRank"->MatrixRank[proj],
    "primitiveProjectorSquareIdentity"->(proj.proj==proj),
    "primitiveKernelL3Zero"->(amat.proj==
      ConstantArray[0,Dimensions[amat]]),
    "selectedTwelveProjectedRank"->MatrixRank[proj.picked],
    "GSTSingleFoldDet"->Det[kry],
    "projectedGSTOrbitRank"->MatrixRank[primitiveWaveOrbit],
    "projectedGSTOrbitRankByFirstK"->projRanks,
    "genuinePrimitiveCycleClassNonzero"->(primitiveWaveOrbit!=
      ConstantArray[0,Dimensions[primitiveWaveOrbit]])
  |>
]