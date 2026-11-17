(* NEW 2026-11-09 mathbox route: full finite-wave-to-genuine-Chow
   cyclic completion on X=E1x...xE6 in codimension two.
   The full 12-dimensional information/CM/Wave-I fold does NOT descend
   through a 9-rank map (no invariant 3-dimensional kernel exists).
   The correct construction extracts nine algebraic primitive wave cycles,
   constructs their actual intersection-dual rational functionals,
   and synthesizes a NEW cycle operator via CH^6(XxX) matrix units.
   An exact 9x9 antidiagonal moment matrix has determinant 1.
   All calculations rational, no float; no preselected target alpha.
   The proof covers the 9-dimensional divisor-product primitive sector,
   not an unspecified full primitive Hodge fiber. *)
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
  primitiveWaveOrbit,projRanks,prefix,pivots,selector,leftInverse,cyclic9,nativeT,geometricDetector,h9,seedCycle,foldPoly,uv,cohom9,kerTest,x},
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
  (* Rank-9 primitive wave prefix: genuinely algebraic cycles in the
     divisor-product Chow sector. Each column is a rational combination
     of D_I, I a two-element subset of {1,...,6}. *)
  prefix=primitiveWaveOrbit[[All,1;;9]];
  pivots={};
  Do[If[MatrixRank[prefix[[Append[pivots,i],All]]]>Length[pivots],
       AppendTo[pivots,i]],{i,1,15}];
  selector=UnitVector[15,#]&/@pivots;
  leftInverse=Inverse[prefix[[pivots,All]]].selector;
  (* Geometric rational correspondence matrix = a linear combination
     of the genuine CH^6(X x X) matrix units
     Gamma_{J,I}=pr1^*D_{I^c} pr2^*D_J. *)
  cyclic9=Table[Boole[r==Mod[c,9]+1],{r,1,9},{c,1,9}];
  nativeT=prefix.cyclic9.leftInverse;
  geometricDetector=leftInverse[[9]];
  seedCycle=prefix[[All,1]];
  (* Avoid Mathematica's MatrixPower[singular,0] ambiguity.
     Nest has the correct identity at zero without inverting anything. *)
  h9=Table[geometricDetector.Nest[nativeT.#&,seedCycle,i+j],
           {i,0,8},{j,0,8}];
  (* The original wave T cannot descend through the candidate Q:
     checking that kernel Q is stable is equivalent to stacked rank. *)
  kerTest=AllTrue[NullSpace[proj.picked],
      proj.picked.oneHoleT.#==ConstantArray[0,15]&];
  x=Unique["x"];
  foldPoly=FactorList[CharacteristicPolynomial[oneHoleT,x]];
  cohom9=AllTrue[Rest[foldPoly],IrreduciblePolynomialQ[#[[1]]]&];

  projRanks=Table[MatrixRank[Take[Transpose[primitiveWaveOrbit],k]],
    {k,1,12}];
  <|
    "oldCandidateQRank"->MatrixRank[proj.picked],
    "oldCandidateQKernelDimension"->Length[NullSpace[proj.picked]],
    "oldCandidateKernelStable"->kerTest,
    "rankStackedQ_QT"->MatrixRank[Join[proj.picked,proj.picked.oneHoleT]],
    "waveCharacteristicFactorDegrees"->(Exponent[#[[1]],x]&/@Rest[foldPoly]),
    "waveCharacteristicFactorMultiplicities"->(#[[2]]&/@Rest[foldPoly]),
    "waveCharacteristicFactorsIrreducible"->cohom9,
    "nativePrimitivePrefixRank"->MatrixRank[prefix],
    "dualPivotRows"->pivots,
    "nativeDualExactlyIdentity"->(leftInverse.prefix==IdentityMatrix[9]),
    "nativeChowCorrespondenceRank"->MatrixRank[nativeT],
    "nativeChowCorrespondenceRational"->AllTrue[Flatten[nativeT],Element[#,Rationals]&],
    "nativeFoldIntertwinesNinePrefix"->(nativeT.prefix==prefix.cyclic9),
    "nativeFoldPrimitive"->(amat.nativeT==ConstantArray[0,{6,15}]),
    "nativeNinefoldSeedReturn"->(Nest[nativeT.#&,seedCycle,9]==seedCycle),
    "geometricMomentMatrixAntiDiagonal"->(h9==Reverse[IdentityMatrix[9]]),
    "geometricMomentDeterminant"->Det[h9],
    "nonzeroChowCorrespondenceCoefficients"->Count[Flatten[nativeT],Except[0]],
    "maxChowDenominator"->Max[Denominator/@Flatten[nativeT]],
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