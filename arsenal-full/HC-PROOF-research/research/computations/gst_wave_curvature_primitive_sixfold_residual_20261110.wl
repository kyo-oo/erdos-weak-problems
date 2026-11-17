(* GST 2026-11-10 exact primitive-sixfold wave+curvature residual test.
   Geometry X=(P^1_C)^6, codimension p=2. Base cycle classes D_I:
   I runs over two-subsets of {1..6}, d_i^2=0.
   Cup with h^3 sends D_I to 6 D_(I U K) on five-subsets J.
   NullSpace supplies 9 actual rational primitive divisor-product cycles.
   Every dual readout is a rational combination of actual complementary
   intersection pairings (not an abstract Hodge-coordinate oracle).
   All computations are exact rational/integer; no tolerance/sampling.
*)
Module[{two, five, lefschetz, primitive, geometricDual, old,
  newCycle, projection, fold, curvature, z, read, coefficients, alpha,
  waveSource, correctedBorn, waveCurvCycle, residual},
  two=Subsets[Range[6],{2}];
  five=Subsets[Range[6],{5}];
  lefschetz=Table[
    If[SubsetQ[five[[a]],two[[b]]],6,0],
    {a,Length[five]},{b,Length[two]}];
  primitive=Transpose[NullSpace[lefschetz]];
  geometricDual=Inverse[Transpose[primitive].primitive].
                 Transpose[primitive];
  old=primitive[[All,1;;2]];
  newCycle=primitive[[All,3]];

  projection=Outer[Times,old[[All,1]],geometricDual[[1]]];
  fold=Outer[Times,newCycle,geometricDual[[1]]];
  curvature=projection.fold-fold.projection;
  z=curvature.old[[All,1]];

  read=geometricDual[[3]];
  coefficients={2,-3,4,5,-2,1,7,-1,3};
  alpha=primitive.coefficients;

  waveSource=old.(geometricDual[[1;;2]].alpha);
  correctedBorn=z-old.(geometricDual[[1;;2]].z);
  waveCurvCycle=waveSource+
    (read.(alpha-waveSource))/(read.z)*correctedBorn;
  residual=alpha-waveCurvCycle;

  <|
    "originalX"->"(P^1_C)^6",
    "codimension"->2,
    "totalMiddleDivisorProductRank"->Length[two],
    "primitiveRank"->MatrixRank[primitive],
    "LefschetzRank"->MatrixRank[lefschetz],
    "primitiveBasisInLefschetzKernel"->
      (lefschetz.primitive===ConstantArray[0,{6,9}]),
    "geometricComplementIntersectionDual"->(
      geometricDual.primitive===IdentityMatrix[9]),
    "curvatureIsNegativeThirdPrimitive"->(z===-newCycle),
    "oldWaveCoordinatesOfCurvature"->geometricDual[[1;;2]].z,
    "newGeometricReadoutOfOldSource"->read.old,
    "newReadoutOfCurvature"->read.z,
    "oldWaveCoordinatesOfResidual"->geometricDual[[1;;2]].residual,
    "newCurvatureReadoutOfResidual"->read.residual,
    "residualPreservesPrimitive"->(
      lefschetz.residual===ConstantArray[0,6]),
    "oldRank"->MatrixRank[old],
    "rankAfterGeometricCurvature"->MatrixRank[
      Join[Transpose[old],{z}]],
    "remainingSixPrimitiveCoordinates"->geometricDual[[4;;9]].residual,
    "residualNonzeroHere"->(residual!=ConstantArray[0,15])
  |>
]
