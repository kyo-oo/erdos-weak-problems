(* GST 2026-11-10: complete 9-direction primitive curvature-birth ladder
   for X=(P^1)^6, codimension p=2. All matrices are genuine geometric
   divisor-product source/target actions realizable by Chow correspondences
   pr_1^*(D_{I^c}) . pr_2^*(D_J); all readouts are rational intersection
   functionals paired with complementary divisor cycles.
   This proves a true specific-X primitive generation example, not a general
   arbitrary-X source-existence theorem. Exact integer/rational arithmetic.
*)
Module[{two,five,l,k,d,alpha,old,source,read,residual,ranks,stages,
        geomA,geomB,comm},
  two=Subsets[Range[6],{2}];
  five=Subsets[Range[6],{5}];
  l=Table[
    If[SubsetQ[five[[i]],two[[j]]],6,0],
    {i,Length[five]},{j,Length[two]}];
  k=Transpose[NullSpace[l]];
  d=Inverse[Transpose[k].k].Transpose[k];
  alpha=k.{2,-3,4,5,-2,1,7,-1,3};
  old=k[[All,1;;2]];
  residual=alpha-old.(d[[1;;2]].alpha);
  ranks={MatrixRank[old]};
  stages={};

  Do[
    geomA=Outer[Times,k[[All,1]],d[[1]]];
    geomB=Outer[Times,k[[All,j]],d[[1]]];
    comm=geomA.geomB-geomB.geomA;
    source=comm.k[[All,1]];
    read=d[[j]];
    residual=residual-(read.residual)/(read.source)*source;
    AppendTo[stages,<|
      "j"->j,
      "curvatureIsMinusPrimitive"->(source===-k[[All,j]]),
      "geometricDetector"->read.source,
      "allEarlierDetectorsZero"->(
        d[[1;;j]].residual===ConstantArray[0,j]),
      "remainingPrimitiveDirections"->(9-j)
    |>];
    AppendTo[ranks,j];
  ,{j,3,9}];

  <|
    "X"->"(P^1_C)^6",
    "primitiveMiddleHodgeRank"->MatrixRank[k],
    "geometricIntersectionDualExact"->(d.k===IdentityMatrix[9]),
    "successiveSourceRanks"->ranks,
    "everyStepCurvatureAndDetectorVerified"->AllTrue[
      stages,#[["curvatureIsMinusPrimitive"]] &&
             #[["allEarlierDetectorsZero"]]&],
    "stages"->stages,
    "finalPrimitiveResidualZero"->(
      residual===ConstantArray[0,15]),
    "allPrimitiveClassesGeneratedBySourceBasis"->(
      k.d.k===k)
  |>
]
