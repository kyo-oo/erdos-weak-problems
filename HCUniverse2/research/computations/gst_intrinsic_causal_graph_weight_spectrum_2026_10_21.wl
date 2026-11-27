(* Actual original-X point-pinch graph topology: exact finite test.
   Supports the analytical derivation in GST_intrinsic_causal_dimension_topology_fold_weight_birth_2026_10_21.tex.
   Tests the combinatorial signed boundary matrix, not mixed Hodge realization. *)
ClearAll[triangleBoundary,triangleFace,unfilledLaplacian,filledLaplacian,loopData,n];
triangleBoundary={{-1,0,1},{1,-1,0},{0,1,-1}};
triangleFace={{1},{1},{1}};
unfilledLaplacian=Transpose[triangleBoundary].triangleBoundary;
filledLaplacian=unfilledLaplacian+triangleFace.Transpose[triangleFace];
loopData=Table[{n,MatrixRank[ConstantArray[0,{1,n}]],n-MatrixRank[ConstantArray[0,{1,n}]]},{n,1,12}];
result=<|
 "bouquetIndependentLoopsN0to12"->loopData,
 "triangleD1D2Zero"->(triangleBoundary.triangleFace==ConstantArray[0,{3,1}]),
 "triangleGraphFirstBetti"->(3-MatrixRank[triangleBoundary]),
 "triangleGraphLaplacianSpectrum"->Sort[Eigenvalues[unfilledLaplacian]],
 "filledTriangleFirstBetti"->(3-MatrixRank[triangleBoundary]-MatrixRank[triangleFace]),
 "filledTriangleLaplacianSpectrum"->Sort[Eigenvalues[filledLaplacian]]
 |>;
If[!TrueQ[result["triangleD1D2Zero"]]||
 result["triangleGraphFirstBetti"]=!=1||
 result["filledTriangleFirstBetti"]=!=0||
 result["triangleGraphLaplacianSpectrum"]=!={0,3,3}||
 result["filledTriangleLaplacianSpectrum"]=!={3,3,3},
 Print["FAIL"];Abort[]];
Print[result];
Print["PASS exact graph boundary and spectrum assertions; MHS proof independent"];
