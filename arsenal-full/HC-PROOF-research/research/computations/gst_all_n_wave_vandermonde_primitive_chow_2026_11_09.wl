(* GST all-N wave source and canonical primitive Chow-rank tests.
   Exact Wolfram rational arithmetic; finite checks only.
   Mathematical all-N assertion is supplied by the Vandermonde
   product formula and independent wave-hole channel addresses.
   This script tests canonical consecutive channels 0,...,n-1, n=1..10.
   For E_1×...×E_m with nonisogenous CM elliptic curves, test the
   divisor-product primitive projector in codim2, m=4..9. *)
Module[{v, closed, nTests, mTests},
  v[n_] := Table[(2+10*i)^k,{i,0,n-1},{k,0,n-1}];
  closed[n_] := 10^(n*(n-1)/2) *
    Product[Factorial[k],{k,1,n-1}];
  nTests=Table[
    <|"holeCount"->n,"orbitRank"->MatrixRank[v[n]],
      "determinant"->Det[v[n]],
      "equalsVandermonde"->(Det[v[n]]==closed[n])|>,
    {n,1,10}];

  mTests=Table[
    Module[{sing,pairs,high,lmat,amat,bmat,proj,piv={},basis,
      pairing,gram},
      sing=Subsets[Range[m],{1}];
      pairs=Subsets[Range[m],{2}];
      high=Subsets[Range[m],{m-1}];
      lmat=Table[
        Boole[SubsetQ[pairs[[i]],sing[[j]]]],
        {i,Length[pairs]},{j,m}];
      amat=Table[
        Factorial[m-3]*Boole[SubsetQ[high[[i]],pairs[[j]]]],
        {i,m},{j,Length[pairs]}];
      bmat=Table[
        Factorial[m-2]*Boole[SubsetQ[high[[i]],sing[[j]]]],
        {i,m},{j,m}];
      proj=IdentityMatrix[Length[pairs]]-lmat.Inverse[bmat].amat;
      Do[If[MatrixRank[proj[[All,Append[piv,i]]]]>
        Length[piv],AppendTo[piv,i]],{i,Length[pairs]}];
      basis=proj[[All,piv]];
      pairing=Table[
        Factorial[m-4]*Boole[
          Intersection[pairs[[i]],pairs[[j]]]=={}],
        {i,Length[pairs]},{j,Length[pairs]}];
      gram=Transpose[basis].pairing.basis;
      <|"complexDimension"->m,
        "primitiveRank"->MatrixRank[proj],
        "expectedRank"->m*(m-3)/2,
        "rankMatches"->(MatrixRank[proj]==m*(m-3)/2),
        "projectorIdempotent"->(proj.proj==proj),
        "primitiveAnnihilatedByLefschetz"->(
           amat.proj==ConstantArray[0,Dimensions[amat]]),
        "geometricIntersectionPairingNondegenerate"->(
           MatrixRank[gram]==Length[piv])|>
    ],{m,4,9}];

  <|"allFirst10VandermondeTests"->And@@(
       #["equalsVandermonde"]&/@nTests),
    "VandermondeChecks"->nTests,
    "allSixProjectorTests"->And@@Flatten[
      Table[{
        mTests[[i]]["rankMatches"],
        mTests[[i]]["projectorIdempotent"],
        mTests[[i]]["primitiveAnnihilatedByLefschetz"],
        mTests[[i]]["geometricIntersectionPairingNondegenerate"]
      },{i,Length[mTests]}]],
    "primitiveChowSourceRankChecks"->mTests,
    "unboundedRankConstruction"->"Choose m=n+4; then m(m-3)/2≥n"|>
]
