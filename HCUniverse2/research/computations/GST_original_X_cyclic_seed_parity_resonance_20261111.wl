(* Exact GST original-X geometry seed check.
   On each of the genuinely constructed divisor/curve Hodge fibers
   the Chow correspondence acts by a cyclic permutation matrix T_r
   on an actual algebraic basis of r rational Hodge classes.

   The original user's Z0 + NZ0 seed can lose rank at even r.
   Z0 + 2 NZ0 always has a full cyclic orbit. The proof is uniform:
     det(I+lambda T_r)=1-(-lambda)^r,  T_r^r=I.
   This file tests a finite discriminating range; the hand proof
   in the original-X Chow correspondence TeX is all-rank exact. *)

ClearAll[GSTChowCyclicMatrix,GSTChowKrylov,GSTChowSeedRow];
GSTChowCyclicMatrix[n_Integer?Positive] :=
  RotateRight[IdentityMatrix[n],{0,1}];
GSTChowKrylov[t_,v_,n_Integer?Positive] :=
  Transpose[NestList[t.#&,v,n-1]];
GSTChowSeedRow[n_Integer?Positive] :=
  Module[{t=GSTChowCyclicMatrix[n],v=UnitVector[n,1],
    old,k1,k2,rank1,ratio1,ratio2},
    old=Det[GSTChowKrylov[t,v,n]];
    k1=GSTChowKrylov[t,(IdentityMatrix[n]+t).v,n];
    k2=GSTChowKrylov[t,(IdentityMatrix[n]+2*t).v,n];
    rank1=MatrixRank[k1];
    ratio1=1-(-1)^n;ratio2=1-(-2)^n;
    <|"rank"->n,"cyclicPermutationOrder"->TrueQ[MatrixPower[t,n]===IdentityMatrix[n]],
      "baseKrylovDet"->old,
      "doubleBirthDet"->Det[k1],
      "doubleBirthRank"->rank1,
      "repairedBirthDet"->Det[k2],
      "originalDeterminantFormula"->TrueQ[Det[k1]===old*ratio1],
      "repairedDeterminantFormula"->TrueQ[Det[k2]===old*ratio2],
      "originalRankParityExact"->TrueQ[rank1==If[EvenQ[n],n-1,n]],
      "repairedNonzero"->(Det[k2]!=0)|>
  ];

Module[{results,all},
  results=Table[GSTChowSeedRow[n],{n,1,12}];
  all=And@@Flatten[{
    Lookup[results,"cyclicPermutationOrder"],
    Lookup[results,"originalDeterminantFormula"],
    Lookup[results,"repairedDeterminantFormula"],
    Lookup[results,"originalRankParityExact"],
    Lookup[results,"repairedNonzero"]}];
  <|"source"->"Original-X actual Chow cyclic matrix from divisor/curve Gram-dual construction",
    "checkedRanks"->Range[12],"results"->results,
    "allPassed"->all|>
]
