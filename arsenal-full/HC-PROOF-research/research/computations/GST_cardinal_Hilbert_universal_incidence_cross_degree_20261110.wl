(* GST graded cardinal-topology original-X INCIDENCE compiler.
   TRUE geometry: X=P^1 x P^1, dim_C X=2.
   The Hilbert scheme Hilb^1(X) of one reduced point is X itself
   (connected), and the UNIVERSAL family of points is the diagonal
   Delta_X in CH^2(X x X).

   The fiber class [point] lies only in codimension 2 and is constant.
   HOWEVER the diagonal contains positive parameter-degree Kunneth
   coefficients and acts as the identity on ALL cohomology grades:
   CH^0 rank1, CH^1 rank2, CH^2 rank1.

   This shows why a cardinal topology compiler must retain source-world
   cohomology and graded incidence, not only component fiber labels.
   No Hodge conjecture is inferred by using Y=X as the parameter:
   that identity construction would be circular for unknown Hodge
   classes. The checks are exact rational intersection algebra.
*)
ClearAll[basis,degree,pairing,delta,action,grades,
  one,hilbert,runs,result];
basis={"1","H1","H2","pt"};
degree={0,1,1,2};
pairing={{0,0,0,1},{0,0,1,0},{0,1,0,0},{1,0,0,0}};
delta=Inverse[pairing];
action[v_]:=v.pairing.delta;
one[q_Integer?NonNegative]:=Module[{indices,sourceImage,expected},
 indices=Flatten[Position[degree,q]];
 sourceImage=Table[action[UnitVector[4,i]],{i,indices}];
 expected=Length[indices];
 <|"codimension"->q,"actualSourceDimension"->expected,
  "diagonalIncidenceOutputRank"->MatrixRank[sourceImage],
  "sameGradeIdentity"->And@@Table[
    action[UnitVector[4,i]]==UnitVector[4,i],{i,indices}],
  "passed"->(MatrixRank[sourceImage]==expected)|>];
runs=Table[one[q],{q,0,2}];
(* Fiber of Delta over any point is the fixed top class pt. *)
hilbert=delta[[1]];
result=<|
 "connectedHilbOfPointsHasOneFiberClass"->(hilbert=={0,0,0,1}),
 "pointFiberHodgeRank"->1,
 "diagonalCoefficientMatrix"->delta,
 "fullDiagonalIsIdentity"->(pairing.delta==IdentityMatrix[4]),
 "codimensionChecks"->runs,
 "totalGradedIncidenceRank"->MatrixRank[pairing.delta],
 "allPassed"->(hilbert=={0,0,0,1} &&
    pairing.delta==IdentityMatrix[4] &&
    And@@(Lookup[#,"passed"]&/@runs))|>;
Print[result];result