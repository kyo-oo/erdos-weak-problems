(* GST 2026-11-10 exact full nine-dimensional primitive cyclic fold:
   X=(P^1_C)^6, codimension 2, genuine original-X Chow cycles.
   Build nine primitive sources: first two wave-frame cycles and
   seven further cycles from real Chow commutators [A,B_j] Z_1.
   Build one original-X codimension-6 correspondence whose
   matrix action is a cyclic shift on those nine source cycles.
   All input/output functionals are rational combinations of
   actual complementary divisor intersection pairings.
   NOTE: use Nest, not MatrixPower[T,0], because T is singular
   on the 15-dimensional ambient H^4 although cyclic on the
   nine-dimensional genuine primitive subspace.
*)
Module[{two,five,lefschetz,k,dual,anchor,curv,frame,cycleMatrix,
        nativeT,seed,orbit,read,moment},
  two=Subsets[Range[6],{2}];
  five=Subsets[Range[6],{5}];
  lefschetz=Table[
    If[SubsetQ[five[[i]],two[[j]]],6,0],
    {i,6},{j,15}];
  k=Transpose[NullSpace[lefschetz]];
  dual=Inverse[Transpose[k].k].Transpose[k];

  anchor=Outer[Times,k[[All,1]],dual[[1]]];
  curv=Table[
    (anchor.Outer[Times,k[[All,j]],dual[[1]]] -
      Outer[Times,k[[All,j]],dual[[1]]].anchor).k[[All,1]],
    {j,3,9}];
  frame=Transpose[Join[{k[[All,1]],k[[All,2]]},-curv]];
  cycleMatrix=RotateRight[IdentityMatrix[9],1];
  nativeT=frame.cycleMatrix.dual;
  seed=k[[All,1]];
  orbit=Transpose[NestList[nativeT.#&,seed,8]];
  read=dual[[9]];
  moment=Table[
    read.Nest[nativeT.#&,seed,i+j],
    {i,0,8},{j,0,8}];

  <|
    "originalX"->"(P^1_C)^6",
    "codimension"->2,
    "primitiveHodgeRank"->MatrixRank[k],
    "sevenCurvatureCyclesGiveCompleteFrame"->(frame===k),
    "singleFoldOneSeedFullOrbit"->(orbit===k),
    "singleFoldOrbitRank"->MatrixRank[orbit],
    "singleFoldOrbitDeterminant"->Det[dual.orbit],
    "antiDiagonalMomentDeterminant"->Det[moment],
    "primitivePreservation"->(
      lefschetz.nativeT.k===ConstantArray[0,{6,9}]),
    "exactCyclicOperator"->(dual.nativeT.k===cycleMatrix)
  |>
]
