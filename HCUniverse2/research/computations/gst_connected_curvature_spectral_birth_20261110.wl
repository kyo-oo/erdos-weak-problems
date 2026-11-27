(* GST N-wave / noncommutative curvature spectral-birth checks
   Base: HC-PROOF 8d85045980acc09fe6190f7b938bf6234e27f41b
   Domain: exact rational information-quotient matrices; NOT Chow
   realization or a universal Hodge conjecture proof.
   Run in a fresh Wolfram Language kernel. *)
ClearAll[gstOne, gstRuns, gstSplit, gstConn, gstLam, gstT,
  gstCurv, gstSeed, gstRank, gstAll];
gstOne[n_Integer?Positive] := Module[
 {lam, t, b, e, p, wrap, f, mom, wanted, curv, projChecks,
  edgeChecks, split, isCycle, nonzeroSeed},
 lam = Table[2 + 10 (i - 1), {i, n}];
 e = IdentityMatrix[n]; t = DiagonalMatrix[lam];
 b = Table[Boole[Abs[i - j] == 1], {i, n}, {j, n}];
 p = Table[
   Fold[Dot, e, Table[
     (t - lam[[j]] e)/(lam[[i]] - lam[[j]]),
     {j, Delete[Range[n], i]}
    ]], {i, n}];
 projChecks = And @@ Flatten[
   Table[p[[i]].p[[j]] ==
     If[i == j, p[[i]], ConstantArray[0, {n, n}]],
    {i, n}, {j, n}]];
 wrap = p[[n]];
 If[n > 1, Do[wrap = p[[i]].b.wrap, {i, n - 1, 1, -1}]];
 f = If[n == 1, e, Sum[p[[i + 1]].b.p[[i]], {i, 1, n - 1}] + wrap];
 wanted = Table[Boole[i == Mod[j, n] + 1], {i, n}, {j, n}];
 mom = Table[
  UnitVector[n, 1].MatrixPower[f, i + j].UnitVector[n, 1],
  {i, 0, n - 1}, {j, 0, n - 1}];
 curv = t.b - b.t;
 edgeChecks = And @@ Table[
   curv[[i + 1, i]] == 10 && curv[[i, i + 1]] == -10,
  {i, 1, n - 1}];
 <|
  "n" -> n, "projectorIdempotents" -> projChecks,
  "projectorsSumToIdentity" -> Total[p] == e,
  "edgeCurvature10" -> edgeChecks,
  "curvatureRank" -> MatrixRank[curv],
  "fullCyclicFold" -> f == wanted,
  "hankelDet" -> Det[mom],
  "expectedHankelDet" -> (-1)^((n - 1)(n - 2)/2),
  "allPass" -> (projChecks && Total[p] == e && edgeChecks &&
     f == wanted && Det[mom] == (-1)^((n - 1)(n - 2)/2))
 |>
];
gstRuns = Table[gstOne[n], {n, 1, 8}];
gstLam = {2, 12, 22, 32};
gstT = DiagonalMatrix[gstLam];
gstSplit = {{0, 1, 0, 0}, {1, 0, 0, 0},
 {0, 0, 0, 1}, {0, 0, 1, 0}};
gstConn = {{0, 1, 0, 0}, {1, 0, 1, 0},
 {0, 1, 0, 1}, {0, 0, 1, 0}};
gstSeed = UnitVector[4, 1];
gstRank[b_] := MatrixRank[Flatten[
 Table[MatrixPower[b, i].MatrixPower[gstT, j].gstSeed,
  {i, 0, 5}, {j, 0, 3}], 1]];
gstAll = <|
 "allSizesPassed" -> And @@ (Lookup[#, "allPass"] & /@ gstRuns),
 "nCases" -> gstRuns,
 "splitCurvatureDet" -> Det[gstT.gstSplit - gstSplit.gstT],
 "connectedCurvatureDet" -> Det[gstT.gstConn - gstConn.gstT],
 "splitNativeOrbitRank" -> gstRank[gstSplit],
 "connectedNativeOrbitRank" -> gstRank[gstConn],
 "noGoPassed" -> (
  Det[gstT.gstSplit - gstSplit.gstT] != 0 &&
  Det[gstT.gstConn - gstConn.gstT] != 0 &&
  gstRank[gstSplit] == 2 &&
  gstRank[gstConn] == 4)
|>;
Print[gstAll];
gstAll
