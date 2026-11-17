(* Exact Wolfram verification, 2026-11-10.
   Mathematical domain: CH-correspondence projector formulas reduce to
   rational linear algebra. Finite tests do not prove universal Chow
   compatibility; see the projection-formula proof in the companion PDF.
*)
ClearAll[exactPower, gram, ph, pk, curv, fold, seed, krylov, detector, hankel, iteration, cases, checks, result];
exactPower[n_Integer?NonNegative] := Module[{p = DiagonalMatrix[{1, 0, 0}], id = IdentityMatrix[3]},
  MatrixPower[id + p, n] == id + (2^n - 1) p];
iteration = Module[{p = DiagonalMatrix[{1, 0, 0}], id = IdentityMatrix[3], z = {1, 1, 1}, n},
  n = id + p;
  <|"userZ" -> z + n.z,
    "nativeOnUserZ" -> n.(z + n.z),
    "zerothIterate" -> MatrixPower[n, 0].z,
    "orbitRank" -> MatrixRank[Transpose[Table[MatrixPower[n, j].z, {j, 0, 2}]]],
    "orbitDeterminant" -> Det[Transpose[Table[MatrixPower[n, j].z, {j, 0, 2}]]],
    "allPowers0To8" -> And @@ Table[exactPower[j], {j, 0, 8}],
    "cumulative0To8" -> And @@ Table[
      Sum[MatrixPower[n, j], {j, 0, k}] ==
        (k + 1) (id - p) + (2^(k + 1) - 1) p,
      {k, 0, 8}]|>];
(* Intersection form on X=P1 x P1, basis H1,H2. *)
gram = {{0, 1}, {1, 0}};
ph = Outer[Times, {1, 1}, (gram.{1, 1})/({1, 1}.gram.{1, 1})];
pk = Outer[Times, {1, 2}, (gram.{1, 2})/({1, 2}.gram.{1, 2})];
curv = ph.pk - pk.ph;
fold = IdentityMatrix[2] + ph + pk;
seed = {1, 1};
krylov = Transpose[{seed, fold.seed}];
detector = LinearSolve[Transpose[krylov], {0, 1}];
hankel = Table[detector.MatrixPower[fold, i + j].seed, {i, 0, 1}, {j, 0, 1}];
checks = <|
  "projectorsIdempotent" -> (ph.ph == ph && pk.pk == pk),
  "nonzeroCurvature" -> (curv == {{3/8, 0}, {0, -3/8}}),
  "fullCyclicRank" -> (MatrixRank[krylov] == 2),
  "cyclicDeterminant" -> (Det[krylov] == 3/4),
  "normalizedDetector" -> (detector == {-4/3, 4/3}),
  "hankelMatrix" -> (hankel == {{0, 1}, {1, 4}}),
  "hankelDeterminant" -> (Det[hankel] == -1),
  "zerothIterateNonzero" -> (iteration["zerothIterate"] == {1, 1, 1}),
  "oneProjectorRankObstruction" -> (iteration["orbitRank"] == 2 && iteration["orbitDeterminant"] == 0),
  "powersAndCumulatives" -> (iteration["allPowers0To8"] && iteration["cumulative0To8"])
|>;
result = <|"exactTests" -> checks,
  "allPassed" -> And @@ Values[checks],
  "nativeTwoProjectorMatrix" -> fold,
  "commutator" -> curv,
  "Krylov" -> krylov,
  "Hankel" -> hankel,
  "iteration" -> iteration|>;
Print[result];
result