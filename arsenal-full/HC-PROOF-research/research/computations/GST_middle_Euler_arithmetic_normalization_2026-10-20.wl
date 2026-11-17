Module[
 {xx, dims = {5, 3, 1}, weights = {2, -3, 5}, lower, reverse,
  blocks, lmat, pmat, jmat, cpoly, spoly, rpoly, smat, rmat, zmat,
  trunc, eval, polyMat, blockChecks, familyChecks, supportChecks, toddChecks,
  ccoef = {1, 2, 3, -1, 5}},
 trunc[poly_, n_] := Normal[Series[poly, {xx, 0, n}]];
 lower[n_] := Table[If[i == j + 1, 1, 0], {i, n}, {j, n}];
 reverse[n_] := Reverse[IdentityMatrix[n]];
 blocks[mats_] := ArrayFlatten[
   Table[If[i == j, mats[[i]], ConstantArray[0, {Length[mats[[i]]], Length[mats[[j]]]}]],
     {i, Length[mats]}, {j, Length[mats]}]];
 lmat = blocks[lower /@ dims];
 pmat = blocks[MapThread[#1 reverse[#2] &, {weights, dims}]];
 jmat = blocks[MapThread[#1 reverse[#2] &, {{1, -1, 1}, dims}]];
 cpoly = Sum[ccoef[[j + 1]] xx^j, {j, 0, 4}];
 spoly = trunc[1/cpoly, 4];
 rpoly = trunc[Sqrt[cpoly], 4];
 polyMat[coeffs_, mat_] := Fold[(#1.mat + #2 IdentityMatrix[Length[mat]]) &,
   ConstantArray[0, Dimensions[mat]], Reverse[coeffs]];
 eval[poly_, mat_, n_] := polyMat[Table[Coefficient[poly, xx, j], {j, 0, n}], mat];
 smat = eval[spoly, lmat, 4];
 rmat = eval[rpoly, lmat, 4];
 zmat = ConstantArray[0, {9, 9}];
 blockChecks = <|
  "graded_dimensions" -> {1, 2, 3, 2, 1},
  "normal_polynomial" -> cpoly, "square_root" -> rpoly,
  "nilpotent" -> (Nest[lmat.# &, IdentityMatrix[9], 5] == zmat),
  "self_adjoint" -> (Transpose[lmat].pmat == pmat.lmat),
  "normal_removed" -> (Transpose[rmat].pmat.smat.rmat == pmat),
  "unipotent_determinants" -> {Det[smat], Det[rmat]},
  "discriminant_ratio" -> (Det[pmat.smat]/Det[pmat]),
  "polarization_involution" -> (jmat.jmat == IdentityMatrix[9]),
  "polarized_eigenvalues" -> Eigenvalues[pmat.jmat],
  "polarized_positive" -> And @@ ((# > 0) & /@ Eigenvalues[pmat.jmat])
 |>;
 familyChecks = Flatten[Table[Module[
   {rank = 2 mm - dd, ll, pp, ss, rr},
   ll = lower[dd + 1]; pp = reverse[dd + 1];
   ss = polyMat[Table[Binomial[-rank, j], {j, 0, dd}], ll];
   rr = polyMat[Table[Binomial[rank/2, j], {j, 0, dd}], ll];
   {dd, mm, Transpose[rr].pp.ss.rr == pp, Det[ss] == 1, Det[rr] == 1}
  ], {dd, 0, 8}, {mm, {dd + 1, 2 dd + 3}}], 1];
 supportChecks = Flatten[Table[
   {rr, kk, Expand[trunc[(1 + xx)^rr Sum[Binomial[-rr, j] xx^j, {j, 0, kk}], kk]] == 1},
   {rr, {0, 1, 2, 5, 11}}, {kk, 0, 7}], 1];
 toddChecks = Table[
  {rr, Expand[trunc[(Exp[xx] - 1)^rr
    (Log[1 + (Exp[xx] - 1)]/(Exp[xx] - 1))^(rr + 1)
    - xx^(rr + 1)/(Exp[xx] - 1), 12]] == 0},
  {rr, 0, 6}];
 <|"heterogeneous_block_test" -> blockChecks,
   "projective_normal_tests" -> familyChecks,
   "single_support_inverse_checks" -> supportChecks,
   "finite_log_Todd_checks" -> toddChecks|>
]
