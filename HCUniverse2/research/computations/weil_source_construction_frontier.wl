(* Exact discriminators for the original Weil-fourfold source problem.
   These calculations do not construct a variety, sheaf, or cycle. *)
ClearAll[t, r, c1, c2, c3, d, aa, bb, cc, ee];
ch = r + c1 t + (c1^2 - 2 c2) t^2/2 +
  (c1^3 - 3 c1 c2 + 3 c3) t^3/6;
normal = Normal[Series[Exp[-c1 t/r] ch, {t, 0, 3}]];
kappa3 = Factor[Coefficient[normal, t, 3]];
cycleFormula = c3/2 - (r - 2) c1 c2/(2 r) +
  (r - 1) (r - 2) c1^3/(6 r^2);
normalizationResidual = Together[kappa3 - cycleFormula];
lineTwistResidual = Together[Coefficient[
  Normal[Series[Exp[-(c1/r + aa) t] Exp[aa t] ch,
    {t, 0, 3}]] - normal, t, 3]];
Print["Wolfram version: ", $Version];
Print["Normalized codimension-three Chern cycle: ", InputForm[cycleFormula]];
Print["Chern identity residual: ", normalizationResidual];
Print["Line tensor normalization residual: ", lineTwistResidual];

(* Generic End^0(A)=Q(u), u^2=-d, contains no nonzero anti-K element.
   This rules out copying a quaternionic graph endomorphism on this A.
   It does not rule out arbitrary algebraic correspondences or surfaces. *)
jmat = {{0, -d}, {1, 0}};
kmat = {{aa, -d bb}, {bb, aa}};
Print["Quadratic centralizer commutator: ", kmat.jmat - jmat.kmat];
Print["Anti-K equations in the quadratic field: ",
  Solve[Thread[Flatten[kmat.jmat + jmat.kmat] == 0], {aa, bb}]];

(* Formal generic middle-Hodge/Lefschetz representation, NOT a Betti
   realization: first five vectors are theta^k/k!, last two are Weil.
   The block property, rather than a finite word cutoff, proves invariance.
   Adding a CM action within the last two coordinates cannot birth a source. *)
lift = ConstantArray[0, {7, 7}];
Do[lift[[k + 2, k + 1]] = k + 1, {k, 0, 3}];
fourier = ConstantArray[0, {7, 7}];
Do[fourier[[5 - k, k + 1]] = (-1)^k, {k, 0, 4}];
fourier[[6, 6]] = 1; fourier[[7, 7]] = 1;
adams = DiagonalMatrix[{1, 2, 4, 8, 16, 4, 4}];
cm = IdentityMatrix[7]; cm[[6 ;; 7, 6 ;; 7]] = {{-7, -24}, {24, -7}};
generators = {lift, fourier, adams, cm};
noCrossBlock = And @@ Flatten[Map[
  Thread[Flatten[#[[6 ;; 7, 1 ;; 5]]] == 0] &, generators]];
seed = UnitVector[7, 1];
fiveSources = NestList[lift.# &, seed, 4];
Print["Lower-left blocks vanish for every generator: ", noCrossBlock];
Print["Polarization-generated span rank: ", MatrixRank[fiveSources]];
Print["Every generated vector has zero Weil coordinates: ",
  And @@ (# == 0 & /@ Flatten[fiveSources[[All, 6 ;; 7]]])];
Print["Interpretation: arbitrary words and rational combinations preserve the five-dimensional ambient block; this is not a counterexample to Hodge."];
If[normalizationResidual =!= 0 || lineTwistResidual =!= 0 ||
   !noCrossBlock || MatrixRank[fiveSources] =!= 5, Abort[]];
