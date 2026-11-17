(* Mathbox all-original-X mathematical proof audits:
  exact Lagrange Vandermonde pure Chern interpolation,
  holomorphic non-abelian causal curvature, finite checks only.
  General theorems in research/derivations/
  GST_universal_affine_causal_flatness_descent_2026-10-23.tex.
*)
ClearAll["Global`*"];
momentWeights[d_Integer,e_Integer]:=LinearSolve[
 Table[If[j==0,1,k^j],{j,0,d},{k,0,d}],
 Table[If[j==e,Factorial[e],0],{j,0,d}]
];
momentChecks=Flatten[Table[
 Module[{w=momentWeights[d,e]},
  Table[
   {d,e,j,TrueQ[
     Sum[w[[k+1]] If[j==0,1,k^j],{k,0,d}]
       ==If[j==e,Factorial[e],0]]},
   {j,0,d}]],
 {d,1,9},{e,0,d}],2];
(* The whole-degree 2-variable line-bundle exponent:
   L^k tensor M^l maps to Exp[t(k x + l y)].
   The signed Lagrange sum must have only monomial x^2 y t^3. *)
dd=5;aa=2;bb=1;
wA=momentWeights[dd,aa];wB=momentWeights[dd,bb];
mixedSource=Expand[Sum[
 wA[[k+1]] wB[[l+1]]
  Normal[Series[Exp[t(k x+l y)],{t,0,dd}]],
 {k,0,dd},{l,0,dd}]];
(* A genuine non-flat holomorphic relative connection on a
  trivial rank-two bundle on affine C^2:
  ∇ = d + A dx + B dy. *)
am={{0,1},{0,0}};
bm={{0,0},{1,0}};
curvature=am.bm-bm.am;
out=<|
 "momentChecks"->Length[momentChecks],
 "allMomentsPass"->And@@momentChecks[[All,4]],
 "momentFailures"->Select[momentChecks,Not[#[[4]]]&],
 "d5MixedTensorLineMonomial"->mixedSource,
 "d5AllGradesPure"->TrueQ[Expand[mixedSource-x^aa y^bb t^(aa+bb)]==0],
 "d4Derivative1Weights"->momentWeights[4,1],
 "noncommutativeHolomorphicVerticalCurvature"->curvature,
 "noncommutativeCurvatureNonzero"->(curvature!={{0,0},{0,0}}),
 "tracelessCurvature"->TrueQ[Tr[curvature]==0],
 "underlyingBundleCanBeFlat"->True
|>;
Print[out];out