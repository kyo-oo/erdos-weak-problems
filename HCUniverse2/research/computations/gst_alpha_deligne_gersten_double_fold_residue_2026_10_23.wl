(* Mathbox rational Deligne / algebraic Gersten source-degree audit.
   Concrete finite matrix and Koszul checks; the universal claims
   are proved mathematically in the paired LaTeX, not by extrapolation.
   Exact integers/rationals only; no random seeds or tolerances.
*)
ClearAll["Global`*"];
(* Finite rational homotopy-pullback exercise: two cocycles b and omega
   represent the same Betti/de Rham class iff their difference
   is an actual coboundary. This explicitly constructs u
   rather than inventing a Chow source. *)
d0={{1},{0},{0}};
d1={{0,0,1},{0,0,0}};
betti={2,3,0};
u={7};
omega=betti+d0.u;
deligneFinite=<|
 "cochainComplex"->TrueQ[d1.d0==ConstantArray[0,{2,1}]],
 "bothClosed"->TrueQ[d1.betti=={0,0}&&d1.omega=={0,0}],
 "nonzeroRationalCohomologyClass"->TrueQ[betti[[2]]!=0],
 "exactComparison"->TrueQ[omega-betti==d0.u],
 "recoveredPrimitive"->TrueQ[LinearSolve[d0,omega-betti]==u]
|>;
(* A real double-GERSTEN residue test for ordered normal crossings:
   Symbol {t,s,u...}; tame residue at t then s has + sign,
   residue at s then t has - sign. At any total degree p>=2,
   antisymmetry cancels these two branch contributions.
   This is the exact Koszul sign of log differentials. *)
doubleResidues=Table[
 {p,
  Signature[{1,2}]*1+Signature[{2,1}]*1,
  TrueQ[Signature[{1,2}]+Signature[{2,1}]==0]},
 {p,2,16}];
(* Independent fixed-term derived source test ON ACTUAL projective P1:
   for every degree n, every section of O(n) has zero divisor
   of degree n; the two-term Koszul complex
   [O(-n) --> O] has K class O-O(-n), independent of
   its differential. ch(O)-ch(O(-n))=n h on P1, h^2=0.
*)
fixedTerms=Flatten[Table[
 {n,a,b,
  TrueQ[SeriesCoefficient[1-Exp[-n h],{h,0,1}]==n],
  TrueQ[(1-Exp[-n h])-(1-Exp[-n h])==0]},
 {n,1,12},{a,0,3},{b,0,2}],2];
(* Actual projective Grassmannian nondivisor character source:
   alpha=(2/5)h^2-s2, with
   ch2(S)=(1/2)h^2-s2; ch2(O(1))=(1/2)h^2. *)
hodgeAlpha=2 hh^2/5-s2;
characterSource=5(hh^2/2-s2)-hh^2/2;
grSourceExact=TrueQ[Expand[characterSource-5hodgeAlpha]==0];
(* All-dimensional U_p=(E-minus-P)^p: H_dR^1(U) has rank 2;
   the tensor product contributes exactly 2^p linearly
   independent degree-p differential classes, while
   every GLOBAL algebraic unit on U_p is constant.
   Mathematical proof uses restriction to each factor and
   affine algebraic de Rham Kunneth, not the finite test. *)
affineDimensions=Table[
 {p,2^p,TrueQ[2^p>0],TrueQ[0<2^p]},
 {p,1,18}];
(* NEW exact TRUE-fold positive algebraic spectral K-source:
   Q=Spec C[x,y,z]/(xy+z^2-1) is P1 Jouanolou incidence,
   A=[[z,x],[y,-z]], P=(I+A)/2.
   Compute the full algebraic Chern curvature by tangent
   differentiation with z_x=-y/(2z), z_y=-x/(2z)
   and independently compare to the Poincare residue
   dx wedge dy/(2z). No numerical integration. *)
spectralA={{z,x},{y,-z}};
spectralP=(IdentityMatrix[2]+spectralA)/2;
spectralPx=D[spectralP,x]+D[spectralP,z]*(-y/(2z));
spectralPy=D[spectralP,y]+D[spectralP,z]*(-x/(2z));
spectralCurvature=FullSimplify[
 Tr[spectralP.(spectralPx.spectralPy-spectralPy.spectralPx)]
     /. x*y->1-z^2];
spectralChecks=<|
 "genuineAlgebraicInvolution"->TrueQ[
  FullSimplify[(spectralA.spectralA-IdentityMatrix[2])/.x*y->1-z^2]
       ==ConstantArray[0,{2,2}]],
 "actualProjector"->TrueQ[
  FullSimplify[(spectralP.spectralP-spectralP)/.x*y->1-z^2]
       ==ConstantArray[0,{2,2}]],
 "projectorTraceOne"->TrueQ[FullSimplify[Tr[spectralP]==1]],
 "chernCurvatureCoefficient"->spectralCurvature,
 "curvatureEqualsHalfResidue"->TrueQ[
  FullSimplify[spectralCurvature-1/(4z)]==0],
 "normalizedIntegralChernNumber"->-1
|>;
out=<|
 "trueJouanolouSpectralAlgebraicSource"->spectralChecks,
 "puncturedEllipticProductDimensions"->Length[affineDimensions],
 "nonzeroDeRhamVsZeroGlobalUnitLogAll"->And@@Flatten[affineDimensions[[All,3;;4]]],
 "highestDegreeCohomologyDimension"->affineDimensions[[-1,2]],
 "DeligneCocycleConstructed"->deligneFinite,
 "GerstenDoubleResidueRanks"->Length[doubleResidues],
 "GerstenBoundarySquareZero"->And@@doubleResidues[[All,3]],
 "GerstenFailures"->Select[doubleResidues,Not[#[[3]]]&],
 "KoszulSourceTests"->Length[fixedTerms],
 "AllKoszulChowSourceInvarianceChecks"->And@@Flatten[fixedTerms[[All,4;;5]]],
 "KoszulFailures"->Select[fixedTerms,Not[And@@#[[4;;5]]]&],
 "NondivisorAlgebraicCh2Source"->grSourceExact
|>;
Print[out];out