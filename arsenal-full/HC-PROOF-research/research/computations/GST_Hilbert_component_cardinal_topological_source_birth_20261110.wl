(* GST original-X cardinal/topology/Hilbert source experiment.
   Geometry: X=P^1 x P^1 embedded by Segre O(1,1).
   Lines on X split into two P^1 connected Hilbert components (two
   rulings) with the SAME Hilbert polynomial m+1, but distinct native
   Chow/Hodge classes H1 and H2. Each component's infinitely many
   members share a single rational cohomology class.
   Tested exactly: all 64 finite samples with 0..7 parameters from
   each component; true intersection form and component-swap fold;
   independent complementary-cycle detector gate.

   This is an exact geometric toy case, NOT a universal-X Hodge proof.
*)
ClearAll[inter,h1,h2,h,source,case,cases,fold,seed,ell,hank,
  fullPair,oldSource,goodDual,badDual,bg,bb,gst];
inter={{0,1},{1,0}};
h1={1,0};h2={0,1};h=h1+h2;
source[m_Integer?NonNegative,n_Integer?NonNegative]:=
 Join[ConstantArray[h1,m],ConstantArray[h2,n]];
case[m_Integer?NonNegative,n_Integer?NonNegative]:=
 Module[{s=source[m,n],r,expected},
 r=If[Length[s]==0,0,MatrixRank[s]];
 expected=If[m>0&&n>0,2,If[m+n>0,1,0]];
 <|"m"->m,"n"->n,"sourceRank"->r,"expected"->expected,
   "passed"->(r==expected)|>
];
cases=Flatten[Table[case[m,n],{m,0,7},{n,0,7}],1];
fold={{0,1},{1,0}};
seed=h1;
ell=h1;
hank=Table[ell.MatrixPower[fold,i+j].seed,
 {i,0,1},{j,0,1}];
(* Abstract perfect Poincare pairing with restricted complementary
   algebraic source families. The bad restriction is not asserted
   realizable for any actual X. *)
fullPair=IdentityMatrix[3];
oldSource={{1,0,0},{0,1,0}};
goodDual={{1,0,0},{0,1,0}};
badDual={{1,0,0},{0,0,1}};
bg=oldSource.fullPair.Transpose[goodDual];
bb=oldSource.fullPair.Transpose[badDual];
gst=<|
 "SegreDegreeH1"->h1.inter.h,
 "SegreDegreeH2"->h2.inter.h,
 "rulingsIntersection"->h1.inter.h2,
 "rulingSelfSquares"->{h1.inter.h1,h2.inter.h2},
 "sameHilbertPolynomialForBothRulings"->"m+1",
 "sampleCount"->Length[cases],
 "allSampleRankPredictions"->And@@(Lookup[#,"passed"]&/@cases),
 "withinFirstComponentRank"->case[7,0]["sourceRank"],
 "withinSecondComponentRank"->case[0,7]["sourceRank"],
 "bothComponentsRank"->case[7,7]["sourceRank"],
 "factorSwapOrbitRank"->MatrixRank[Transpose[{seed,fold.seed}]],
 "swapHankelDet"->Det[hank],
 "actualChowComplementaryPairingMatrix"->inter,
 "actualChowComplementaryPairingRank"->MatrixRank[inter],
 "abstractGoodDualPairRank"->MatrixRank[bg],
 "abstractBadDualPairRank"->MatrixRank[bb],
 "allPassed"->(
   And@@(Lookup[#,"passed"]&/@cases)&&
   h1.inter.h==1&&h2.inter.h==1&&
   MatrixRank[inter]==2&&Det[hank]==1&&
   MatrixRank[bg]==2&&MatrixRank[bb]==1)
 |>;

(* ACTUAL ORIGINAL-X CHOW CORRESPONDENCE MATRIX from each Hilbert
   component: Gamma_Z = (1/q) pr1*h^(d-p) pr2*Z;
   F_Z(beta)=ell_h(beta) Z, ell_h(beta)=int beta*h/q.
   Two representatives of one connected Hilbert component induce the
   same BETTI operator even when their Chow classes are not equal. *)
ellh=(inter.h)/(h.inter.h);
actualGamma1=Outer[Times,h1,ellh];
actualGamma2=Outer[Times,h2,ellh];
actualCurvature=actualGamma1.actualGamma2-
 actualGamma2.actualGamma1;
topologicalSourceCheck=<|
 "ampleSelfIntersection"->h.inter.h,
 "nativeOneSeedHitsRuling1"->(actualGamma1.h==h1),
 "nativeOneSeedHitsRuling2"->(actualGamma2.h==h2),
 "genuineChowComponentComposition"->(
   actualGamma1.actualGamma2==(ellh.h2)actualGamma1 &&
   actualGamma2.actualGamma1==(ellh.h1)actualGamma2),
 "noncommutativeTopologicalCurvature"->actualCurvature,
 "curvatureNonzero"->(actualCurvature!=ConstantArray[0,{2,2}]),
 "sourceSpanIsTwo"->(MatrixRank[{actualGamma1.h,actualGamma2.h}]==2)
|>;
gst=Join[gst, <|
 "realHilbertComponentChowSourceOperators"->topologicalSourceCheck,
 "allWithGeometricOperatorsPassed"->(
  gst["allPassed"] &&
  topologicalSourceCheck["nativeOneSeedHitsRuling1"] &&
  topologicalSourceCheck["nativeOneSeedHitsRuling2"] &&
  topologicalSourceCheck["genuineChowComponentComposition"] &&
  topologicalSourceCheck["curvatureNonzero"] &&
  topologicalSourceCheck["sourceSpanIsTwo"])
 |>];
Print[gst];gst
