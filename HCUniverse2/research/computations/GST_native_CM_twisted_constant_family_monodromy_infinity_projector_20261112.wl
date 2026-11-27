(* GST native curvature-twisted constant family and all-cardinal finite monodromy energy projector.
   Exact integer/rational tests only; no assertion of generic algebraicity.
   ACTUAL geometric family is (P1xP1xCstar)/<(swap,t->-t)> -> C*, s=t^2.
   The genuine algebraic factor-swap operator on H2(P1xP1,Q)
   agrees with original GST fixed-null/max [J,M]/2 and equal-area Hodge Star.
   More general 5-d polarized rational model tests Picard-Lefschetz-type
   reflection finite fixed-vector compression without claiming realization
   on every original X or alpha. *)
Module[{twoId,swap,cm,surv,curv,pInv,pAnti,
    gram,n=5,id,ds,reflections,R,chi,q,degree,poly,projector,
    reflectedChecks,defectChecks,alpha},
twoId=IdentityMatrix[2];
swap={{0,1},{1,0}};
cm={{0,1},{-1,0}};surv={{0,0},{0,2}};
curv=cm.surv-surv.cm;
pInv=(twoId+swap)/2;pAnti=(twoId-swap)/2;
gram=DiagonalMatrix[{6,-2,-2,-2,-2}];
id=IdentityMatrix[n];
ds=Table[UnitVector[n,i],{i,2,n}];
reflections=Table[
  id-2 Outer[Times,d,gram.d]/(d.gram.d),
  {d,ds}];
R=Total[Table[Transpose[t-id].(t-id),{t,reflections}]];
chi=Expand[CharacteristicPolynomial[R,z]];
q=PolynomialQuotient[chi,z,z];
degree=Exponent[q,z];
poly=Sum[Coefficient[q,z,k]*If[k==0,id,MatrixPower[R,k]],
  {k,0,degree}];
projector=Together[poly/(q/.z->0)];
reflectedChecks=Table[
  reflections[[i]].reflections[[i]]==id &&
  Transpose[reflections[[i]]].gram.reflections[[i]]==gram,
  {i,Length[reflections]}];
defectChecks=Table[
  (reflections[[i]]-id).projector==ConstantArray[0,{n,n}],
  {i,Length[reflections]}];
alpha={a,b};
<|"twistedFamily"->"(P1xP1xC*)/(swap,t->-t), s=t^2",
  "originalGSTCurvatureIsTwiceGeometricMonodromy"->(curv==2*swap),
  "genuineCupPairingPreserved"->(
    Transpose[swap].{{0,1},{1,0}}.swap=={{0,1},{1,0}}),
  "swapInvariantProjector"->pInv,
  "swapAntiInvariantProjector"->pAnti,
  "prescribedAlphaInvariantProjection"->pInv.alpha,
  "prescribedAlphaLostAntiInvariantPart"->pAnti.alpha,
  "allReflectionPairingsPreserved"->And@@reflectedChecks,
  "allReflectionsAreOrderTwo"->And@@Table[
    reflections[[i]].reflections[[i]]==id,{i,Length[reflections]}],
  "defectEnergyMatrix"->R,
  "defectCharacteristicPolynomial"->Factor[chi],
  "zeroModeFilterPolynomial"->Factor[q],
  "normalizedRationalZeroModeProjector"->projector,
  "projectorRank"->MatrixRank[projector],
  "projectorIdempotent"->projector.projector==projector,
  "projectorKilledByAllMonodromyDefects"->And@@defectChecks,
  "allPassed"->And[curv==2*swap,
    swap.swap==twoId,pInv.pInv==pInv,pAnti.pAnti==pAnti,
    pInv.pAnti==ConstantArray[0,{2,2}],
    And@@reflectedChecks,And@@defectChecks,
    projector==DiagonalMatrix[{1,0,0,0,0}],
    projector.projector==projector]|>
]
