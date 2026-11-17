(* Exact symbolic check. The geometric interpretation is external. *)
Clear[d, m, u, a, b, c, e, t, x, y, graphGram, div0, divu,
  auxiliaryGram, jmat, sector0, sector1, extraction, fourth, orbit];

(* Basis: Graph(u), F1=E x {0}, F2={0} x E, diagonal. *)
graphGram = {{0,d,1,d+1},{d,0,1,1},{1,1,0,1},{d+1,1,1,0}};
div0 = {0,-1,-1,1};
divu = {1,-1,-d,0};
auxiliaryGram = Simplify[{
  {div0.graphGram.div0, div0.graphGram.divu},
  {divu.graphGram.div0, divu.graphGram.divu}}];

jmat = {{0,-d},{1,0}};
sector0 = {{1,0},{0,-1/d}};
sector1 = {{0,1},{1,0}};
extraction = Transpose[(#.auxiliaryGram.{1,0}) & /@ {sector0,sector1}];
fourth = PolynomialRemainder[(m+u)^4, u^2+d, u];
orbit = Det[Transpose[{{x,y},
  (Coefficient[fourth,u,0] IdentityMatrix[2] +
   Coefficient[fourth,u,1] jmat).{x,y}}]];

<|
 "KernelVersion" -> $Version,
 "AuxiliaryGram" -> auxiliaryGram,
 "ProductPolarizationPairings" ->
   {div0.graphGram.{0,1,0,0}, div0.graphGram.{0,0,1,0}},
 "PaddedHermitianDeterminant" ->
   Factor[Det[DiagonalMatrix[{a,b,-c,-e,t,-1/(a b c e t)}]]],
 "EqualizerChecks" -> Simplify[{
   jmat.sector0-sector0.Transpose[jmat],
   jmat.sector1-sector1.Transpose[jmat]}],
 "ExtractionMatrix" -> extraction,
 "ExtractionDeterminant" -> Det[extraction],
 "FourthPowerModuloQuadratic" -> Expand[fourth],
 "OrbitDeterminant" -> Factor[orbit],
 "ImaginaryCoefficientAtSafeChoice" ->
   Factor[Coefficient[fourth,u,1] /. m -> d+1]
|>
