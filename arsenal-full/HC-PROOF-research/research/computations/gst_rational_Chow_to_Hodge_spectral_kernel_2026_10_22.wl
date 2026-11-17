(* Mathbox/Wolfram exact evidence for:
   research/derivations/GST_hodge_spectral_rational_cycle_reduction_2026-10-22.tex
   Checks entire Hodge charge spectrum p=0..12 in the component basis,
   the rational/complex kernel interface, and a rank discriminator.
   These finite tests DO NOT prove the Hodge conjecture.
*)
ClearAll[p,charge,gen,proj,tests,gToy,cFull,cZero,result];
tests=Table[
  charge=Range[-p,p]*2;
  gen=DiagonalMatrix[I*charge];
  proj=If[p==0, IdentityMatrix[2*p+1], FullSimplify[
    Product[IdentityMatrix[2*p+1]+gen.gen/(4*r^2),{r,1,p}]]];
  <|"p"->p,
    "rankHodgeZero"->(2*p+1-MatrixRank[gen]),
    "rankDiagonalSpectralProjector"->MatrixRank[proj],
    "projectorIdempotent"->TrueQ[proj.proj==proj],
    "zeroChargeOnly"->TrueQ[
       Normal[proj]==Normal[SparseArray[{ {p+1,p+1}->1},{2*p+1,2*p+1}]]
       ]|>,
 {p,0,12}];
gToy={{0,0,0},{0,0,-2},{0,2,0}};
cFull={{1},{0},{0}};
cZero={{0},{0},{0}};
result=<|
  "spectralChargesP0Through12"->tests,
  "allFiniteSpectrumChecks"->And@@
    ((#["rankHodgeZero"]==1&&
       #["rankDiagonalSpectralProjector"]==1&&
       #["projectorIdempotent"]&&#["zeroChargeOnly"])&/@tests),
  "toySpectrum"->Eigenvalues[gToy],
  "toyRationalHodgeKernelRank"->3-MatrixRank[gToy],
  "sourceImageRankFull"->MatrixRank[cFull],
  "sourceImageRankZero"->MatrixRank[cZero],
  "bothSourcesChargeZero"->TrueQ[
    gToy.cFull==ConstantArray[0,{3,1}]&&
    gToy.cZero==ConstantArray[0,{3,1}]]
|>;
Print[result];
