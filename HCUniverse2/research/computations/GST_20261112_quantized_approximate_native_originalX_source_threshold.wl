(* Exact rational-lattice checkpoint for the owner's new GST native
   approximate-source condition. A rational prescribed target alpha
   with d*alpha integral, and an actual cycle class beta with m*beta
   integral and 1<=m<=C, satisfy:
     ||beta-alpha|| < 1/(d*C)  ==> beta=alpha
   in an integral coordinate norm. The full all-rank theorem is
   proved by integer lattice divisibility in the companion TeX.
   This finite experiment checks the SHARPNESS and a bounded range.
   It does NOT manufacture actual algebraic cycles or prove Hodge. *)
Module[{d=5,C=7,alpha=2/5,beta=3/7,
  errors,positives,test,minimum},
 errors=Flatten[Table[Abs[k/m-alpha],{m,1,C},{k,-12,12}]];
 positives=Select[errors,#>0&];
 test=Flatten[Table[If[Abs[k/m-alpha]<1/(d*C),
                          k/m==alpha,True],
                     {m,1,C},{k,-12,12}]];
 minimum=Min[positives];
 <|"targetAlpha"->alpha,
   "targetClearingDenominator"->d,
   "uniformCycleDenominatorBound"->C,
   "strictLatticeThreshold"->1/(d*C),
   "sharpNonMatchingCycleClass"->beta,
   "sharpBoundaryError"->Abs[beta-alpha],
   "minimumPositiveErrorInTest"->minimum,
   "boundedExactCases"->Length[errors],
   "finiteLatticeChecksPassed"->And@@test,
   "unimprovableStrictThresholdWitness"->Abs[beta-alpha]==1/(d*C),
   "allPassed"->(
     And@@test && minimum==1/(d*C) &&
     Abs[beta-alpha]==1/(d*C))|>
]