(* GST arbitrary full-multiplicity native mass calibration.
   Mathematical source: research/derivations/
     GST_fibered_native_mass_calibrated_cycle_birthday_2026-10-22.tex
   Exact rational experiment, p=1..12, positive-dimensional
   hyperplane complete-intersection generator relation:
       [W_2] = 2^p [W_1] in Chow/Betti.
   Native presentation is a FREE source cycle space: these
   two sources retain different coefficient masses.
   No Hodge-conjecture source-surjectivity assumption.
*)
ClearAll[nativeBetti,nativeMass,calibrated,gauge,w2,p,tests];
tests=Table[Module[{n=2^p,C,nu,b,aMass,bs},
 C={{1,n},{0,0}};
 nu={n,-1}/(n-1);
 b={0,1/n};aMass=1;
 bs=Simplify[b+(aMass-Total[b])*nu];
 <|"p"->p,
   "nullClass"->TrueQ[C.nu=={0,0}],
   "massOne"->TrueQ[Total[nu]==1],
   "massAfter"->TrueQ[Total[bs]==aMass],
   "classPreserved"->TrueQ[C.bs==C.b],
   "explicitCorrectedSource"->bs|>
 ],{p,1,12}];
allPass=And@@(And@@Values[KeyTake[#,
   {"nullClass","massOne","massAfter","classPreserved"}]]&/@tests);
If[!TrueQ[allPass],Print["FAIL"];Abort[]];
Print[<|"status"->"PASS","domain"->"exact rational p=1..12",
  "tests"->tests,"allPass"->True|>];
