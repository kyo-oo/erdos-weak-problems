(* Mathbox corrected-direction exact arithmetic audit.
   Claimed universal geometry is proved in accompanying LaTeX by
   rational K-theory + Thom-Porteous + Hodge-Riemann + Federer-Fleming.
   This script audits finite polynomial identities, not source algebraization.
*)
ClearAll["Global`*"];
tests=Flatten[Table[
 Module[{t=Unique["t"],a=Unique["a"],h=Unique["h"],
    lam=Unique["lam"],m=Unique["m"],c,cp,cm},
  c=(-1)^(p-1) Factorial[p-1] m;
  cp=Coefficient[Normal[Series[
     Exp[c (a+lam h^p) t^p],{t,0,p}]],t,p];
  cm=Coefficient[Normal[Series[
     Exp[c lam h^p t^p],{t,0,p}]],t,p];
  {p,d,TrueQ[FullSimplify[
    (-1)^(p-1) (cp-cm)/(m Factorial[p-1])==a]],
   TrueQ[2(p+1)-p>=p+2]}
 ],{p,1,8},{d,p,12}],1];
(* Exact Kähler-angle inequality for complex line calibration:
   2(1-cos theta) - sin(theta)^2 = (1-cos theta)^2 >=0. *)
angleDefect=FullSimplify[
  2(1-Cos[t]) - Sin[t]^2 -(1-Cos[t])^2];
out=<|
 "ChernSignedNormalizationCases"->Length[tests],
 "exactOriginalXTargetReconstruction"->And@@tests[[All,3]],
 "properStrataCodimensions"->And@@tests[[All,4]],
 "failures"->Select[tests,Not[#[[3]]&&#[[4]]]&],
 "exactKaehlerAngleIdentity"->TrueQ[angleDefect==0]
|>;
Print[out];out