(* 2026-10-21, GST original-X excess components / native world return.
   Exact symbolic checks. These DO NOT establish existence of a prescribed
   Hodge-cycle detector on arbitrary X.
   Conventions: quotient projective bundles P(E), xi=c1(O(1)).
   Concrete projective quadric fourfold in P^5 with equation
   x0 y0+x1 y1+x2 y2=0; cut y1=y2=0 gives x0 y0=0.
*)
ClearAll[t,a,b,dimAmbient,chT,normalC,planeSelf,primitiveSq,
   pushCoeff,recErrors,checks];
dimAmbient=5;
chT=Normal[Series[(dimAmbient+1)Exp[t]-1-Exp[2t],{t,0,4}]];
normalC=Normal[Series[(1+t)^3/(1+2t),{t,0,2}]];
planeSelf=Coefficient[normalC,t,2];
primitiveSq=4planeSelf-4+2;
pushCoeff[n_Integer?NonNegative]:=Sum[a^(n-j)b^j,{j,0,n}];
recErrors=Table[
 Expand[pushCoeff[k]-(a+b)pushCoeff[k-1]+a b pushCoeff[k-2]],
 {k,2,8}];
checks=And[
   chT==4+4t+t^2-t^3/3-5t^4/12,
   normalC==1+t+t^2,
   planeSelf==1,primitiveSq==2,
   2*1-2==0,
   And@@(TrueQ[#==0]&/@recErrors)];
If[!TrueQ[checks],Print["FAILED CHECKS"];Abort[]];
Print[<|"checksPass"->True,
 "quadricTangentCh"->chT,
 "normalChern"->normalC,
 "quadricPrimitiveNorm"->primitiveSq,
 "projectiveBundlePushC0toC4"->Table[pushCoeff[k],{k,0,4}],
 "projectiveBundleRecurrenceErrors"->recErrors,
 "Scope"->"Exact finite coefficients only; theorem is from geometric Chow push-pull"|>];
