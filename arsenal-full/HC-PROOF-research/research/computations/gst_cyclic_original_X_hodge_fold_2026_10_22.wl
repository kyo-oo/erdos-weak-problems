(* GST cyclic original-X causal Hodge fold: exact finite audit.
   2026-10-22. Stateless Wolfram Language, exact symbolic integers/rationals.
   This tests equations (6)-(9) in GST_cyclic_original_X_causal_hodge_fold_2026-10-22.tex.
   It does NOT establish existence of original-X Hodge cycle lifts or prove geometry.
*)
ClearAll[t,s,u,v,a,pE,pP,cyclicInvariant,fold,smooth,twice,coeff,nonnegativeQ,profiles];
a=t^2 s^2 u v;
pE=1+t s (u+v)+a;
pP=1+a;
cyclicInvariant[pp_, mm_Integer?Positive] :=
  Expand[Sum[With[{gg=GCD[mm,j], ll=mm/GCD[mm,j]},
      (pp /. {t -> (-1)^(ll-1) t^ll, s -> s^ll,
              u -> u^ll, v -> v^ll})^gg],
     {j,0,mm-1}]/mm];
fold[pp_,mm_] := Expand[(1+t) cyclicInvariant[pp,mm]+a pp^mm];
smooth[pp_,mm_] := Expand[(1+t s (u+v)+a) cyclicInvariant[pp,mm]];
twice[pp_,mm_] := Expand[(1+t+a) fold[pp,mm]];
coeff[pp_,kk_,ww_] := Expand[Coefficient[Coefficient[pp,t,kk],s,ww]];
nonnegativeQ[pp_] := AllTrue[Last /@ CoefficientRules[pp,{t,s,u,v}],#>=0&];
profiles=Table[{mm,cyclicInvariant[pE,mm]/.{t->1,s->1,u->1,v->1},
               nonnegativeQ[cyclicInvariant[pE,mm]]},{mm,1,5}];
<|
"ellipticCyclicProfiles"->profiles,
"ellipticFoldWeight1Degree2"->coeff[fold[pE,2],2,1],
"ellipticFoldWeight2Degree2"->coeff[fold[pE,2],2,2],
"ellipticSmoothWeight2Degree2"->coeff[smooth[pE,2],2,2],
"ellipticDoubleWeight2Degree4"->coeff[twice[pE,2],4,2],
"P1DoubleWeight2Degree4"->coeff[twice[pP,2],4,2],
"differenceExact"->(Expand[smooth[pE,2]-fold[pE,2]-
   t(s(u+v)-1)cyclicInvariant[pE,2]-
   a(cyclicInvariant[pE,2]-pE^2)]===0),
"allCyclicNonnegative"->And@@(profiles[[All,3]]),
"ellipticFoldNonnegative"->nonnegativeQ[fold[pE,2]],
"P1DoubleNonnegative"->nonnegativeQ[twice[pP,2]]
|>
