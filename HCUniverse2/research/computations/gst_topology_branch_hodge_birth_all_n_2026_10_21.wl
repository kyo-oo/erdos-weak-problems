(* Genuine smooth-projective double-cover topology fold.
   All-n mathematical proof in:
   research/derivations/GST_topological_branch_fold_all_N_Hodge_birth_2026_10_21.tex
   Checks exact coefficient identities p=1..8 for independent formal
   m,k, and geometric intersection calibrations P^(2p), m=1,k=2p+1.
   The finite test cannot establish existence/smoothness of algebraic
   cover; these are proved geometrically with Bertini in the manuscript. *)
ClearAll[t,m,k,p,n,d,bEuler,yEuler,sChern,antiSquare,check,values,
   char,deg,top];
sChern[p_Integer?Positive]:=
 Coefficient[Normal[Series[(1+m*t)^p*(1+k*t)/(1+2*k*t),
                        {t,0,p}]],t,p];
antiSquare[p_Integer?Positive]:=Expand[4*sChern[p]-2*m^p];
values=Table[
 {p,FullSimplify[sChern[p]-(m^p+(m-2*k)^p)/2]===0,
    FullSimplify[antiSquare[p]-2*(m-2*k)^p]===0,
    2*(-4*p-1)^p},
 {p,1,8}];
d[n_Integer?Positive]:=2*(n+1);
bEuler[n_Integer?Positive]:=
 d[n]*Sum[Binomial[n+1,j]*(-d[n])^(n-1-j),{j,0,n-1}];
yEuler[n_Integer?Positive]:=2*(n+1)-bEuler[n];
top=Table[{n,d[n],bEuler[n],yEuler[n]},{n,1,8}];
check=And@@Flatten[values[[All,2;;3]]];
If[!TrueQ[check]||top[[2,4]]!=24||top[[3,4]]!=-296||
   values[[1,4]]!=-10||values[[2,4]]!=162,
   Print["FAIL"];Abort[]];
Print[<|"exactAllCoefficientChecksP1to8"->values,
  "evenBranchCalabiYauMiddleAntiSquare"->values[[All,{1,4}]],
  "branchEulerForPn1to8"->top,
  "sampleK3AntiNorm"->values[[1,4]],
  "sampleCalabiYauFourfoldAntiNorm"->values[[2,4]],
  "allChecksPass"->True|>];
