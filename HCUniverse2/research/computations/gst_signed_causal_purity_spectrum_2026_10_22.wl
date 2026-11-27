(* GST signed causal purity spectrum, 22 Oct 2026.
   Exactly tests the three full Hodge/weight polynomials (equation 14),
   at m=2,3,4 and ell=1,2,3, X = elliptic or projective line,
   p=0,1: 2*3*3*2=36 deterministic exact cases.
   Invariants use graded Koszul cycle-index characters, no floating point.
   The program does NOT verify scheme quotients or arbitrary-X theorem.
*)
ClearAll[tt,ss,uu,vv,aTate,bOpen,pEll,pLine,invar,triplet,coef,nne,allTests,run];
aTate=tt^2 ss^2 uu vv; bOpen=tt ss^2 uu vv;
pEll=1+tt ss(uu+vv)+aTate;
pLine=1+aTate;
invar[poly_,mm_Integer?Positive]:=
  Expand[Sum[With[{g=GCD[mm,j],len=mm/GCD[mm,j]},
      (poly/.{tt->(-1)^(len-1)tt^len,ss->ss^len,
               uu->uu^len,vv->vv^len})^g],
      {j,0,mm-1}]/mm];
triplet[poly_,mm_Integer?Positive,ell_Integer?Positive]:=
  Module[{i=invar[poly,mm]},{
    Expand[((1+tt)i+aTate poly^mm)(1+tt+aTate)^(2ell-1)],
    Expand[(1+tt ss(uu+vv)+aTate)i(1+aTate)^(2ell-1)],
    Expand[i(1+bOpen)^(2ell)]
  }];
coef[poly_,kk_,ww_,pp_,qq_]:=
   Coefficient[Coefficient[Coefficient[
      Coefficient[poly,tt,kk],ss,ww],uu,pp],vv,qq];
nne[poly_]:=And@@(NonNegative/@(Last/@
                         CoefficientRules[poly,{tt,ss,uu,vv}]));
run[poly_,mm_,ell_,pp_]:=
  Module[{z=triplet[poly,mm,ell],k=2pp+2ell},{
    coef[z[[1]],k,2pp,pp,pp],
    coef[z[[2]],k,2pp+2ell,pp+ell,pp+ell],
    coef[z[[3]],k,2pp+4ell,pp+2ell,pp+2ell],
    And@@(nne/@z)
  }];
allTests=Flatten[Table[
   With[{test=run[poly,mm,ell,pp]},
     {If[poly===pEll,"elliptic","line"],mm,ell,pp,test,
      And@@(Positive/@Take[test,3])&&test[[4]]}],
   {poly,{pEll,pLine}},{mm,2,4},{ell,1,3},{pp,0,1}],3];
{
  "cases", Length[allTests],
  "allChecked", And@@allTests[[All,6]],
  "elliptic_m2_ell1_p1",
     Select[allTests,#[[1]]=="elliptic"&&#[[2]]==2&&
                     #[[3]]==1&&#[[4]]==1&],
  "line_m2_ell1_p1",
     Select[allTests,#[[1]]=="line"&&#[[2]]==2&&
                     #[[3]]==1&&#[[4]]==1&],
  "minimumThreeSectorDimensions",
     Min/@Transpose[allTests[[All,5,1;;3]]],
  "failedCases", Select[allTests,Not[#[[6]]]&]
}
