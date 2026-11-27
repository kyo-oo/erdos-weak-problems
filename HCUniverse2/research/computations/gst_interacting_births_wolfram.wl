(* Independent exact Wolfram checks; evaluate with Wolfram Language. *)
Module[{cup4, gram4, sources4, primitive4, h, xx, zz, pp=3,
  reduce, top, cc, ss, gram6, terms, cup6, kernel6, primitive6,
  rr, tt, dd, aa, coupling, schur, numerator},
 cup4={{9,3,3,0,1},{-6,0,0,1,-3},{0,0,1,4,-3}};
 gram4={{1,0,0,0,0},{0,0,-1,0,0},{0,-1,0,0,0},
        {0,0,0,0,-1},{0,0,0,-1,3}};
 sources4={{1,21,-24,6,0},{-3,-11,18,0,6}};
 primitive4=sources4.gram4.Transpose[sources4];
 reduce[f_]:=Expand[PolynomialRemainder[Expand[f],xx^2+3h xx+2h^2,xx]];
 top[f_]:=Coefficient[Coefficient[reduce[f],xx,1],h,pp-1];
 cc=Normal[Series[(1-xx zz)(1+h zz)^pp/(1+2h zz),{zz,0,pp}]];
 ss=Normal[Series[1/cc,{zz,0,pp-2}]];
 gram6=ConstantArray[0,{7,7}];
 gram6[[1,1]]=1; gram6[[2,2]]=gram6[[3,3]]=-1;
 terms={{1,h^2},{1,xx h},{2,h},{2,xx}};
 Do[If[terms[[ii,1]]+terms[[jj,1]]>=pp,
   gram6[[ii+3,jj+3]]=-top[terms[[ii,2]] terms[[jj,2]]
      Coefficient[ss,zz,terms[[ii,1]]+terms[[jj,1]]-pp]]],{ii,4},{jj,4}];
 cup6={{9,3,3,0,0,0,1},{-6,0,0,0,0,1,-3},
       {0,1,0,3,0,1,-4},{0,0,0,1,0,8,-8},{0,0,0,0,1,4,-4}};
 kernel6=Reverse[NullSpace[cup6]];
 primitive6=kernel6.gram6.Transpose[kernel6];
 dd=(tt^2-1)/3;
 aa=rr^2/(4tt^2)+2-7rr/(3tt)+rr/3;
 coupling=tt/3-7/6+(3rr+4)/(12tt);
 schur=Factor[((dd+rr/4)aa-rr coupling^2)/.tt->2rr+1];
 numerator=rr*(105+411rr+596rr^2+384rr^3)/(36*(1+2rr)^2);
 <|"fourfoldCupSources"->cup4.Transpose[sources4],
   "fourfoldPrimitiveGram"->primitive4,
   "fourfoldDeterminant"->Det[primitive4],
   "fourfoldInverse"->Inverse[primitive4],
   "sixfoldAmbientGram"->gram6,"sixfoldCupRank"->MatrixRank[cup6],
   "sixfoldIntegerSources"->kernel6,"sixfoldPrimitiveGram"->primitive6,
   "sixfoldDeterminant"->Det[primitive6],
   "parallelSchurFormulaError"->Together[schur-numerator],
   "parallelSchurNumeratorCoefficients"->CoefficientList[105+411rr+596rr^2+384rr^3,rr]|>
]
