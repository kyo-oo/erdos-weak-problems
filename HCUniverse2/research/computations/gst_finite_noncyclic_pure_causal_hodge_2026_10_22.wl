(* Genuine noncyclic finite holonomy: E^2, swap and global [-1].
   All exact rational character polynomials; 2026-10-22. *)
ClearAll[tt,ss,uu,vv,aa,pe,pb,trSwap,trNeg,trSwapNeg,pk,y,s,check,coeff,pos];
tt=Unique["tt"];ss=Unique["ss"];uu=Unique["uu"];vv=Unique["vv"];
aa=tt^2 ss^2 uu vv;pe=1+tt ss(uu+vv)+aa;pb=Expand[pe^2];
trSwap=Expand[pe/.{tt->-tt^2,ss->ss^2,uu->uu^2,vv->vv^2}];
trNeg=Expand[(pe/.tt->-tt)^2];
trSwapNeg=trSwap;
pk=Expand[(pb+trSwap+trNeg+trSwapNeg)/4];
y=Expand[(1+tt)pk+(aa+tt)pb];
s=Expand[(1+aa)pk+tt ss(uu+vv)(pb+pk)];
coeff[pol_,k_,w_]:=Expand[Coefficient[Coefficient[pol,tt,k],ss,w]];
pos[pol_]:=And@@Map[(IntegerQ[#]&&#>=0)&,Last/@CoefficientRules[pol,{tt,ss,uu,vv}]];
<|"GInvariantPolynomial"->pk,"BettiInvariantDimension"->(pk/.{tt->1,ss->1,uu->1,vv->1}),
"nodeH2Weight1"->coeff[y,2,1],"nodeH2Weight2"->coeff[y,2,2],
"smoothH2Weight2"->coeff[s,2,2],"allCoefficientsNonnegative"->(pos[pk]&&pos[y]&&pos[s])|>