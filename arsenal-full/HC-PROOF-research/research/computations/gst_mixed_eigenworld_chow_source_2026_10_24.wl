(* Exact K0-model and Chern character finite checks for independent GST
   double-world anti-eigenline sources. Rational/integral symbolic arithmetic.
   Does not prove full Hodge conjecture. Date 2026-10-24. *)
ClearAll[uu, aa, bb, tt, rr];
mixed2=8 uu[1] uu[2];
singleSquareReduction = PolynomialReduce[(2 uu[1])^2,
  {uu[1]^2,uu[2]^2},{uu[1],uu[2]}][[2]]===0;
mixed2Reduction=PolynomialReduce[mixed2,
  {uu[1]^2,uu[2]^2},{uu[1],uu[2]}][[2]];
mixed2Nonzero = mixed2Reduction===mixed2;
evenTests=Table[
 Module[{vars=Array[uu,r],prod,rem},
  prod=2 Times@@(2 vars);
  rem=PolynomialReduce[prod,vars^2,vars][[2]];
  Simplify[rem==2^(r+1) Times@@vars]],
 {r,{2,4,6}}];
oddTests=Table[
 Module[{vars=Array[uu,r],plus,minus},
   plus=Times@@(2 vars); minus=Times@@(-2 vars);
   Simplify[plus+minus==0]],
 {r,{1,3,5,7}}];
leadTests=Table[
 Module[{expr,lead,lower},
  expr=Normal[Series[Product[Exp[tt aa[i]]-Exp[tt bb[i]],
                                  {i,1,r}],{tt,0,r}]];
  lead=Coefficient[expr,tt,r];
  lower=And@@Table[Coefficient[expr,tt,j]===0,{j,0,r-1}];
  TrueQ[Simplify[lead==Product[aa[i]-bb[i],{i,1,r}]]]&&lower],
 {r,1,6}];
tests=<|
"OneSourceSquareZeroInK0"->singleSquareReduction,
"TwoIndependentSourcesMixedNonzero"->mixed2Nonzero,
"NonzeroEvenDimensionalReturns"->And@@evenTests,
"OddDeckCharacterCancellation"->And@@oddTests,
"ExactLeadingChowGrading"->And@@leadTests
|>;
Print["TESTS=",tests];
Print["ALL_TRUE=",And@@Values[tests]];
Print["MIXED_TWO_CHOW_K0=",mixed2Reduction];
Print["EVEN_CASES_2_4_6=",evenTests];
Print["ODD_CASES_1_3_5_7=",oddTests];
Print["CHOW_GRADINGS_1_TO_6=",leadTests];
