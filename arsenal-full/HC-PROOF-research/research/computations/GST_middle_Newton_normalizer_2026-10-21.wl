(* Identity check; evaluated as the first independent cell. *)
Module[{ss, rr, dd, nn, step},
 step = rr (3-ss rr^2)/2;
 <|"rational_Newton_error_identity" ->
   Expand[1-ss step^2-(1-ss rr^2)^2 (3+(1-ss rr^2))/4],
   "integral_Newton_error_identity" ->
   Expand[(2 dd^3)^2-ss (nn (3 dd^2-ss nn^2))^2-
     (dd^2-ss nn^2)^2 (3 dd^2+(dd^2-ss nn^2))]|>
]

(* Finite exact comparison tests; evaluated as the second independent cell. *)
Module[{lower, polyMat, checks, xx},
 lower[n_] := Table[If[i == j+1,1,0],{i,n},{j,n}];
 polyMat[coeff_, mat_] := Fold[(#1.mat + #2 IdentityMatrix[Length[mat]]) &,
   ConstantArray[0,Dimensions[mat]], Reverse[coeff]];
 checks = Flatten[Table[Module[{ll, ss, rr, expected, ident, rank},
   ll=lower[dd+1]; ident=IdentityMatrix[dd+1]; rank=2 mm-dd;
   ss=polyMat[Table[Binomial[-rank,j],{j,0,dd}],ll];
   rr=ident;
   Do[rr=rr.(3 ident-ss.rr.rr)/2,{dd+1}];
   expected=polyMat[Table[Binomial[rank/2,j],{j,0,dd}],ll];
   {dd,mm,ss.rr.rr==ident,rr==expected}
 ],{dd,0,8},{mm,{dd+1,2 dd+3}}],1];
 <|"Newton_constructed_normalizers"->checks,
   "all_exact"->And@@Flatten[checks[[All,{3,4}]]]|>
]
