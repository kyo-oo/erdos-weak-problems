(* Independent symbolic center interpolation and source-period checks. *)
Module[{zz, cc, p, j, result, target, errors, a, b, dd, nn, v, center, primitive, gram},
 errors=Table[
   cc=1+Sum[Subscript[v,i]zz^i,{i,1,p}];
   result=Sum[(-1)^(p+j-2)Binomial[p,j]/(j Factorial[p-1])
                  Coefficient[Expand[cc^j],zz,p],{j,1,p}];
   target=(-1)^(p-1)/Factorial[p-1]
                  Coefficient[Normal[Series[Log[cc],{zz,0,p}]],zz,p];
   Expand[result-target],{p,1,8}];
 nn=dd^2-3dd+3; gram={{dd,1},{1,nn}};
 center={nn,-1}; primitive={-1,dd};
 <|"ChernInterpolationPolynomialErrors_p1to8"->errors,
   "SharpTwoCenterEnergyError"->Expand[17(a^2+b^2)-4(b/2-2a)^2-(a+4b)^2],
   "EquationDrivenOriginalCenterPeriodError"->Expand[primitive.gram.center+(dd-1)^3],
   "EquationDrivenCenterAmpleDegreeError"->Expand[{1,0}.gram.center-(dd-1)^3],
   "EquationDrivenCenterPlaneIntersection"->Expand[{0,1}.gram.center]|>
]
