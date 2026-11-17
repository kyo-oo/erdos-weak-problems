(* GST Cardinal Projective Stabilization exact deficit-polynomial checks.
   This checks symbolic combinatorics, NOT the geometry proof:
   theorem uses the projective bundle formula and Betti Kunneth.
   Defect_p(X) = dim Hdg_p(X) - rank cl_X^p. Exact theorem:
   Defect(X x (P1)^d;t)=(1+t)^d Defect(X;t).
   Infinite cardinal indices carry FINITE support only. *)
ClearAll[dd,defect,gstCases,oneDefect,gstAnswer];
defect[t_] := Sum[dd[j] t^j,{j,0,5}];
gstCases=Table[
 Module[{expanded=Expand[(1+t)^d defect[t]],tests},
   tests=Table[
      Expand[Coefficient[expanded,t,p]-
        Sum[If[0<=p-j<=5,Binomial[d,j] dd[p-j],0],{j,0,d}]]===0,
      {p,0,d+5}];
   <|"d"->d,"testedWeights"->Length[tests],
     "identityPassed"->And@@tests|>
 ],{d,0,8}];
oneDefect=Expand[t^2(1+t)^4];
gstAnswer=<|
 "testedDimensionParameters"->Length[gstCases],
 "allSymbolicBinomialDefectIdentities"->And@@(Lookup[#,"identityPassed"]&/@gstCases),
 "runs"->gstCases,
 "oneOriginalPrimitiveDefectPropagatedToFourNewFactors"->oneDefect,
 "explicitDeficitVector"->Table[Coefficient[oneDefect,t,p],{p,0,7}],
 "coefficientAtOriginalCodimensionSurvives"->(Coefficient[oneDefect,t,2]==1),
 "allPassed"->And@@(Lookup[#,"identityPassed"]&/@gstCases)
|>;
Print[gstAnswer];gstAnswer